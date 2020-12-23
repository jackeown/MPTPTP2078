%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sgi4d0Jvb7

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:20 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 164 expanded)
%              Number of leaves         :   32 (  61 expanded)
%              Depth                    :   27
%              Number of atoms          : 1224 (2278 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('4',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ( m1_subset_1 @ ( sk_E @ X13 @ X14 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_waybel_0 @ X12 @ X11 @ X14 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( ( k2_waybel_0 @ X18 @ X17 @ X19 )
        = ( k3_funct_2 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) @ ( u1_waybel_0 @ X18 @ X17 ) @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d8_waybel_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ X1 ) @ ( u1_waybel_0 @ X1 @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['4','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('20',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X23 @ X22 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('22',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

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

thf('25',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_funct_2 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X5 ) ) )
      | ( r2_hidden @ ( k3_funct_2 @ X7 @ X5 @ X6 @ X8 ) @ ( k2_relset_1 @ X7 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t189_funct_2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X23 @ X22 )
      | ( v1_funct_2 @ ( u1_waybel_0 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) @ ( u1_struct_0 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('29',plain,
    ( ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_struct_0 @ X22 )
      | ~ ( l1_waybel_0 @ X23 @ X22 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('34',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['26','31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['18','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X12 @ X11 @ ( sk_E @ X13 @ X14 @ X11 @ X12 ) ) @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_waybel_0 @ X12 @ X11 @ X14 )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','47'])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('52',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','64'])).

thf('66',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('67',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_waybel_0 @ X20 @ X21 )
      | ( l1_orders_2 @ X20 )
      | ~ ( l1_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('68',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['65','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.sgi4d0Jvb7
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 55 iterations in 0.042s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.19/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.49  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.49  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(dt_l1_orders_2, axiom,
% 0.19/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.19/0.49  thf('0', plain, (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.19/0.49  thf(d1_xboole_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.49  thf(t1_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf(t8_waybel_9, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49           ( r1_waybel_0 @
% 0.19/0.49             A @ B @ 
% 0.19/0.49             ( k2_relset_1 @
% 0.19/0.49               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.49               ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49              ( r1_waybel_0 @
% 0.19/0.49                A @ B @ 
% 0.19/0.49                ( k2_relset_1 @
% 0.19/0.49                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.49                  ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t8_waybel_9])).
% 0.19/0.49  thf('4', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('5', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf(d11_waybel_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.19/0.49               ( ?[D:$i]:
% 0.19/0.49                 ( ( ![E:$i]:
% 0.19/0.49                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.49                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.19/0.49                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.19/0.49                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X11)
% 0.19/0.49          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.19/0.49          | (m1_subset_1 @ (sk_E @ X13 @ X14 @ X11 @ X12) @ (u1_struct_0 @ X11))
% 0.19/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.19/0.49          | (r1_waybel_0 @ X12 @ X11 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X12)
% 0.19/0.49          | (v2_struct_0 @ X12))),
% 0.19/0.49      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.19/0.49          | (v2_struct_0 @ X1)
% 0.19/0.49          | ~ (l1_struct_0 @ X1)
% 0.19/0.49          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.19/0.49          | (m1_subset_1 @ 
% 0.19/0.49             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.19/0.49             (u1_struct_0 @ X0))
% 0.19/0.49          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.19/0.49          | (v2_struct_0 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (m1_subset_1 @ 
% 0.19/0.49             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.19/0.49             (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '8'])).
% 0.19/0.49  thf('10', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (m1_subset_1 @ 
% 0.19/0.49             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.19/0.49             (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf(d8_waybel_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.49               ( ( k2_waybel_0 @ A @ B @ C ) =
% 0.19/0.49                 ( k3_funct_2 @
% 0.19/0.49                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.19/0.49                   ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X17)
% 0.19/0.49          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.19/0.49          | ((k2_waybel_0 @ X18 @ X17 @ X19)
% 0.19/0.49              = (k3_funct_2 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18) @ 
% 0.19/0.49                 (u1_waybel_0 @ X18 @ X17) @ X19))
% 0.19/0.49          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.19/0.49          | ~ (l1_struct_0 @ X18)
% 0.19/0.49          | (v2_struct_0 @ X18))),
% 0.19/0.49      inference('cnf', [status(esa)], [d8_waybel_0])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (v2_struct_0 @ X1)
% 0.19/0.49          | ~ (l1_struct_0 @ X1)
% 0.19/0.49          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.19/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.19/0.49              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X1) @ 
% 0.19/0.49                 (u1_waybel_0 @ X1 @ sk_B_1) @ 
% 0.19/0.49                 (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)))
% 0.19/0.49          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.19/0.49          | (v2_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.19/0.49          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.19/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.19/0.49              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X1) @ 
% 0.19/0.49                 (u1_waybel_0 @ X1 @ sk_B_1) @ 
% 0.19/0.49                 (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)))
% 0.19/0.49          | ~ (l1_struct_0 @ X1)
% 0.19/0.49          | (v2_struct_0 @ X1)
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (l1_struct_0 @ sk_A)
% 0.19/0.49          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.19/0.49              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49                 (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.19/0.49                 (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '14'])).
% 0.19/0.49  thf('16', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.19/0.49              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49                 (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.19/0.49                 (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.19/0.49            = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49               (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.19/0.49               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)))
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (m1_subset_1 @ 
% 0.19/0.49             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.19/0.49             (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('demod', [status(thm)], ['9', '10'])).
% 0.19/0.49  thf('20', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_u1_waybel_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.19/0.49       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.19/0.49         ( v1_funct_2 @
% 0.19/0.49           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.49         ( m1_subset_1 @
% 0.19/0.49           ( u1_waybel_0 @ A @ B ) @ 
% 0.19/0.49           ( k1_zfmisc_1 @
% 0.19/0.49             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X22 : $i, X23 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X22)
% 0.19/0.49          | ~ (l1_waybel_0 @ X23 @ X22)
% 0.19/0.49          | (m1_subset_1 @ (u1_waybel_0 @ X22 @ X23) @ 
% 0.19/0.49             (k1_zfmisc_1 @ 
% 0.19/0.49              (k2_zfmisc_1 @ (u1_struct_0 @ X23) @ (u1_struct_0 @ X22)))))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.19/0.49         (k1_zfmisc_1 @ 
% 0.19/0.49          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf(t189_funct_2, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_subset_1 @ C @ A ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.49                     ( m1_subset_1 @
% 0.19/0.49                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.49                   ( r2_hidden @
% 0.19/0.49                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.19/0.49                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ X5)
% 0.19/0.49          | ~ (v1_funct_1 @ X6)
% 0.19/0.49          | ~ (v1_funct_2 @ X6 @ X7 @ X5)
% 0.19/0.49          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X5)))
% 0.19/0.49          | (r2_hidden @ (k3_funct_2 @ X7 @ X5 @ X6 @ X8) @ 
% 0.19/0.49             (k2_relset_1 @ X7 @ X5 @ X6))
% 0.19/0.49          | ~ (m1_subset_1 @ X8 @ X7)
% 0.19/0.49          | (v1_xboole_0 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [t189_funct_2])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (r2_hidden @ 
% 0.19/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (u1_waybel_0 @ sk_A @ sk_B_1) @ X0) @ 
% 0.19/0.49             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49          | ~ (v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.19/0.49               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1))
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X22 : $i, X23 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X22)
% 0.19/0.49          | ~ (l1_waybel_0 @ X23 @ X22)
% 0.19/0.49          | (v1_funct_2 @ (u1_waybel_0 @ X22 @ X23) @ (u1_struct_0 @ X23) @ 
% 0.19/0.49             (u1_struct_0 @ X22)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.19/0.49         (u1_struct_0 @ sk_A))
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.49  thf('30', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      ((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.19/0.49        (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.49  thf('32', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      (![X22 : $i, X23 : $i]:
% 0.19/0.49         (~ (l1_struct_0 @ X22)
% 0.19/0.49          | ~ (l1_waybel_0 @ X23 @ X22)
% 0.19/0.49          | (v1_funct_1 @ (u1_waybel_0 @ X22 @ X23)))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1)) | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('35', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('36', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (r2_hidden @ 
% 0.19/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (u1_waybel_0 @ sk_A @ sk_B_1) @ X0) @ 
% 0.19/0.49             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('demod', [status(thm)], ['26', '31', '36'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (r2_hidden @ 
% 0.19/0.49             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.19/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.19/0.49             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['19', '37'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r2_hidden @ 
% 0.19/0.49           (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.19/0.49            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r2_hidden @ 
% 0.19/0.49           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['18', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | (v2_struct_0 @ sk_B_1)
% 0.19/0.49          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_A)
% 0.19/0.49          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49          | (r2_hidden @ 
% 0.19/0.49             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.19/0.49             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49              (u1_waybel_0 @ sk_A @ sk_B_1))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['40'])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X11)
% 0.19/0.49          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.19/0.49          | ~ (r2_hidden @ 
% 0.19/0.49               (k2_waybel_0 @ X12 @ X11 @ (sk_E @ X13 @ X14 @ X11 @ X12)) @ X14)
% 0.19/0.49          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.19/0.49          | (r1_waybel_0 @ X12 @ X11 @ X14)
% 0.19/0.49          | ~ (l1_struct_0 @ X12)
% 0.19/0.49          | (v2_struct_0 @ X12))),
% 0.19/0.49      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49        | (v2_struct_0 @ sk_B_1)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A)
% 0.19/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.19/0.49             (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.49  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('45', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49        | (v2_struct_0 @ sk_B_1)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49        | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.19/0.49             (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.19/0.49  thf('47', plain,
% 0.19/0.49      ((~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.19/0.49           (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | (v2_struct_0 @ sk_B_1)
% 0.19/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49        | (v2_struct_0 @ sk_B_1)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['3', '47'])).
% 0.19/0.49  thf('49', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.49        | (v2_struct_0 @ sk_B_1)
% 0.19/0.49        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['48'])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.19/0.49          (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49           (u1_waybel_0 @ sk_A @ sk_B_1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_B_1)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.19/0.49  thf(fc2_struct_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.49       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      (![X9 : $i]:
% 0.19/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.19/0.49          | ~ (l1_struct_0 @ X9)
% 0.19/0.49          | (v2_struct_0 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B_1)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['51', '52'])).
% 0.19/0.49  thf('54', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('55', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B_1)
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['53', '54'])).
% 0.19/0.49  thf('56', plain,
% 0.19/0.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.19/0.49        | (v2_struct_0 @ sk_A)
% 0.19/0.49        | (v2_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('simplify', [status(thm)], ['55'])).
% 0.19/0.49  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.19/0.49      inference('clc', [status(thm)], ['56', '57'])).
% 0.19/0.49  thf('59', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('60', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('clc', [status(thm)], ['58', '59'])).
% 0.19/0.49  thf('61', plain,
% 0.19/0.49      (![X9 : $i]:
% 0.19/0.49         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.19/0.49          | ~ (l1_struct_0 @ X9)
% 0.19/0.49          | (v2_struct_0 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.49  thf('62', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['60', '61'])).
% 0.19/0.49  thf('63', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('64', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.19/0.49      inference('clc', [status(thm)], ['62', '63'])).
% 0.19/0.49  thf('65', plain, (~ (l1_orders_2 @ sk_B_1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['0', '64'])).
% 0.19/0.49  thf('66', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_l1_waybel_0, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_struct_0 @ A ) =>
% 0.19/0.49       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.19/0.49  thf('67', plain,
% 0.19/0.49      (![X20 : $i, X21 : $i]:
% 0.19/0.49         (~ (l1_waybel_0 @ X20 @ X21)
% 0.19/0.49          | (l1_orders_2 @ X20)
% 0.19/0.49          | ~ (l1_struct_0 @ X21))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.19/0.49  thf('68', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['66', '67'])).
% 0.19/0.49  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('70', plain, ((l1_orders_2 @ sk_B_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['68', '69'])).
% 0.19/0.49  thf('71', plain, ($false), inference('demod', [status(thm)], ['65', '70'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
