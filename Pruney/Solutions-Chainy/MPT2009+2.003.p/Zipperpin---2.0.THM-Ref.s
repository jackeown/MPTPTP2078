%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b3SQVysTWp

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 173 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   28
%              Number of atoms          : 1246 (2359 expanded)
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

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
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

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

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

thf('6',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

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

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ( m1_subset_1 @ ( sk_E @ X14 @ X15 @ X12 @ X13 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r1_waybel_0 @ X13 @ X12 @ X15 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r1_waybel_0 @ X1 @ X0 @ X2 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( l1_waybel_0 @ X18 @ X19 )
      | ( ( k2_waybel_0 @ X19 @ X18 @ X20 )
        = ( k3_funct_2 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X19 ) @ ( u1_waybel_0 @ X19 @ X18 ) @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_struct_0 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d8_waybel_0])).

thf('15',plain,(
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
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
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
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v2_struct_0 @ sk_A )
      | ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('22',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_struct_0 @ A )
        & ( l1_waybel_0 @ B @ A ) )
     => ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) )
        & ( v1_funct_2 @ ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ ( u1_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X24 @ X23 )
      | ( m1_subset_1 @ ( u1_waybel_0 @ X23 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('24',plain,
    ( ( m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

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

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X6 ) ) )
      | ( r2_hidden @ ( k3_funct_2 @ X8 @ X6 @ X7 @ X9 ) @ ( k2_relset_1 @ X8 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t189_funct_2])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X24 @ X23 )
      | ( v1_funct_2 @ ( u1_waybel_0 @ X23 @ X24 ) @ ( u1_struct_0 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('31',plain,
    ( ( v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l1_struct_0 @ X23 )
      | ~ ( l1_waybel_0 @ X24 @ X23 )
      | ( v1_funct_1 @ ( u1_waybel_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_u1_waybel_0])).

thf('36',plain,
    ( ( v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_1 @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ X0 ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['28','33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
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
    inference('sup+',[status(thm)],['20','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_B_1 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) ) @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( l1_waybel_0 @ X12 @ X13 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ X13 @ X12 @ ( sk_E @ X14 @ X15 @ X12 @ X13 ) ) @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r1_waybel_0 @ X13 @ X12 @ X15 )
      | ~ ( l1_struct_0 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('45',plain,
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
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k2_relset_1 @ ( u1_struct_0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) @ ( u1_waybel_0 @ sk_A @ sk_B_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('54',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ~ ( l1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','66'])).

thf('68',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('69',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l1_waybel_0 @ X21 @ X22 )
      | ( l1_orders_2 @ X21 )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('70',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['67','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.b3SQVysTWp
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 75 iterations in 0.050s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.21/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.50  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(dt_l1_orders_2, axiom,
% 0.21/0.50    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.21/0.50  thf('0', plain, (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_orders_2 @ X11))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.21/0.50  thf(d1_xboole_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf(d2_subset_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.50       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.50          | (m1_subset_1 @ X3 @ X4)
% 0.21/0.50          | (v1_xboole_0 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.21/0.50      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf(t8_waybel_9, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( r1_waybel_0 @
% 0.21/0.50             A @ B @ 
% 0.21/0.50             ( k2_relset_1 @
% 0.21/0.50               ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.50               ( u1_waybel_0 @ A @ B ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50              ( r1_waybel_0 @
% 0.21/0.50                A @ B @ 
% 0.21/0.50                ( k2_relset_1 @
% 0.21/0.50                  ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.50                  ( u1_waybel_0 @ A @ B ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t8_waybel_9])).
% 0.21/0.50  thf('6', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]: ((v1_xboole_0 @ X0) | (m1_subset_1 @ (sk_B @ X0) @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.50  thf(d11_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.21/0.50               ( ?[D:$i]:
% 0.21/0.50                 ( ( ![E:$i]:
% 0.21/0.50                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.21/0.50                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.21/0.50                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X12)
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | (m1_subset_1 @ (sk_E @ X14 @ X15 @ X12 @ X13) @ (u1_struct_0 @ X12))
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.21/0.50          | (r1_waybel_0 @ X13 @ X12 @ X15)
% 0.21/0.50          | ~ (l1_struct_0 @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (l1_struct_0 @ X1)
% 0.21/0.50          | (r1_waybel_0 @ X1 @ X0 @ X2)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.21/0.50             (u1_struct_0 @ X0))
% 0.21/0.50          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.21/0.50  thf('12', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf(d8_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50               ( ( k2_waybel_0 @ A @ B @ C ) =
% 0.21/0.50                 ( k3_funct_2 @
% 0.21/0.50                   ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.21/0.50                   ( u1_waybel_0 @ A @ B ) @ C ) ) ) ) ) ) ))).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X18)
% 0.21/0.50          | ~ (l1_waybel_0 @ X18 @ X19)
% 0.21/0.50          | ((k2_waybel_0 @ X19 @ X18 @ X20)
% 0.21/0.50              = (k3_funct_2 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X19) @ 
% 0.21/0.50                 (u1_waybel_0 @ X19 @ X18) @ X20))
% 0.21/0.50          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.21/0.50          | ~ (l1_struct_0 @ X19)
% 0.21/0.50          | (v2_struct_0 @ X19))),
% 0.21/0.50      inference('cnf', [status(esa)], [d8_waybel_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | ~ (l1_struct_0 @ X1)
% 0.21/0.50          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.21/0.50              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X1) @ 
% 0.21/0.50                 (u1_waybel_0 @ X1 @ sk_B_1) @ 
% 0.21/0.50                 (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)))
% 0.21/0.50          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.21/0.50          | ((k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.21/0.50              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ X1) @ 
% 0.21/0.50                 (u1_waybel_0 @ X1 @ sk_B_1) @ 
% 0.21/0.50                 (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)))
% 0.21/0.50          | ~ (l1_struct_0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ X1)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.21/0.50              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50                 (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.21/0.50                 (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '16'])).
% 0.21/0.50  thf('18', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | ((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.21/0.50              = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50                 (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.21/0.50                 (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A))
% 0.21/0.50            = (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50               (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.21/0.50               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)))
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (m1_subset_1 @ 
% 0.21/0.50             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.50  thf('22', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_u1_waybel_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( l1_struct_0 @ A ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.21/0.50       ( ( v1_funct_1 @ ( u1_waybel_0 @ A @ B ) ) & 
% 0.21/0.50         ( v1_funct_2 @
% 0.21/0.50           ( u1_waybel_0 @ A @ B ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.50         ( m1_subset_1 @
% 0.21/0.50           ( u1_waybel_0 @ A @ B ) @ 
% 0.21/0.50           ( k1_zfmisc_1 @
% 0.21/0.50             ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X23)
% 0.21/0.50          | ~ (l1_waybel_0 @ X24 @ X23)
% 0.21/0.50          | (m1_subset_1 @ (u1_waybel_0 @ X23 @ X24) @ 
% 0.21/0.50             (k1_zfmisc_1 @ 
% 0.21/0.50              (k2_zfmisc_1 @ (u1_struct_0 @ X24) @ (u1_struct_0 @ X23)))))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.21/0.50         (k1_zfmisc_1 @ 
% 0.21/0.50          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((m1_subset_1 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.21/0.50        (k1_zfmisc_1 @ 
% 0.21/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.50      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.50  thf(t189_funct_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.50               ( ![D:$i]:
% 0.21/0.50                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.50                     ( m1_subset_1 @
% 0.21/0.50                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50                   ( r2_hidden @
% 0.21/0.50                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.21/0.50                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ X6)
% 0.21/0.50          | ~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_funct_2 @ X7 @ X8 @ X6)
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X6)))
% 0.21/0.50          | (r2_hidden @ (k3_funct_2 @ X8 @ X6 @ X7 @ X9) @ 
% 0.21/0.50             (k2_relset_1 @ X8 @ X6 @ X7))
% 0.21/0.50          | ~ (m1_subset_1 @ X9 @ X8)
% 0.21/0.50          | (v1_xboole_0 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [t189_funct_2])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50              (u1_waybel_0 @ sk_A @ sk_B_1) @ X0) @ 
% 0.21/0.50             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50          | ~ (v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.21/0.50               (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | ~ (v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1))
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.50  thf('29', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X23)
% 0.21/0.50          | ~ (l1_waybel_0 @ X24 @ X23)
% 0.21/0.50          | (v1_funct_2 @ (u1_waybel_0 @ X23 @ X24) @ (u1_struct_0 @ X24) @ 
% 0.21/0.50             (u1_struct_0 @ X23)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.50         (u1_struct_0 @ sk_A))
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((v1_funct_2 @ (u1_waybel_0 @ sk_A @ sk_B_1) @ (u1_struct_0 @ sk_B_1) @ 
% 0.21/0.50        (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.50  thf('34', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X23 : $i, X24 : $i]:
% 0.21/0.50         (~ (l1_struct_0 @ X23)
% 0.21/0.50          | ~ (l1_waybel_0 @ X24 @ X23)
% 0.21/0.50          | (v1_funct_1 @ (u1_waybel_0 @ X23 @ X24)))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_waybel_0])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1)) | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('38', plain, ((v1_funct_1 @ (u1_waybel_0 @ sk_A @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['36', '37'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50              (u1_waybel_0 @ sk_A @ sk_B_1) @ X0) @ 
% 0.21/0.50             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['28', '33', '38'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50              (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.50             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50              (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ 
% 0.21/0.50           (k3_funct_2 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1) @ 
% 0.21/0.50            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r2_hidden @ 
% 0.21/0.50           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup+', [status(thm)], ['20', '41'])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (v2_struct_0 @ sk_B_1)
% 0.21/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.21/0.50          | (v2_struct_0 @ sk_A)
% 0.21/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50          | (r2_hidden @ 
% 0.21/0.50             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50              (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A)) @ 
% 0.21/0.50             (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50              (u1_waybel_0 @ sk_A @ sk_B_1))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.50         ((v2_struct_0 @ X12)
% 0.21/0.50          | ~ (l1_waybel_0 @ X12 @ X13)
% 0.21/0.50          | ~ (r2_hidden @ 
% 0.21/0.50               (k2_waybel_0 @ X13 @ X12 @ (sk_E @ X14 @ X15 @ X12 @ X13)) @ X15)
% 0.21/0.50          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.21/0.50          | (r1_waybel_0 @ X13 @ X12 @ X15)
% 0.21/0.50          | ~ (l1_struct_0 @ X13)
% 0.21/0.50          | (v2_struct_0 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50        | (v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.50  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('47', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50        | (v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50        | ~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.21/0.50             (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      ((~ (m1_subset_1 @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ 
% 0.21/0.50           (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50        | (v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '49'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50        | (v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50           (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50            (u1_waybel_0 @ sk_A @ sk_B_1)))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.21/0.50          (k2_relset_1 @ (u1_struct_0 @ sk_B_1) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.50           (u1_waybel_0 @ sk_A @ sk_B_1)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf(fc2_struct_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.21/0.50       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X10 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.21/0.50          | ~ (l1_struct_0 @ X10)
% 0.21/0.50          | (v2_struct_0 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | ~ (l1_struct_0 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_1)
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v2_struct_0 @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))
% 0.21/0.50        | (v2_struct_0 @ sk_A)
% 0.21/0.50        | (v2_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('simplify', [status(thm)], ['57'])).
% 0.21/0.50  thf('59', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (((v2_struct_0 @ sk_B_1) | (v1_xboole_0 @ (u1_struct_0 @ sk_B_1)))),
% 0.21/0.50      inference('clc', [status(thm)], ['58', '59'])).
% 0.21/0.50  thf('61', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('62', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (![X10 : $i]:
% 0.21/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 0.21/0.50          | ~ (l1_struct_0 @ X10)
% 0.21/0.50          | (v2_struct_0 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.21/0.50  thf('64', plain, (((v2_struct_0 @ sk_B_1) | ~ (l1_struct_0 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain, (~ (l1_struct_0 @ sk_B_1)),
% 0.21/0.50      inference('clc', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain, (~ (l1_orders_2 @ sk_B_1)),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '66'])).
% 0.21/0.50  thf('68', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_l1_waybel_0, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_struct_0 @ A ) =>
% 0.21/0.50       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (![X21 : $i, X22 : $i]:
% 0.21/0.50         (~ (l1_waybel_0 @ X21 @ X22)
% 0.21/0.50          | (l1_orders_2 @ X21)
% 0.21/0.50          | ~ (l1_struct_0 @ X22))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.21/0.50  thf('70', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('72', plain, ((l1_orders_2 @ sk_B_1)),
% 0.21/0.50      inference('demod', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain, ($false), inference('demod', [status(thm)], ['67', '72'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
