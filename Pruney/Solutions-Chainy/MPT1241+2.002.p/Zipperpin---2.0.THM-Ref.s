%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gjp09Fx0o4

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 218 expanded)
%              Number of leaves         :   25 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  781 (2914 expanded)
%              Number of equality atoms :   51 ( 179 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t55_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( v3_pre_topc @ D @ B )
                     => ( ( k1_tops_1 @ B @ D )
                        = D ) )
                    & ( ( ( k1_tops_1 @ A @ C )
                        = C )
                     => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( v3_pre_topc @ D @ B )
                       => ( ( k1_tops_1 @ B @ D )
                          = D ) )
                      & ( ( ( k1_tops_1 @ A @ C )
                          = C )
                       => ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_tops_1])).

thf('0',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t30_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X16 )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X16 ) @ X15 ) @ X16 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t30_tops_1])).

thf('6',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('10',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['6','7','10'])).

thf('12',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['3','11'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v4_pre_topc @ X9 @ X10 )
      | ( ( k2_pre_topc @ X10 @ X9 )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
        = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X2 @ X3 )
        = ( k4_xboole_0 @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k1_tops_1 @ X12 @ X11 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ ( k2_pre_topc @ X12 @ ( k3_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 ) ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tops_1 @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ ( k2_pre_topc @ X1 @ ( k4_xboole_0 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','33'])).

thf('35',plain,
    ( ( ( ( k1_tops_1 @ sk_B @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
      | ~ ( l1_pre_topc @ sk_B ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['20','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_subset_1 @ X5 @ ( k3_subset_1 @ X5 @ X4 ) )
        = X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('43',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('44',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['35','41','42','43','44'])).

thf('46',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
   <= ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D ) ),
    inference(split,[status(esa)],['46'])).

thf('48',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('49',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D ) ),
    inference(split,[status(esa)],['49'])).

thf('51',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(split,[status(esa)],['49'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X13 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('54',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup+',[status(thm)],['51','57'])).

thf('59',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['46'])).

thf('60',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
     != sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ( k1_tops_1 @ sk_B @ sk_D )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['48','50','60'])).

thf('62',plain,(
    ( k1_tops_1 @ sk_B @ sk_D )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['47','61'])).

thf('63',plain,(
    ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['45','62'])).

thf('64',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','63','64','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gjp09Fx0o4
% 0.15/0.35  % Computer   : n006.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:27:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 83 iterations in 0.035s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.50  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(t55_tops_1, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( l1_pre_topc @ B ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.50                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.22/0.50                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.22/0.50                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.22/0.50                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( l1_pre_topc @ B ) =>
% 0.22/0.50              ( ![C:$i]:
% 0.22/0.50                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                  ( ![D:$i]:
% 0.22/0.50                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.50                      ( ( ( v3_pre_topc @ D @ B ) =>
% 0.22/0.50                          ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.22/0.50                        ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.22/0.50                          ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t55_tops_1])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (((v3_pre_topc @ sk_D @ sk_B) | ((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) | ((v3_pre_topc @ sk_D @ sk_B))),
% 0.22/0.50      inference('split', [status(esa)], ['0'])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (((v3_pre_topc @ sk_D @ sk_B) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t30_tops_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( v3_pre_topc @ B @ A ) <=>
% 0.22/0.50             ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X15 : $i, X16 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.50          | ~ (v3_pre_topc @ X15 @ X16)
% 0.22/0.50          | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X16) @ X15) @ X16)
% 0.22/0.50          | ~ (l1_pre_topc @ X16))),
% 0.22/0.50      inference('cnf', [status(esa)], [t30_tops_1])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.50        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B)
% 0.22/0.50        | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.50  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d5_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.22/0.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B)
% 0.22/0.50        | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['6', '7', '10'])).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (((v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))
% 0.22/0.50         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '11'])).
% 0.22/0.50  thf(t36_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 0.22/0.50      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.50  thf(t3_subset, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X6 : $i, X8 : $i]:
% 0.22/0.50         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf(t52_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.50             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.50               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.22/0.50          | ~ (v4_pre_topc @ X9 @ X10)
% 0.22/0.50          | ((k2_pre_topc @ X10 @ X9) = (X9))
% 0.22/0.50          | ~ (l1_pre_topc @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X0)
% 0.22/0.50          | ((k2_pre_topc @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.50              = (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.50          | ~ (v4_pre_topc @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.22/0.50           = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.22/0.50         | ~ (l1_pre_topc @ sk_B))) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['12', '17'])).
% 0.22/0.50  thf('19', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      ((((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.22/0.50          = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.22/0.50         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.50       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.22/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.22/0.50           = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X2 : $i, X3 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X2 @ X3) = (k4_xboole_0 @ X2 @ X3))
% 0.22/0.50          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.50      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.50           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.50           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))
% 0.22/0.50           = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.50      inference('demod', [status(thm)], ['23', '26', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf(d1_tops_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ( k1_tops_1 @ A @ B ) =
% 0.22/0.50             ( k3_subset_1 @
% 0.22/0.50               ( u1_struct_0 @ A ) @ 
% 0.22/0.50               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.22/0.50          | ((k1_tops_1 @ X12 @ X11)
% 0.22/0.50              = (k3_subset_1 @ (u1_struct_0 @ X12) @ 
% 0.22/0.50                 (k2_pre_topc @ X12 @ (k3_subset_1 @ (u1_struct_0 @ X12) @ X11))))
% 0.22/0.50          | ~ (l1_pre_topc @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X0)
% 0.22/0.50          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.50              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50                 (k2_pre_topc @ X0 @ 
% 0.22/0.50                  (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.50           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X0)
% 0.22/0.50          | ((k1_tops_1 @ X0 @ (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))
% 0.22/0.50              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50                 (k2_pre_topc @ X0 @ 
% 0.22/0.50                  (k4_xboole_0 @ (u1_struct_0 @ X0) @ 
% 0.22/0.50                   (k4_xboole_0 @ (u1_struct_0 @ X0) @ X1))))))),
% 0.22/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (((k1_tops_1 @ X1 @ 
% 0.22/0.50            (k4_xboole_0 @ (u1_struct_0 @ X1) @ 
% 0.22/0.50             (k4_xboole_0 @ (u1_struct_0 @ X1) @ X0)))
% 0.22/0.50            = (k3_subset_1 @ (u1_struct_0 @ X1) @ 
% 0.22/0.50               (k2_pre_topc @ X1 @ (k4_xboole_0 @ (u1_struct_0 @ X1) @ X0))))
% 0.22/0.50          | ~ (l1_pre_topc @ X1))),
% 0.22/0.50      inference('sup+', [status(thm)], ['28', '33'])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (((((k1_tops_1 @ sk_B @ 
% 0.22/0.50           (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.50            (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.22/0.50           = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.50              (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.22/0.50         | ~ (l1_pre_topc @ sk_B))) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['20', '34'])).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (((k3_subset_1 @ X5 @ (k3_subset_1 @ X5 @ X4)) = (X4))
% 0.22/0.50          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.50  thf('38', plain,
% 0.22/0.50      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.50         (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.22/0.50         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.50           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.50         (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.22/0.50           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.50  thf('43', plain,
% 0.22/0.50      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.50         (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.22/0.50      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.22/0.50  thf('44', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.22/0.50         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['35', '41', '42', '43', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D)) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D)))
% 0.22/0.50         <= (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))))),
% 0.22/0.50      inference('split', [status(esa)], ['46'])).
% 0.22/0.50  thf('48', plain,
% 0.22/0.50      (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))) | 
% 0.22/0.50       ~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.50      inference('split', [status(esa)], ['46'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D))
% 0.22/0.50        | ((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) | 
% 0.22/0.50       ~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))),
% 0.22/0.50      inference('split', [status(esa)], ['49'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.22/0.50         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.22/0.50      inference('split', [status(esa)], ['49'])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(fc9_tops_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.22/0.50  thf('53', plain,
% 0.22/0.50      (![X13 : $i, X14 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X13)
% 0.22/0.50          | ~ (v2_pre_topc @ X13)
% 0.22/0.50          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.50          | (v3_pre_topc @ (k1_tops_1 @ X13 @ X14) @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.22/0.50  thf('54', plain,
% 0.22/0.50      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.22/0.50        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.50  thf('55', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('57', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      (((v3_pre_topc @ sk_C @ sk_A))
% 0.22/0.50         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.22/0.50      inference('sup+', [status(thm)], ['51', '57'])).
% 0.22/0.50  thf('59', plain,
% 0.22/0.50      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.22/0.50      inference('split', [status(esa)], ['46'])).
% 0.22/0.50  thf('60', plain,
% 0.22/0.50      (((v3_pre_topc @ sk_C @ sk_A)) | ~ (((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['58', '59'])).
% 0.22/0.50  thf('61', plain, (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['48', '50', '60'])).
% 0.22/0.50  thf('62', plain, (((k1_tops_1 @ sk_B @ sk_D) != (sk_D))),
% 0.22/0.50      inference('simpl_trail', [status(thm)], ['47', '61'])).
% 0.22/0.50  thf('63', plain, (~ ((v3_pre_topc @ sk_D @ sk_B))),
% 0.22/0.50      inference('simplify_reflect-', [status(thm)], ['45', '62'])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      (~ ((v3_pre_topc @ sk_C @ sk_A)) | ((v3_pre_topc @ sk_D @ sk_B))),
% 0.22/0.50      inference('split', [status(esa)], ['2'])).
% 0.22/0.50  thf('65', plain, ($false),
% 0.22/0.50      inference('sat_resolution*', [status(thm)], ['1', '63', '64', '60'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
