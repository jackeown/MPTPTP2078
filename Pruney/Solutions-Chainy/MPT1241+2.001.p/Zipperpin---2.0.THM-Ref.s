%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OWAJxXtUXO

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:08 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 326 expanded)
%              Number of leaves         :   32 ( 107 expanded)
%              Depth                    :   18
%              Number of atoms          : 1003 (4487 expanded)
%              Number of equality atoms :   67 ( 286 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('11',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('12',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['6','15','16'])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('29',plain,
    ( ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['21','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('31',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X1 @ X2 )
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['6','15','16'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
      = sk_D )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('38',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d6_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( v3_pre_topc @ ( k7_subset_1 @ ( u1_struct_0 @ X13 ) @ ( k2_struct_0 @ X13 ) @ X12 ) @ X13 )
      | ( v4_pre_topc @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[d6_pre_topc])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k7_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X3 ) @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('44',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( ( k7_subset_1 @ X9 @ X8 @ X10 )
        = ( k4_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k7_subset_1 @ X0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ X0 ) @ X1 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['38','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('50',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('52',plain,
    ( ~ ( v3_pre_topc @ sk_D @ sk_B )
    | ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf('53',plain,
    ( ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['19','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

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

thf('55',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v4_pre_topc @ X15 @ X16 )
      | ( ( k2_pre_topc @ X16 @ X15 )
        = X15 )
      | ~ ( l1_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('56',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
      = ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('61',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k1_tops_1 @ X18 @ X17 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ ( k2_pre_topc @ X18 @ ( k3_subset_1 @ ( u1_struct_0 @ X18 ) @ X17 ) ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('62',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('65',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('66',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('68',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('70',plain,
    ( ( k3_subset_1 @ ( k2_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ),
    inference('sup+',[status(thm)],['65','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D )
    = ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) ),
    inference(demod,[status(thm)],['64','71'])).

thf('73',plain,
    ( ( k1_tops_1 @ sk_B @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['62','63','72'])).

thf('74',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_B ) @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['59','73'])).

thf('75',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['17','74'])).

thf('76',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
   <= ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D ) ),
    inference(split,[status(esa)],['76'])).

thf('78',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('79',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
    | ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(split,[status(esa)],['79'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ) )).

thf('83',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v3_pre_topc @ ( k1_tops_1 @ X19 @ X20 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc9_tops_1])).

thf('84',plain,
    ( ( v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v3_pre_topc @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup+',[status(thm)],['81','87'])).

thf('89',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['76'])).

thf('90',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
     != sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ( k1_tops_1 @ sk_B @ sk_D )
 != sk_D ),
    inference('sat_resolution*',[status(thm)],['78','80','90'])).

thf('92',plain,(
    ( k1_tops_1 @ sk_B @ sk_D )
 != sk_D ),
    inference(simpl_trail,[status(thm)],['77','91'])).

thf('93',plain,(
    ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['75','92'])).

thf('94',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
    | ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','93','94','90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OWAJxXtUXO
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:39:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 192 iterations in 0.086s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.55  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.55  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.22/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.55  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.22/0.55  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.22/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.55  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.55  thf(t55_tops_1, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( l1_pre_topc @ B ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.55                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.22/0.55                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.22/0.55                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.22/0.55                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( l1_pre_topc @ B ) =>
% 0.22/0.55              ( ![C:$i]:
% 0.22/0.55                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55                  ( ![D:$i]:
% 0.22/0.55                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.22/0.55                      ( ( ( v3_pre_topc @ D @ B ) =>
% 0.22/0.55                          ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.22/0.55                        ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.22/0.55                          ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t55_tops_1])).
% 0.22/0.55  thf('0', plain,
% 0.22/0.55      (((v3_pre_topc @ sk_D @ sk_B) | ((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) | ((v3_pre_topc @ sk_D @ sk_B))),
% 0.22/0.55      inference('split', [status(esa)], ['0'])).
% 0.22/0.55  thf(d3_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.55  thf('2', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X6 : $i, X7 : $i]:
% 0.22/0.55         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.22/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.22/0.55      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55         (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      ((((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55          (k3_subset_1 @ (k2_struct_0 @ sk_B) @ sk_D)) = (sk_D))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['2', '5'])).
% 0.22/0.55  thf('7', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('8', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('9', plain,
% 0.22/0.55      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.55  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_l1_pre_topc, axiom,
% 0.22/0.55    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_pre_topc @ X14))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.55  thf('12', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_struct_0 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.55  thf(d5_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i]:
% 0.22/0.55         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.55  thf('16', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('17', plain,
% 0.22/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55         (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['6', '15', '16'])).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (((v3_pre_topc @ sk_D @ sk_B) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('19', plain,
% 0.22/0.55      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.55      inference('split', [status(esa)], ['18'])).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('21', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_k3_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      (![X4 : $i, X5 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k3_subset_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.22/0.55          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X4)))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i]:
% 0.22/0.55         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['24', '27'])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ 
% 0.22/0.55         (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['21', '28'])).
% 0.22/0.55  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      (![X1 : $i, X2 : $i]:
% 0.22/0.55         (((k3_subset_1 @ X1 @ X2) = (k4_xboole_0 @ X1 @ X2))
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.22/0.55  thf('33', plain,
% 0.22/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55         (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))
% 0.22/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55            (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.55  thf('34', plain,
% 0.22/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55         (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['6', '15', '16'])).
% 0.22/0.55  thf('35', plain,
% 0.22/0.55      (((k4_xboole_0 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55         (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.22/0.55      inference('sup+', [status(thm)], ['33', '34'])).
% 0.22/0.55  thf('36', plain,
% 0.22/0.55      ((((k4_xboole_0 @ (k2_struct_0 @ sk_B) @ 
% 0.22/0.55          (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D)) = (sk_D))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['20', '35'])).
% 0.22/0.55  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (((k4_xboole_0 @ (k2_struct_0 @ sk_B) @ 
% 0.22/0.55         (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.55  thf('39', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf(d6_pre_topc, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( v4_pre_topc @ B @ A ) <=>
% 0.22/0.55             ( v3_pre_topc @
% 0.22/0.55               ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_struct_0 @ A ) @ B ) @ 
% 0.22/0.55               A ) ) ) ) ))).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      (![X12 : $i, X13 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.22/0.55          | ~ (v3_pre_topc @ 
% 0.22/0.55               (k7_subset_1 @ (u1_struct_0 @ X13) @ (k2_struct_0 @ X13) @ X12) @ 
% 0.22/0.55               X13)
% 0.22/0.55          | (v4_pre_topc @ X12 @ X13)
% 0.22/0.55          | ~ (l1_pre_topc @ X13))),
% 0.22/0.55      inference('cnf', [status(esa)], [d6_pre_topc])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (v3_pre_topc @ 
% 0.22/0.55             (k7_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.22/0.55          | ~ (l1_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | (v4_pre_topc @ X1 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.55  thf(dt_k2_subset_1, axiom,
% 0.22/0.55    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (![X3 : $i]: (m1_subset_1 @ (k2_subset_1 @ X3) @ (k1_zfmisc_1 @ X3))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.22/0.55  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.22/0.55  thf('43', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 0.22/0.55      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.22/0.55  thf('44', plain, (![X3 : $i]: (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X3))),
% 0.22/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.55  thf(redefinition_k7_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.22/0.55          | ((k7_subset_1 @ X9 @ X8 @ X10) = (k4_xboole_0 @ X8 @ X10)))),
% 0.22/0.55      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((k7_subset_1 @ X0 @ X0 @ X1) = (k4_xboole_0 @ X0 @ X1))),
% 0.22/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (v3_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ X0) @ X1) @ X0)
% 0.22/0.55          | ~ (l1_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_pre_topc @ X0)
% 0.22/0.55          | (v4_pre_topc @ X1 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.55      inference('demod', [status(thm)], ['41', '46'])).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      ((~ (v3_pre_topc @ sk_D @ sk_B)
% 0.22/0.55        | ~ (m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ 
% 0.22/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))
% 0.22/0.55        | (v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ sk_B)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_B)
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['38', '47'])).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf('50', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('51', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      ((~ (v3_pre_topc @ sk_D @ sk_B)
% 0.22/0.55        | (v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (((v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ sk_B))
% 0.22/0.55         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['19', '52'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      ((m1_subset_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.55  thf(t52_pre_topc, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.22/0.55             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.22/0.55               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (![X15 : $i, X16 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.22/0.55          | ~ (v4_pre_topc @ X15 @ X16)
% 0.22/0.55          | ((k2_pre_topc @ X16 @ X15) = (X15))
% 0.22/0.55          | ~ (l1_pre_topc @ X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.55        | ((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))
% 0.22/0.55            = (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))
% 0.22/0.55        | ~ (v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.22/0.55      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.55  thf('57', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('58', plain,
% 0.22/0.55      ((((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))
% 0.22/0.55          = (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))
% 0.22/0.55        | ~ (v4_pre_topc @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.22/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.55  thf('59', plain,
% 0.22/0.55      ((((k2_pre_topc @ sk_B @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))
% 0.22/0.55          = (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D)))
% 0.22/0.55         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['53', '58'])).
% 0.22/0.55  thf('60', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(d1_tops_1, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_pre_topc @ A ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55           ( ( k1_tops_1 @ A @ B ) =
% 0.22/0.55             ( k3_subset_1 @
% 0.22/0.55               ( u1_struct_0 @ A ) @ 
% 0.22/0.55               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.22/0.55  thf('61', plain,
% 0.22/0.55      (![X17 : $i, X18 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.55          | ((k1_tops_1 @ X18 @ X17)
% 0.22/0.55              = (k3_subset_1 @ (u1_struct_0 @ X18) @ 
% 0.22/0.55                 (k2_pre_topc @ X18 @ (k3_subset_1 @ (u1_struct_0 @ X18) @ X17))))
% 0.22/0.55          | ~ (l1_pre_topc @ X18))),
% 0.22/0.55      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      ((~ (l1_pre_topc @ sk_B)
% 0.22/0.55        | ((k1_tops_1 @ sk_B @ sk_D)
% 0.22/0.55            = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55               (k2_pre_topc @ sk_B @ 
% 0.22/0.55                (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.55  thf('63', plain, ((l1_pre_topc @ sk_B)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('64', plain,
% 0.22/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('65', plain,
% 0.22/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.55  thf('66', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.55  thf('67', plain,
% 0.22/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.55      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.55  thf('68', plain,
% 0.22/0.55      ((((k3_subset_1 @ (k2_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55          = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.22/0.55        | ~ (l1_struct_0 @ sk_B))),
% 0.22/0.55      inference('sup+', [status(thm)], ['66', '67'])).
% 0.22/0.55  thf('69', plain, ((l1_struct_0 @ sk_B)),
% 0.22/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.55  thf('70', plain,
% 0.22/0.55      (((k3_subset_1 @ (k2_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['68', '69'])).
% 0.22/0.55  thf('71', plain,
% 0.22/0.55      (((k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55         = (k4_xboole_0 @ (u1_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.55      inference('sup+', [status(thm)], ['65', '70'])).
% 0.22/0.55  thf('72', plain,
% 0.22/0.55      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)
% 0.22/0.55         = (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))),
% 0.22/0.55      inference('demod', [status(thm)], ['64', '71'])).
% 0.22/0.55  thf('73', plain,
% 0.22/0.55      (((k1_tops_1 @ sk_B @ sk_D)
% 0.22/0.55         = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55            (k2_pre_topc @ sk_B @ (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))))),
% 0.22/0.55      inference('demod', [status(thm)], ['62', '63', '72'])).
% 0.22/0.55  thf('74', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_B @ sk_D)
% 0.22/0.55          = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.22/0.55             (k4_xboole_0 @ (k2_struct_0 @ sk_B) @ sk_D))))
% 0.22/0.55         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['59', '73'])).
% 0.22/0.55  thf('75', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.22/0.55         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.22/0.55      inference('sup+', [status(thm)], ['17', '74'])).
% 0.22/0.55  thf('76', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D)) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('77', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D)))
% 0.22/0.55         <= (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))))),
% 0.22/0.55      inference('split', [status(esa)], ['76'])).
% 0.22/0.55  thf('78', plain,
% 0.22/0.55      (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))) | 
% 0.22/0.55       ~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.22/0.55      inference('split', [status(esa)], ['76'])).
% 0.22/0.55  thf('79', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D))
% 0.22/0.55        | ((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('80', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) | 
% 0.22/0.55       ~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))),
% 0.22/0.55      inference('split', [status(esa)], ['79'])).
% 0.22/0.55  thf('81', plain,
% 0.22/0.55      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.22/0.55         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.22/0.55      inference('split', [status(esa)], ['79'])).
% 0.22/0.55  thf('82', plain,
% 0.22/0.55      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(fc9_tops_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & 
% 0.22/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.55       ( v3_pre_topc @ ( k1_tops_1 @ A @ B ) @ A ) ))).
% 0.22/0.55  thf('83', plain,
% 0.22/0.55      (![X19 : $i, X20 : $i]:
% 0.22/0.55         (~ (l1_pre_topc @ X19)
% 0.22/0.55          | ~ (v2_pre_topc @ X19)
% 0.22/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.55          | (v3_pre_topc @ (k1_tops_1 @ X19 @ X20) @ X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc9_tops_1])).
% 0.22/0.55  thf('84', plain,
% 0.22/0.55      (((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)
% 0.22/0.55        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.55        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.22/0.55  thf('85', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('86', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('87', plain, ((v3_pre_topc @ (k1_tops_1 @ sk_A @ sk_C) @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['84', '85', '86'])).
% 0.22/0.55  thf('88', plain,
% 0.22/0.55      (((v3_pre_topc @ sk_C @ sk_A))
% 0.22/0.55         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.22/0.55      inference('sup+', [status(thm)], ['81', '87'])).
% 0.22/0.55  thf('89', plain,
% 0.22/0.55      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.22/0.55      inference('split', [status(esa)], ['76'])).
% 0.22/0.55  thf('90', plain,
% 0.22/0.55      (((v3_pre_topc @ sk_C @ sk_A)) | ~ (((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['88', '89'])).
% 0.22/0.55  thf('91', plain, (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['78', '80', '90'])).
% 0.22/0.55  thf('92', plain, (((k1_tops_1 @ sk_B @ sk_D) != (sk_D))),
% 0.22/0.55      inference('simpl_trail', [status(thm)], ['77', '91'])).
% 0.22/0.55  thf('93', plain, (~ ((v3_pre_topc @ sk_D @ sk_B))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['75', '92'])).
% 0.22/0.55  thf('94', plain,
% 0.22/0.55      (~ ((v3_pre_topc @ sk_C @ sk_A)) | ((v3_pre_topc @ sk_D @ sk_B))),
% 0.22/0.55      inference('split', [status(esa)], ['18'])).
% 0.22/0.55  thf('95', plain, ($false),
% 0.22/0.55      inference('sat_resolution*', [status(thm)], ['1', '93', '94', '90'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
