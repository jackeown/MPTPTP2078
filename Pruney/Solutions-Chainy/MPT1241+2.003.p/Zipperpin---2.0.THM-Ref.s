%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kc4lz5zngh

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:08 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 168 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  904 (2731 expanded)
%              Number of equality atoms :   53 ( 164 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
    | ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X4 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('12',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('16',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k1_tops_1 @ X9 @ X8 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k2_pre_topc @ X9 @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('19',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_C ) )
    = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,
    ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v2_pre_topc @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
       != X6 )
      | ( v4_pre_topc @ X6 @ X7 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('26',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
     != ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    | ~ ( v2_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
     != ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
       != ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t29_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v4_pre_topc @ B @ A )
          <=> ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('33',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X11 )
      | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('34',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('38',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','38'])).

thf('40',plain,
    ( ( v3_pre_topc @ sk_C @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,
    ( ~ ( v3_pre_topc @ sk_C @ sk_A )
   <= ~ ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_C )
     != sk_C )
    | ( v3_pre_topc @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = sk_C ) ),
    inference(split,[status(esa)],['6'])).

thf('44',plain,
    ( ( v3_pre_topc @ sk_D @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('47',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) @ X11 )
      | ( v4_pre_topc @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t29_tops_1])).

thf('49',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
    | ~ ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_subset_1 @ X3 @ ( k3_subset_1 @ X3 @ X2 ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('53',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','53'])).

thf('55',plain,
    ( ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('57',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ( ( k2_pre_topc @ X7 @ X6 )
        = X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('58',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    | ~ ( v4_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) @ sk_B ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k1_tops_1 @ X9 @ X8 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k2_pre_topc @ X9 @ ( k3_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 ) ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k1_tops_1 @ sk_B @ sk_D )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_pre_topc @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) ) )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_B ) @ sk_D ) )
    = sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('69',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
   <= ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D )
   <= ( ( k1_tops_1 @ sk_B @ sk_D )
     != sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('71',plain,
    ( ( sk_D != sk_D )
   <= ( ( ( k1_tops_1 @ sk_B @ sk_D )
       != sk_D )
      & ( v3_pre_topc @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k1_tops_1 @ sk_B @ sk_D )
      = sk_D )
    | ~ ( v3_pre_topc @ sk_D @ sk_B ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','42','43','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Kc4lz5zngh
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:30:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.58  % Solved by: fo/fo7.sh
% 0.37/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.58  % done 244 iterations in 0.120s
% 0.37/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.58  % SZS output start Refutation
% 0.37/0.58  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.58  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.58  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.37/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.58  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.58  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.58  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.37/0.58  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.58  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.37/0.58  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.58  thf(t55_tops_1, conjecture,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( l1_pre_topc @ B ) =>
% 0.37/0.58           ( ![C:$i]:
% 0.37/0.58             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58               ( ![D:$i]:
% 0.37/0.58                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.58                   ( ( ( v3_pre_topc @ D @ B ) =>
% 0.37/0.58                       ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.37/0.58                     ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.37/0.58                       ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ))).
% 0.37/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.58    (~( ![A:$i]:
% 0.37/0.58        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.37/0.58          ( ![B:$i]:
% 0.37/0.58            ( ( l1_pre_topc @ B ) =>
% 0.37/0.58              ( ![C:$i]:
% 0.37/0.58                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58                  ( ![D:$i]:
% 0.37/0.58                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.37/0.58                      ( ( ( v3_pre_topc @ D @ B ) =>
% 0.37/0.58                          ( ( k1_tops_1 @ B @ D ) = ( D ) ) ) & 
% 0.37/0.58                        ( ( ( k1_tops_1 @ A @ C ) = ( C ) ) =>
% 0.37/0.58                          ( v3_pre_topc @ C @ A ) ) ) ) ) ) ) ) ) ) )),
% 0.37/0.58    inference('cnf.neg', [status(esa)], [t55_tops_1])).
% 0.37/0.58  thf('0', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_D @ sk_B) | ((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('1', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_D @ sk_B)) | (((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.37/0.58      inference('split', [status(esa)], ['0'])).
% 0.37/0.58  thf('2', plain,
% 0.37/0.58      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D)) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('3', plain,
% 0.37/0.58      (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))) | 
% 0.37/0.58       ~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.58      inference('split', [status(esa)], ['2'])).
% 0.37/0.58  thf('4', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_D @ sk_B) | ~ (v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('5', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_D @ sk_B)) | ~ ((v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.58      inference('split', [status(esa)], ['4'])).
% 0.37/0.58  thf('6', plain,
% 0.37/0.58      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D))
% 0.37/0.58        | ((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('7', plain,
% 0.37/0.58      ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))
% 0.37/0.58         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.37/0.58      inference('split', [status(esa)], ['6'])).
% 0.37/0.58  thf('8', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(dt_k3_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.37/0.58  thf('9', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.37/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.58  thf('10', plain,
% 0.37/0.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf(dt_k2_pre_topc, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.58         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.58       ( m1_subset_1 @
% 0.37/0.58         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.58  thf('11', plain,
% 0.37/0.58      (![X4 : $i, X5 : $i]:
% 0.37/0.58         (~ (l1_pre_topc @ X4)
% 0.37/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.37/0.58          | (m1_subset_1 @ (k2_pre_topc @ X4 @ X5) @ 
% 0.37/0.58             (k1_zfmisc_1 @ (u1_struct_0 @ X4))))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.58  thf('12', plain,
% 0.37/0.58      (((m1_subset_1 @ 
% 0.37/0.58         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.37/0.58         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.37/0.58        | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.37/0.58  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('14', plain,
% 0.37/0.58      ((m1_subset_1 @ 
% 0.37/0.58        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.37/0.58  thf(involutiveness_k3_subset_1, axiom,
% 0.37/0.58    (![A:$i,B:$i]:
% 0.37/0.58     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.58       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.37/0.58  thf('15', plain,
% 0.37/0.58      (![X2 : $i, X3 : $i]:
% 0.37/0.58         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.37/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.37/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.37/0.58  thf('16', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.37/0.58         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.58  thf('17', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf(d1_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( k1_tops_1 @ A @ B ) =
% 0.37/0.58             ( k3_subset_1 @
% 0.37/0.58               ( u1_struct_0 @ A ) @ 
% 0.37/0.58               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.37/0.58  thf('18', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.37/0.58          | ((k1_tops_1 @ X9 @ X8)
% 0.37/0.58              = (k3_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.37/0.58                 (k2_pre_topc @ X9 @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8))))
% 0.37/0.58          | ~ (l1_pre_topc @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.37/0.58  thf('19', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | ((k1_tops_1 @ sk_A @ sk_C)
% 0.37/0.58            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58               (k2_pre_topc @ sk_A @ 
% 0.37/0.58                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.58  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('21', plain,
% 0.37/0.58      (((k1_tops_1 @ sk_A @ sk_C)
% 0.37/0.58         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.37/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.37/0.58  thf('22', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_C))
% 0.37/0.58         = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.37/0.58      inference('demod', [status(thm)], ['16', '21'])).
% 0.37/0.58  thf('23', plain,
% 0.37/0.58      ((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.37/0.58          = (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.37/0.58         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.37/0.58      inference('sup+', [status(thm)], ['7', '22'])).
% 0.37/0.58  thf('24', plain,
% 0.37/0.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf(t52_pre_topc, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.37/0.58             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.37/0.58               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.37/0.58  thf('25', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.37/0.58          | ~ (v2_pre_topc @ X7)
% 0.37/0.58          | ((k2_pre_topc @ X7 @ X6) != (X6))
% 0.37/0.58          | (v4_pre_topc @ X6 @ X7)
% 0.37/0.58          | ~ (l1_pre_topc @ X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.58  thf('26', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.37/0.58        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.58            != (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.58        | ~ (v2_pre_topc @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.37/0.58  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('28', plain, ((v2_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('29', plain,
% 0.37/0.58      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)
% 0.37/0.58        | ((k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.58            != (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.37/0.58      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.37/0.58  thf('30', plain,
% 0.37/0.58      (((((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)
% 0.37/0.58           != (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.37/0.58         | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A)))
% 0.37/0.58         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['23', '29'])).
% 0.37/0.58  thf('31', plain,
% 0.37/0.58      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))
% 0.37/0.58         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.37/0.58      inference('simplify', [status(thm)], ['30'])).
% 0.37/0.58  thf('32', plain,
% 0.37/0.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.58  thf(t29_tops_1, axiom,
% 0.37/0.58    (![A:$i]:
% 0.37/0.58     ( ( l1_pre_topc @ A ) =>
% 0.37/0.58       ( ![B:$i]:
% 0.37/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.58           ( ( v4_pre_topc @ B @ A ) <=>
% 0.37/0.58             ( v3_pre_topc @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.37/0.58  thf('33', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.58          | ~ (v4_pre_topc @ X10 @ X11)
% 0.37/0.58          | (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10) @ X11)
% 0.37/0.58          | ~ (l1_pre_topc @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.37/0.58  thf('34', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_A)
% 0.37/0.58        | (v3_pre_topc @ 
% 0.37/0.58           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.37/0.58           sk_A)
% 0.37/0.58        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.58  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('36', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('37', plain,
% 0.37/0.58      (![X2 : $i, X3 : $i]:
% 0.37/0.58         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.37/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.37/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.37/0.58  thf('38', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.37/0.58         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 0.37/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.58  thf('39', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_C @ sk_A)
% 0.37/0.58        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A))),
% 0.37/0.58      inference('demod', [status(thm)], ['34', '35', '38'])).
% 0.37/0.58  thf('40', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_C @ sk_A))
% 0.37/0.58         <= ((((k1_tops_1 @ sk_A @ sk_C) = (sk_C))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['31', '39'])).
% 0.37/0.58  thf('41', plain,
% 0.37/0.58      ((~ (v3_pre_topc @ sk_C @ sk_A)) <= (~ ((v3_pre_topc @ sk_C @ sk_A)))),
% 0.37/0.58      inference('split', [status(esa)], ['2'])).
% 0.37/0.58  thf('42', plain,
% 0.37/0.58      (~ (((k1_tops_1 @ sk_A @ sk_C) = (sk_C))) | ((v3_pre_topc @ sk_C @ sk_A))),
% 0.37/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.58  thf('43', plain,
% 0.37/0.58      (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))) | 
% 0.37/0.58       (((k1_tops_1 @ sk_A @ sk_C) = (sk_C)))),
% 0.37/0.58      inference('split', [status(esa)], ['6'])).
% 0.37/0.58  thf('44', plain,
% 0.37/0.58      (((v3_pre_topc @ sk_D @ sk_B)) <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.58      inference('split', [status(esa)], ['4'])).
% 0.37/0.58  thf('45', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('46', plain,
% 0.37/0.58      (![X0 : $i, X1 : $i]:
% 0.37/0.58         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.37/0.58          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.58      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.37/0.58  thf('47', plain,
% 0.37/0.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.58  thf('48', plain,
% 0.37/0.58      (![X10 : $i, X11 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.37/0.58          | ~ (v3_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10) @ X11)
% 0.37/0.58          | (v4_pre_topc @ X10 @ X11)
% 0.37/0.58          | ~ (l1_pre_topc @ X11))),
% 0.37/0.58      inference('cnf', [status(esa)], [t29_tops_1])).
% 0.37/0.58  thf('49', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.58        | (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B)
% 0.37/0.58        | ~ (v3_pre_topc @ 
% 0.37/0.58             (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58              (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) @ 
% 0.37/0.58             sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.58  thf('50', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('51', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('52', plain,
% 0.37/0.58      (![X2 : $i, X3 : $i]:
% 0.37/0.58         (((k3_subset_1 @ X3 @ (k3_subset_1 @ X3 @ X2)) = (X2))
% 0.37/0.58          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.37/0.58      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.37/0.58  thf('53', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58         (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.37/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.58  thf('54', plain,
% 0.37/0.58      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B)
% 0.37/0.58        | ~ (v3_pre_topc @ sk_D @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['49', '50', '53'])).
% 0.37/0.58  thf('55', plain,
% 0.37/0.58      (((v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))
% 0.37/0.58         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['44', '54'])).
% 0.37/0.58  thf('56', plain,
% 0.37/0.58      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ 
% 0.37/0.58        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.58  thf('57', plain,
% 0.37/0.58      (![X6 : $i, X7 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.37/0.58          | ~ (v4_pre_topc @ X6 @ X7)
% 0.37/0.58          | ((k2_pre_topc @ X7 @ X6) = (X6))
% 0.37/0.58          | ~ (l1_pre_topc @ X7))),
% 0.37/0.58      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.37/0.58  thf('58', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.58        | ((k2_pre_topc @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.37/0.58            = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.37/0.58        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.37/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.37/0.58  thf('59', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('60', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.37/0.58          = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.37/0.58        | ~ (v4_pre_topc @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D) @ sk_B))),
% 0.37/0.58      inference('demod', [status(thm)], ['58', '59'])).
% 0.37/0.58  thf('61', plain,
% 0.37/0.58      ((((k2_pre_topc @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))
% 0.37/0.58          = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)))
% 0.37/0.58         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['55', '60'])).
% 0.37/0.58  thf('62', plain,
% 0.37/0.58      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('63', plain,
% 0.37/0.58      (![X8 : $i, X9 : $i]:
% 0.37/0.58         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.37/0.58          | ((k1_tops_1 @ X9 @ X8)
% 0.37/0.58              = (k3_subset_1 @ (u1_struct_0 @ X9) @ 
% 0.37/0.58                 (k2_pre_topc @ X9 @ (k3_subset_1 @ (u1_struct_0 @ X9) @ X8))))
% 0.37/0.58          | ~ (l1_pre_topc @ X9))),
% 0.37/0.58      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.37/0.58  thf('64', plain,
% 0.37/0.58      ((~ (l1_pre_topc @ sk_B)
% 0.37/0.58        | ((k1_tops_1 @ sk_B @ sk_D)
% 0.37/0.58            = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58               (k2_pre_topc @ sk_B @ 
% 0.37/0.58                (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)))))),
% 0.37/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.37/0.58  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.37/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.58  thf('66', plain,
% 0.37/0.58      (((k1_tops_1 @ sk_B @ sk_D)
% 0.37/0.58         = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58            (k2_pre_topc @ sk_B @ (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))))),
% 0.37/0.58      inference('demod', [status(thm)], ['64', '65'])).
% 0.37/0.58  thf('67', plain,
% 0.37/0.58      ((((k1_tops_1 @ sk_B @ sk_D)
% 0.37/0.58          = (k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58             (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D))))
% 0.37/0.58         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['61', '66'])).
% 0.37/0.58  thf('68', plain,
% 0.37/0.58      (((k3_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.37/0.58         (k3_subset_1 @ (u1_struct_0 @ sk_B) @ sk_D)) = (sk_D))),
% 0.37/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.58  thf('69', plain,
% 0.37/0.58      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D)))
% 0.37/0.58         <= (((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.58      inference('sup+', [status(thm)], ['67', '68'])).
% 0.37/0.58  thf('70', plain,
% 0.37/0.58      ((((k1_tops_1 @ sk_B @ sk_D) != (sk_D)))
% 0.37/0.58         <= (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))))),
% 0.37/0.58      inference('split', [status(esa)], ['2'])).
% 0.37/0.58  thf('71', plain,
% 0.37/0.58      ((((sk_D) != (sk_D)))
% 0.37/0.58         <= (~ (((k1_tops_1 @ sk_B @ sk_D) = (sk_D))) & 
% 0.37/0.58             ((v3_pre_topc @ sk_D @ sk_B)))),
% 0.37/0.58      inference('sup-', [status(thm)], ['69', '70'])).
% 0.37/0.58  thf('72', plain,
% 0.37/0.58      ((((k1_tops_1 @ sk_B @ sk_D) = (sk_D))) | ~ ((v3_pre_topc @ sk_D @ sk_B))),
% 0.37/0.58      inference('simplify', [status(thm)], ['71'])).
% 0.37/0.58  thf('73', plain, ($false),
% 0.37/0.58      inference('sat_resolution*', [status(thm)],
% 0.37/0.58                ['1', '3', '5', '42', '43', '72'])).
% 0.37/0.58  
% 0.37/0.58  % SZS output end Refutation
% 0.37/0.58  
% 0.37/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
