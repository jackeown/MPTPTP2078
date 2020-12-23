%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yAijvuhNLv

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:56 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 102 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  651 (1379 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t48_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ B @ C )
                 => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t48_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ( r1_tarski @ ( k3_subset_1 @ X3 @ X2 ) @ ( k3_subset_1 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C )
    | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf(t49_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ ( k2_pre_topc @ X8 @ X7 ) @ ( k2_pre_topc @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[t49_pre_topc])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('22',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ( r1_tarski @ ( k3_subset_1 @ X3 @ X2 ) @ ( k3_subset_1 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k1_tops_1 @ X11 @ X10 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k2_pre_topc @ X11 @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k1_tops_1 @ X11 @ X10 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ ( k2_pre_topc @ X11 @ ( k3_subset_1 @ ( u1_struct_0 @ X11 ) @ X10 ) ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('36',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_C )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k1_tops_1 @ sk_A @ sk_C )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('40',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X5 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('41',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['33','38','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yAijvuhNLv
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.11  % Solved by: fo/fo7.sh
% 0.91/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.11  % done 414 iterations in 0.614s
% 0.91/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.11  % SZS output start Refutation
% 0.91/1.11  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.11  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.91/1.11  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.91/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.11  thf(sk_C_type, type, sk_C: $i).
% 0.91/1.11  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.91/1.11  thf(t48_tops_1, conjecture,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( l1_pre_topc @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11           ( ![C:$i]:
% 0.91/1.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11               ( ( r1_tarski @ B @ C ) =>
% 0.91/1.11                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.91/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.11    (~( ![A:$i]:
% 0.91/1.11        ( ( l1_pre_topc @ A ) =>
% 0.91/1.11          ( ![B:$i]:
% 0.91/1.11            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11              ( ![C:$i]:
% 0.91/1.11                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11                  ( ( r1_tarski @ B @ C ) =>
% 0.91/1.11                    ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 0.91/1.11    inference('cnf.neg', [status(esa)], [t48_tops_1])).
% 0.91/1.11  thf('0', plain,
% 0.91/1.11      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('1', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('2', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(t31_subset_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11       ( ![C:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11           ( ( r1_tarski @ B @ C ) <=>
% 0.91/1.11             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.91/1.11  thf('3', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.91/1.11          | ~ (r1_tarski @ X4 @ X2)
% 0.91/1.11          | (r1_tarski @ (k3_subset_1 @ X3 @ X2) @ (k3_subset_1 @ X3 @ X4))
% 0.91/1.11          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.91/1.11  thf('4', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.91/1.11             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.91/1.11          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.91/1.11      inference('sup-', [status(thm)], ['2', '3'])).
% 0.91/1.11  thf('5', plain,
% 0.91/1.11      ((~ (r1_tarski @ sk_B @ sk_C)
% 0.91/1.11        | (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.91/1.11           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['1', '4'])).
% 0.91/1.11  thf('6', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('7', plain,
% 0.91/1.11      ((r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.91/1.11        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.91/1.11      inference('demod', [status(thm)], ['5', '6'])).
% 0.91/1.11  thf('8', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(dt_k3_subset_1, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.11       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.91/1.11  thf('9', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.91/1.11          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.91/1.11  thf('10', plain,
% 0.91/1.11      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.11  thf(t49_pre_topc, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( l1_pre_topc @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11           ( ![C:$i]:
% 0.91/1.11             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11               ( ( r1_tarski @ B @ C ) =>
% 0.91/1.11                 ( r1_tarski @
% 0.91/1.11                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.91/1.11  thf('11', plain,
% 0.91/1.11      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.91/1.11          | ~ (r1_tarski @ X7 @ X9)
% 0.91/1.11          | (r1_tarski @ (k2_pre_topc @ X8 @ X7) @ (k2_pre_topc @ X8 @ X9))
% 0.91/1.11          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.91/1.11          | ~ (l1_pre_topc @ X8))),
% 0.91/1.11      inference('cnf', [status(esa)], [t49_pre_topc])).
% 0.91/1.11  thf('12', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ sk_A)
% 0.91/1.11          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.91/1.11  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('14', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ X0))
% 0.91/1.11          | ~ (r1_tarski @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ X0))),
% 0.91/1.11      inference('demod', [status(thm)], ['12', '13'])).
% 0.91/1.11  thf('15', plain,
% 0.91/1.11      (((r1_tarski @ 
% 0.91/1.11         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.91/1.11         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.91/1.11        | ~ (m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['7', '14'])).
% 0.91/1.11  thf('16', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('17', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         ((m1_subset_1 @ (k3_subset_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))
% 0.91/1.11          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.91/1.11  thf('18', plain,
% 0.91/1.11      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.11  thf('19', plain,
% 0.91/1.11      ((r1_tarski @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.91/1.11      inference('demod', [status(thm)], ['15', '18'])).
% 0.91/1.11  thf('20', plain,
% 0.91/1.11      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.11  thf(dt_k2_pre_topc, axiom,
% 0.91/1.11    (![A:$i,B:$i]:
% 0.91/1.11     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.11         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.11       ( m1_subset_1 @
% 0.91/1.11         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.11  thf('21', plain,
% 0.91/1.11      (![X5 : $i, X6 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X5)
% 0.91/1.11          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.91/1.11          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.91/1.11  thf('22', plain,
% 0.91/1.11      (((m1_subset_1 @ 
% 0.91/1.11         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.91/1.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.11  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('24', plain,
% 0.91/1.11      ((m1_subset_1 @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['22', '23'])).
% 0.91/1.11  thf('25', plain,
% 0.91/1.11      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.91/1.11          | ~ (r1_tarski @ X4 @ X2)
% 0.91/1.11          | (r1_tarski @ (k3_subset_1 @ X3 @ X2) @ (k3_subset_1 @ X3 @ X4))
% 0.91/1.11          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.91/1.11  thf('26', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ 
% 0.91/1.11             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.11              (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 0.91/1.11             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.91/1.11          | ~ (r1_tarski @ X0 @ 
% 0.91/1.11               (k2_pre_topc @ sk_A @ 
% 0.91/1.11                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['24', '25'])).
% 0.91/1.11  thf('27', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(d1_tops_1, axiom,
% 0.91/1.11    (![A:$i]:
% 0.91/1.11     ( ( l1_pre_topc @ A ) =>
% 0.91/1.11       ( ![B:$i]:
% 0.91/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.11           ( ( k1_tops_1 @ A @ B ) =
% 0.91/1.11             ( k3_subset_1 @
% 0.91/1.11               ( u1_struct_0 @ A ) @ 
% 0.91/1.11               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.91/1.11  thf('28', plain,
% 0.91/1.11      (![X10 : $i, X11 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.11          | ((k1_tops_1 @ X11 @ X10)
% 0.91/1.11              = (k3_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.91/1.11                 (k2_pre_topc @ X11 @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10))))
% 0.91/1.11          | ~ (l1_pre_topc @ X11))),
% 0.91/1.11      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.91/1.11  thf('29', plain,
% 0.91/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.11        | ((k1_tops_1 @ sk_A @ sk_B)
% 0.91/1.11            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.11               (k2_pre_topc @ sk_A @ 
% 0.91/1.11                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['27', '28'])).
% 0.91/1.11  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('31', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ sk_B)
% 0.91/1.11         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.11            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.91/1.11      inference('demod', [status(thm)], ['29', '30'])).
% 0.91/1.11  thf('32', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 0.91/1.11          | ~ (r1_tarski @ X0 @ 
% 0.91/1.11               (k2_pre_topc @ sk_A @ 
% 0.91/1.11                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.91/1.11      inference('demod', [status(thm)], ['26', '31'])).
% 0.91/1.11  thf('33', plain,
% 0.91/1.11      (((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 0.91/1.11         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.11          (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.91/1.11        | ~ (m1_subset_1 @ 
% 0.91/1.11             (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['19', '32'])).
% 0.91/1.11  thf('34', plain,
% 0.91/1.11      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('35', plain,
% 0.91/1.11      (![X10 : $i, X11 : $i]:
% 0.91/1.11         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.11          | ((k1_tops_1 @ X11 @ X10)
% 0.91/1.11              = (k3_subset_1 @ (u1_struct_0 @ X11) @ 
% 0.91/1.11                 (k2_pre_topc @ X11 @ (k3_subset_1 @ (u1_struct_0 @ X11) @ X10))))
% 0.91/1.11          | ~ (l1_pre_topc @ X11))),
% 0.91/1.11      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.91/1.11  thf('36', plain,
% 0.91/1.11      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.11        | ((k1_tops_1 @ sk_A @ sk_C)
% 0.91/1.11            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.11               (k2_pre_topc @ sk_A @ 
% 0.91/1.11                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.11  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('38', plain,
% 0.91/1.11      (((k1_tops_1 @ sk_A @ sk_C)
% 0.91/1.11         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.11            (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.91/1.11      inference('demod', [status(thm)], ['36', '37'])).
% 0.91/1.11  thf('39', plain,
% 0.91/1.11      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['8', '9'])).
% 0.91/1.11  thf('40', plain,
% 0.91/1.11      (![X5 : $i, X6 : $i]:
% 0.91/1.11         (~ (l1_pre_topc @ X5)
% 0.91/1.11          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 0.91/1.11          | (m1_subset_1 @ (k2_pre_topc @ X5 @ X6) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (u1_struct_0 @ X5))))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.91/1.11  thf('41', plain,
% 0.91/1.11      (((m1_subset_1 @ 
% 0.91/1.11         (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.91/1.11         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.11        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['39', '40'])).
% 0.91/1.11  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('43', plain,
% 0.91/1.11      ((m1_subset_1 @ 
% 0.91/1.11        (k2_pre_topc @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) @ 
% 0.91/1.11        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.11      inference('demod', [status(thm)], ['41', '42'])).
% 0.91/1.11  thf('44', plain,
% 0.91/1.11      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.91/1.11      inference('demod', [status(thm)], ['33', '38', '43'])).
% 0.91/1.11  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.91/1.11  
% 0.91/1.11  % SZS output end Refutation
% 0.91/1.11  
% 0.91/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
