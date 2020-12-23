%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M7E91JbDzs

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:47 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 190 expanded)
%              Number of leaves         :   17 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  746 (3253 expanded)
%              Number of equality atoms :   18 (  91 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t34_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                  = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) )
                    = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tops_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t51_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k2_pre_topc @ A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ X9 @ ( k9_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 @ X10 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ X9 ) @ ( k2_pre_topc @ X9 @ X8 ) @ ( k2_pre_topc @ X9 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t51_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ X6 @ ( k2_pre_topc @ X7 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('8',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ sk_B @ ( k2_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B )
    | ( ( k2_pre_topc @ sk_A @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( r1_tarski @ C @ B ) )
               => ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ( r1_tarski @ ( k2_pre_topc @ X12 @ X13 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v4_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_B )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['20','22'])).

thf('24',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['5','24'])).

thf('26',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ X6 @ ( k2_pre_topc @ X7 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r1_tarski @ sk_C @ ( k2_pre_topc @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,
    ( ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_C )
    | ( ( k2_pre_topc @ sk_A @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X11 @ X12 )
      | ~ ( r1_tarski @ X13 @ X11 )
      | ( r1_tarski @ ( k2_pre_topc @ X12 @ X13 ) @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_tops_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v4_pre_topc @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v4_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ X0 ) @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_C )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('43',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['33','43'])).

thf('45',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['26','44'])).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
      = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( r1_tarski @ X6 @ ( k2_pre_topc @ X7 @ X6 ) )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C )
    = ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','54'])).

thf('56',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_pre_topc @ sk_A @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['12','23'])).

thf('58',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k2_pre_topc @ sk_A @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['33','43'])).

thf('60',plain,(
    ( k2_pre_topc @ sk_A @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
 != ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M7E91JbDzs
% 0.11/0.30  % Computer   : n009.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 11:32:41 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running portfolio for 600 s
% 0.11/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.31  % Number of cores: 8
% 0.11/0.31  % Python version: Python 3.6.8
% 0.16/0.31  % Running in FO mode
% 0.16/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.16/0.46  % Solved by: fo/fo7.sh
% 0.16/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.16/0.46  % done 62 iterations in 0.045s
% 0.16/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.16/0.46  % SZS output start Refutation
% 0.16/0.46  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.16/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.16/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.16/0.46  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.16/0.46  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.16/0.46  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.16/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.16/0.46  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.16/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.16/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.16/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.16/0.46  thf(t34_tops_1, conjecture,
% 0.16/0.46    (![A:$i]:
% 0.16/0.46     ( ( l1_pre_topc @ A ) =>
% 0.16/0.46       ( ![B:$i]:
% 0.16/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46           ( ![C:$i]:
% 0.16/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.16/0.46                 ( ( k2_pre_topc @
% 0.16/0.46                     A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.16/0.46                   ( k9_subset_1 @
% 0.16/0.46                     ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.16/0.46                     ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.16/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.16/0.46    (~( ![A:$i]:
% 0.16/0.46        ( ( l1_pre_topc @ A ) =>
% 0.16/0.46          ( ![B:$i]:
% 0.16/0.46            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46              ( ![C:$i]:
% 0.16/0.46                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.16/0.46                    ( ( k2_pre_topc @
% 0.16/0.46                        A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) =
% 0.16/0.46                      ( k9_subset_1 @
% 0.16/0.46                        ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.16/0.46                        ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) ) )),
% 0.16/0.46    inference('cnf.neg', [status(esa)], [t34_tops_1])).
% 0.16/0.46  thf('0', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('1', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf(t51_pre_topc, axiom,
% 0.16/0.46    (![A:$i]:
% 0.16/0.46     ( ( l1_pre_topc @ A ) =>
% 0.16/0.46       ( ![B:$i]:
% 0.16/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46           ( ![C:$i]:
% 0.16/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46               ( r1_tarski @
% 0.16/0.46                 ( k2_pre_topc @
% 0.16/0.46                   A @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 0.16/0.46                 ( k9_subset_1 @
% 0.16/0.46                   ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ B ) @ 
% 0.16/0.46                   ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 0.16/0.46  thf('2', plain,
% 0.16/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.16/0.46          | (r1_tarski @ 
% 0.16/0.46             (k2_pre_topc @ X9 @ (k9_subset_1 @ (u1_struct_0 @ X9) @ X8 @ X10)) @ 
% 0.16/0.46             (k9_subset_1 @ (u1_struct_0 @ X9) @ (k2_pre_topc @ X9 @ X8) @ 
% 0.16/0.46              (k2_pre_topc @ X9 @ X10)))
% 0.16/0.46          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.16/0.46          | ~ (l1_pre_topc @ X9))),
% 0.16/0.46      inference('cnf', [status(esa)], [t51_pre_topc])).
% 0.16/0.46  thf('3', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (~ (l1_pre_topc @ sk_A)
% 0.16/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.16/0.46          | (r1_tarski @ 
% 0.16/0.46             (k2_pre_topc @ sk_A @ 
% 0.16/0.46              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.16/0.46             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.16/0.46              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 0.16/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.16/0.46  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('5', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.16/0.46          | (r1_tarski @ 
% 0.16/0.46             (k2_pre_topc @ sk_A @ 
% 0.16/0.46              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.16/0.46             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.16/0.46              (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ X0))))),
% 0.16/0.46      inference('demod', [status(thm)], ['3', '4'])).
% 0.16/0.46  thf('6', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf(t48_pre_topc, axiom,
% 0.16/0.46    (![A:$i]:
% 0.16/0.46     ( ( l1_pre_topc @ A ) =>
% 0.16/0.46       ( ![B:$i]:
% 0.16/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.16/0.46  thf('7', plain,
% 0.16/0.46      (![X6 : $i, X7 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.16/0.46          | (r1_tarski @ X6 @ (k2_pre_topc @ X7 @ X6))
% 0.16/0.46          | ~ (l1_pre_topc @ X7))),
% 0.16/0.46      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.16/0.46  thf('8', plain,
% 0.16/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.16/0.46        | (r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B)))),
% 0.16/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.16/0.46  thf('9', plain, ((l1_pre_topc @ sk_A)),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('10', plain, ((r1_tarski @ sk_B @ (k2_pre_topc @ sk_A @ sk_B))),
% 0.16/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.16/0.46  thf(d10_xboole_0, axiom,
% 0.16/0.46    (![A:$i,B:$i]:
% 0.16/0.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.16/0.46  thf('11', plain,
% 0.16/0.46      (![X0 : $i, X2 : $i]:
% 0.16/0.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.16/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.16/0.46  thf('12', plain,
% 0.16/0.46      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)
% 0.16/0.46        | ((k2_pre_topc @ sk_A @ sk_B) = (sk_B)))),
% 0.16/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.16/0.46  thf('13', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('14', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf(t31_tops_1, axiom,
% 0.16/0.46    (![A:$i]:
% 0.16/0.46     ( ( l1_pre_topc @ A ) =>
% 0.16/0.46       ( ![B:$i]:
% 0.16/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46           ( ![C:$i]:
% 0.16/0.46             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.16/0.46               ( ( ( v4_pre_topc @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.16/0.46                 ( r1_tarski @ ( k2_pre_topc @ A @ C ) @ B ) ) ) ) ) ) ))).
% 0.16/0.46  thf('15', plain,
% 0.16/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.16/0.46          | ~ (v4_pre_topc @ X11 @ X12)
% 0.16/0.46          | ~ (r1_tarski @ X13 @ X11)
% 0.16/0.46          | (r1_tarski @ (k2_pre_topc @ X12 @ X13) @ X11)
% 0.16/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.16/0.46          | ~ (l1_pre_topc @ X12))),
% 0.16/0.46      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.16/0.46  thf('16', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (~ (l1_pre_topc @ sk_A)
% 0.16/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.16/0.46          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 0.16/0.46          | ~ (r1_tarski @ X0 @ sk_B)
% 0.16/0.46          | ~ (v4_pre_topc @ sk_B @ sk_A))),
% 0.16/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.16/0.46  thf('17', plain, ((l1_pre_topc @ sk_A)),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('18', plain, ((v4_pre_topc @ sk_B @ sk_A)),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('19', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.16/0.46          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_B)
% 0.16/0.46          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.16/0.46      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.16/0.46  thf('20', plain,
% 0.16/0.46      ((~ (r1_tarski @ sk_B @ sk_B)
% 0.16/0.46        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B))),
% 0.16/0.46      inference('sup-', [status(thm)], ['13', '19'])).
% 0.16/0.46  thf('21', plain,
% 0.16/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.16/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.16/0.46  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.16/0.46      inference('simplify', [status(thm)], ['21'])).
% 0.16/0.46  thf('23', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ sk_B)),
% 0.16/0.46      inference('demod', [status(thm)], ['20', '22'])).
% 0.16/0.46  thf('24', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.16/0.46      inference('demod', [status(thm)], ['12', '23'])).
% 0.16/0.46  thf('25', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.16/0.46          | (r1_tarski @ 
% 0.16/0.46             (k2_pre_topc @ sk_A @ 
% 0.16/0.46              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)) @ 
% 0.16/0.46             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.16/0.46              (k2_pre_topc @ sk_A @ X0))))),
% 0.16/0.46      inference('demod', [status(thm)], ['5', '24'])).
% 0.16/0.46  thf('26', plain,
% 0.16/0.46      ((r1_tarski @ 
% 0.16/0.46        (k2_pre_topc @ sk_A @ 
% 0.16/0.46         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 0.16/0.46        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.16/0.46         (k2_pre_topc @ sk_A @ sk_C)))),
% 0.16/0.46      inference('sup-', [status(thm)], ['0', '25'])).
% 0.16/0.46  thf('27', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('28', plain,
% 0.16/0.46      (![X6 : $i, X7 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.16/0.46          | (r1_tarski @ X6 @ (k2_pre_topc @ X7 @ X6))
% 0.16/0.46          | ~ (l1_pre_topc @ X7))),
% 0.16/0.46      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.16/0.46  thf('29', plain,
% 0.16/0.46      ((~ (l1_pre_topc @ sk_A)
% 0.16/0.46        | (r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.16/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.16/0.46  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('31', plain, ((r1_tarski @ sk_C @ (k2_pre_topc @ sk_A @ sk_C))),
% 0.16/0.46      inference('demod', [status(thm)], ['29', '30'])).
% 0.16/0.46  thf('32', plain,
% 0.16/0.46      (![X0 : $i, X2 : $i]:
% 0.16/0.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.16/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.16/0.46  thf('33', plain,
% 0.16/0.46      ((~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_C) @ sk_C)
% 0.16/0.46        | ((k2_pre_topc @ sk_A @ sk_C) = (sk_C)))),
% 0.16/0.46      inference('sup-', [status(thm)], ['31', '32'])).
% 0.16/0.46  thf('34', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('35', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('36', plain,
% 0.16/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.16/0.46          | ~ (v4_pre_topc @ X11 @ X12)
% 0.16/0.46          | ~ (r1_tarski @ X13 @ X11)
% 0.16/0.46          | (r1_tarski @ (k2_pre_topc @ X12 @ X13) @ X11)
% 0.16/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.16/0.46          | ~ (l1_pre_topc @ X12))),
% 0.16/0.46      inference('cnf', [status(esa)], [t31_tops_1])).
% 0.16/0.46  thf('37', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (~ (l1_pre_topc @ sk_A)
% 0.16/0.46          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.16/0.46          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_C)
% 0.16/0.46          | ~ (r1_tarski @ X0 @ sk_C)
% 0.16/0.46          | ~ (v4_pre_topc @ sk_C @ sk_A))),
% 0.16/0.46      inference('sup-', [status(thm)], ['35', '36'])).
% 0.16/0.46  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('39', plain, ((v4_pre_topc @ sk_C @ sk_A)),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('40', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.16/0.46          | (r1_tarski @ (k2_pre_topc @ sk_A @ X0) @ sk_C)
% 0.16/0.46          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.16/0.46      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.16/0.46  thf('41', plain,
% 0.16/0.46      ((~ (r1_tarski @ sk_C @ sk_C)
% 0.16/0.46        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_C) @ sk_C))),
% 0.16/0.46      inference('sup-', [status(thm)], ['34', '40'])).
% 0.16/0.46  thf('42', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.16/0.46      inference('simplify', [status(thm)], ['21'])).
% 0.16/0.46  thf('43', plain, ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_C) @ sk_C)),
% 0.16/0.46      inference('demod', [status(thm)], ['41', '42'])).
% 0.16/0.46  thf('44', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.16/0.46      inference('demod', [status(thm)], ['33', '43'])).
% 0.16/0.46  thf('45', plain,
% 0.16/0.46      ((r1_tarski @ 
% 0.16/0.46        (k2_pre_topc @ sk_A @ 
% 0.16/0.46         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 0.16/0.46        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.16/0.46      inference('demod', [status(thm)], ['26', '44'])).
% 0.16/0.46  thf('46', plain,
% 0.16/0.46      (![X0 : $i, X2 : $i]:
% 0.16/0.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.16/0.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.16/0.46  thf('47', plain,
% 0.16/0.46      ((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.16/0.46           (k2_pre_topc @ sk_A @ 
% 0.16/0.46            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))
% 0.16/0.46        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.16/0.46            = (k2_pre_topc @ sk_A @ 
% 0.16/0.46               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))))),
% 0.16/0.46      inference('sup-', [status(thm)], ['45', '46'])).
% 0.16/0.46  thf('48', plain,
% 0.16/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf(dt_k9_subset_1, axiom,
% 0.16/0.46    (![A:$i,B:$i,C:$i]:
% 0.16/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.16/0.46       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.16/0.46  thf('49', plain,
% 0.16/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.16/0.46         ((m1_subset_1 @ (k9_subset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X3))
% 0.16/0.46          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.16/0.46      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.16/0.46  thf('50', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.16/0.46          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.16/0.46      inference('sup-', [status(thm)], ['48', '49'])).
% 0.16/0.46  thf('51', plain,
% 0.16/0.46      (![X6 : $i, X7 : $i]:
% 0.16/0.46         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.16/0.46          | (r1_tarski @ X6 @ (k2_pre_topc @ X7 @ X6))
% 0.16/0.46          | ~ (l1_pre_topc @ X7))),
% 0.16/0.46      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.16/0.46  thf('52', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (~ (l1_pre_topc @ sk_A)
% 0.16/0.46          | (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.16/0.46             (k2_pre_topc @ sk_A @ 
% 0.16/0.46              (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C))))),
% 0.16/0.46      inference('sup-', [status(thm)], ['50', '51'])).
% 0.16/0.46  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('54', plain,
% 0.16/0.46      (![X0 : $i]:
% 0.16/0.46         (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.16/0.46          (k2_pre_topc @ sk_A @ 
% 0.16/0.46           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)))),
% 0.16/0.46      inference('demod', [status(thm)], ['52', '53'])).
% 0.16/0.46  thf('55', plain,
% 0.16/0.46      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)
% 0.16/0.46         = (k2_pre_topc @ sk_A @ 
% 0.16/0.46            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)))),
% 0.16/0.46      inference('demod', [status(thm)], ['47', '54'])).
% 0.16/0.46  thf('56', plain,
% 0.16/0.46      (((k2_pre_topc @ sk_A @ 
% 0.16/0.46         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.16/0.46         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.16/0.46             (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_C)))),
% 0.16/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.16/0.46  thf('57', plain, (((k2_pre_topc @ sk_A @ sk_B) = (sk_B))),
% 0.16/0.46      inference('demod', [status(thm)], ['12', '23'])).
% 0.16/0.46  thf('58', plain,
% 0.16/0.46      (((k2_pre_topc @ sk_A @ 
% 0.16/0.46         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.16/0.46         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.16/0.46             (k2_pre_topc @ sk_A @ sk_C)))),
% 0.16/0.46      inference('demod', [status(thm)], ['56', '57'])).
% 0.16/0.46  thf('59', plain, (((k2_pre_topc @ sk_A @ sk_C) = (sk_C))),
% 0.16/0.46      inference('demod', [status(thm)], ['33', '43'])).
% 0.16/0.46  thf('60', plain,
% 0.16/0.46      (((k2_pre_topc @ sk_A @ 
% 0.16/0.46         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 0.16/0.46         != (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 0.16/0.46      inference('demod', [status(thm)], ['58', '59'])).
% 0.16/0.46  thf('61', plain, ($false),
% 0.16/0.46      inference('simplify_reflect-', [status(thm)], ['55', '60'])).
% 0.16/0.46  
% 0.16/0.46  % SZS output end Refutation
% 0.16/0.46  
% 0.16/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
