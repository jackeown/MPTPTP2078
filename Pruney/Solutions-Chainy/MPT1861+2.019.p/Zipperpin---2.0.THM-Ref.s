%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Ijd9dsgOl

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:14 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 185 expanded)
%              Number of leaves         :   21 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  660 (1989 expanded)
%              Number of equality atoms :   20 (  47 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t29_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v2_tex_2 @ B @ A )
                  | ( v2_tex_2 @ C @ A ) )
               => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v2_tex_2 @ B @ A )
                    | ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( r1_tarski @ C @ B )
                  & ( v2_tex_2 @ B @ A ) )
               => ( v2_tex_2 @ C @ A ) ) ) ) ) )).

thf('11',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ( v2_tex_2 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k3_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('27',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('28',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_B ),
    inference('sup+',[status(thm)],['25','36'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X7 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v2_tex_2 @ X18 @ X19 )
      | ~ ( r1_tarski @ X20 @ X18 )
      | ( v2_tex_2 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['44','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['39','54'])).

thf('56',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('57',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('59',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference('sat_resolution*',[status(thm)],['57','58'])).

thf('60',plain,(
    v2_tex_2 @ sk_C @ sk_A ),
    inference(simpl_trail,[status(thm)],['16','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('64',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C ) @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['4','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3Ijd9dsgOl
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 232 iterations in 0.136s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.42/0.61  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.42/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.42/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(t29_tex_2, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( l1_pre_topc @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.42/0.61                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( l1_pre_topc @ A ) =>
% 0.42/0.61          ( ![B:$i]:
% 0.42/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61              ( ![C:$i]:
% 0.42/0.61                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.42/0.61                    ( v2_tex_2 @
% 0.42/0.61                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.42/0.61  thf('0', plain,
% 0.42/0.61      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.42/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.61  thf('5', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(dt_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 0.42/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '6'])).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.42/0.61  thf('10', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(t28_tex_2, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( l1_pre_topc @ A ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.42/0.61               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.42/0.61                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.42/0.61  thf('11', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.42/0.61          | ~ (v2_tex_2 @ X18 @ X19)
% 0.42/0.61          | ~ (r1_tarski @ X20 @ X18)
% 0.42/0.61          | (v2_tex_2 @ X20 @ X19)
% 0.42/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.42/0.61          | ~ (l1_pre_topc @ X19))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (l1_pre_topc @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ sk_C)
% 0.42/0.61          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.42/0.61  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('14', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ sk_C)
% 0.42/0.61          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.42/0.61  thf('15', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.42/0.61      inference('split', [status(esa)], ['15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(commutativity_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.42/0.61  thf('18', plain,
% 0.42/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.42/0.61          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.42/0.61      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.42/0.61           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.42/0.61  thf('20', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k3_xboole_0 @ X0 @ sk_C)
% 0.42/0.61           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['19', '20'])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.42/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.42/0.61  thf('25', plain,
% 0.42/0.61      (((k3_xboole_0 @ sk_B @ sk_C) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup+', [status(thm)], ['21', '24'])).
% 0.42/0.61  thf(dt_k2_subset_1, axiom,
% 0.42/0.61    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.42/0.61  thf('26', plain,
% 0.42/0.61      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.42/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.42/0.61  thf('27', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.42/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.42/0.61  thf('28', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.42/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.61  thf('29', plain,
% 0.42/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 0.42/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.42/0.61  thf('30', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.42/0.61  thf(t3_subset, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X15 : $i, X16 : $i]:
% 0.42/0.61         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.42/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.42/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.42/0.61  thf('33', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.42/0.61      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.42/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('35', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.42/0.61      inference('demod', [status(thm)], ['32', '35'])).
% 0.42/0.61  thf('37', plain, ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_B)),
% 0.42/0.61      inference('sup+', [status(thm)], ['25', '36'])).
% 0.42/0.61  thf(t28_xboole_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_B)
% 0.42/0.61         = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf('40', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('41', plain,
% 0.42/0.61      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k9_subset_1 @ X7 @ X8 @ X9) @ (k1_zfmisc_1 @ X7))
% 0.42/0.61          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X7)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 0.42/0.61           = (k3_xboole_0 @ X0 @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.42/0.61  thf('44', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_B) @ 
% 0.42/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['42', '43'])).
% 0.42/0.61  thf('45', plain,
% 0.42/0.61      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.61      inference('split', [status(esa)], ['15'])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.42/0.61          | ~ (v2_tex_2 @ X18 @ X19)
% 0.42/0.61          | ~ (r1_tarski @ X20 @ X18)
% 0.42/0.61          | (v2_tex_2 @ X20 @ X19)
% 0.42/0.61          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.42/0.61          | ~ (l1_pre_topc @ X19))),
% 0.42/0.61      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.42/0.61  thf('48', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (l1_pre_topc @ sk_A)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.61          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.42/0.61  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('50', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.61          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['48', '49'])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      ((![X0 : $i]:
% 0.42/0.61          (~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.61           | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.61           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.42/0.61         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['45', '50'])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      ((![X0 : $i]:
% 0.42/0.61          ((v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A)
% 0.42/0.61           | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B)))
% 0.42/0.61         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['44', '51'])).
% 0.42/0.61  thf('53', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.42/0.61      inference('demod', [status(thm)], ['32', '35'])).
% 0.42/0.61  thf('54', plain,
% 0.42/0.61      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_A))
% 0.42/0.61         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.61      inference('demod', [status(thm)], ['52', '53'])).
% 0.42/0.61  thf('55', plain,
% 0.42/0.61      (((v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 0.42/0.61         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.61      inference('sup+', [status(thm)], ['39', '54'])).
% 0.42/0.61  thf('56', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.61  thf('57', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['55', '56'])).
% 0.42/0.61  thf('58', plain, (((v2_tex_2 @ sk_C @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.61      inference('split', [status(esa)], ['15'])).
% 0.42/0.61  thf('59', plain, (((v2_tex_2 @ sk_C @ sk_A))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('60', plain, ((v2_tex_2 @ sk_C @ sk_A)),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['16', '59'])).
% 0.42/0.61  thf('61', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.61          | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.61          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.42/0.61      inference('demod', [status(thm)], ['14', '60'])).
% 0.42/0.61  thf('62', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C) @ sk_C)
% 0.42/0.61          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['9', '61'])).
% 0.42/0.61  thf('63', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.42/0.61      inference('demod', [status(thm)], ['32', '35'])).
% 0.42/0.61  thf('64', plain, (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C) @ sk_A)),
% 0.42/0.61      inference('demod', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('65', plain, ($false), inference('demod', [status(thm)], ['4', '64'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
