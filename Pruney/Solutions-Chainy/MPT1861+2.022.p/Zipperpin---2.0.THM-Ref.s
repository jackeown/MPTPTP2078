%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ybAoVF5LVx

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:15 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 161 expanded)
%              Number of leaves         :   18 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  835 (2312 expanded)
%              Number of equality atoms :   14 (  23 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X3 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ( v2_tex_2 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ sk_A )
        | ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,
    ( ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('17',plain,
    ( ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X12 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t38_tops_2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) )
            = B ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('29',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('37',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v2_tex_2 @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ( v2_tex_2 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ sk_A )
        | ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ sk_C ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,
    ( ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('47',plain,
    ( ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf('51',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('52',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['19','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ X12 @ X13 ) ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[t38_tops_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( u1_struct_0 @ ( k1_pre_topc @ X10 @ X9 ) )
        = X9 )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t29_pre_topc])).

thf('64',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['60','61','66'])).

thf('68',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('69',plain,(
    r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['53','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ybAoVF5LVx
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 10:38:59 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.14/0.33  % Running portfolio for 600 s
% 0.14/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.33  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.46/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.69  % Solved by: fo/fo7.sh
% 0.46/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.69  % done 326 iterations in 0.250s
% 0.46/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.69  % SZS output start Refutation
% 0.46/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.69  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.69  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.46/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.69  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.46/0.69  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.46/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.69  thf(t29_tex_2, conjecture,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.46/0.69                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.46/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.69    (~( ![A:$i]:
% 0.46/0.69        ( ( l1_pre_topc @ A ) =>
% 0.46/0.69          ( ![B:$i]:
% 0.46/0.69            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69              ( ![C:$i]:
% 0.46/0.69                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.46/0.69                    ( v2_tex_2 @
% 0.46/0.69                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.46/0.69    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.46/0.69  thf('0', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(commutativity_k9_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.46/0.69  thf('1', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 0.46/0.69          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.46/0.69      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.46/0.69  thf('2', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.46/0.69           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.69  thf('3', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(dt_k9_subset_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.69       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.46/0.69  thf('4', plain,
% 0.46/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.69         ((m1_subset_1 @ (k9_subset_1 @ X3 @ X4 @ X5) @ (k1_zfmisc_1 @ X3))
% 0.46/0.69          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X3)))),
% 0.46/0.69      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.46/0.69  thf('5', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.46/0.69          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.69  thf('6', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('7', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['6'])).
% 0.46/0.69  thf('8', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t28_tex_2, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.46/0.69                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.46/0.69  thf('9', plain,
% 0.46/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.69          | ~ (v2_tex_2 @ X14 @ X15)
% 0.46/0.69          | ~ (r1_tarski @ X16 @ X14)
% 0.46/0.69          | (v2_tex_2 @ X16 @ X15)
% 0.46/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.69          | ~ (l1_pre_topc @ X15))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.46/0.69  thf('10', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ sk_A)
% 0.46/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.69          | (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.69          | ~ (r1_tarski @ X0 @ sk_B)
% 0.46/0.69          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.69  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('12', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.69          | (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.69          | ~ (r1_tarski @ X0 @ sk_B)
% 0.46/0.69          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.46/0.69      inference('demod', [status(thm)], ['10', '11'])).
% 0.46/0.69  thf('13', plain,
% 0.46/0.69      ((![X0 : $i]:
% 0.46/0.69          (~ (r1_tarski @ X0 @ sk_B)
% 0.46/0.69           | (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.69           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.69         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['7', '12'])).
% 0.46/0.69  thf('14', plain,
% 0.46/0.69      ((![X0 : $i]:
% 0.46/0.69          ((v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ sk_A)
% 0.46/0.69           | ~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.46/0.69                sk_B)))
% 0.46/0.69         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['5', '13'])).
% 0.46/0.69  thf('15', plain,
% 0.46/0.69      (((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69            sk_B)
% 0.46/0.69         | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B) @ 
% 0.46/0.69            sk_A)))
% 0.46/0.69         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['2', '14'])).
% 0.46/0.69  thf('16', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.46/0.69           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.69  thf('17', plain,
% 0.46/0.69      (((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69            sk_B)
% 0.46/0.69         | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69            sk_A)))
% 0.46/0.69         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['15', '16'])).
% 0.46/0.69  thf('18', plain,
% 0.46/0.69      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('19', plain,
% 0.46/0.69      ((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69           sk_B))
% 0.46/0.69         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.46/0.69      inference('clc', [status(thm)], ['17', '18'])).
% 0.46/0.69  thf('20', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('21', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t38_tops_2, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69               ( m1_subset_1 @
% 0.46/0.69                 ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ 
% 0.46/0.69                 ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k1_pre_topc @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('22', plain,
% 0.46/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.69          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ X12) @ X11 @ X13) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X12 @ X13))))
% 0.46/0.69          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.69          | ~ (l1_pre_topc @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [t38_tops_2])).
% 0.46/0.69  thf('23', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ sk_A)
% 0.46/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.69          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['21', '22'])).
% 0.46/0.69  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('25', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.69          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))),
% 0.46/0.69      inference('demod', [status(thm)], ['23', '24'])).
% 0.46/0.69  thf('26', plain,
% 0.46/0.69      ((m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['20', '25'])).
% 0.46/0.69  thf('27', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf(t29_pre_topc, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_pre_topc @ A ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69           ( ( u1_struct_0 @ ( k1_pre_topc @ A @ B ) ) = ( B ) ) ) ) ))).
% 0.46/0.69  thf('28', plain,
% 0.46/0.69      (![X9 : $i, X10 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.69          | ((u1_struct_0 @ (k1_pre_topc @ X10 @ X9)) = (X9))
% 0.46/0.69          | ~ (l1_pre_topc @ X10))),
% 0.46/0.69      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.46/0.69  thf('29', plain,
% 0.46/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.69        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.69  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('31', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_C)) = (sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['29', '30'])).
% 0.46/0.69  thf('32', plain,
% 0.46/0.69      ((m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69        (k1_zfmisc_1 @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['26', '31'])).
% 0.46/0.69  thf(t3_subset, axiom,
% 0.46/0.69    (![A:$i,B:$i]:
% 0.46/0.69     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.69  thf('33', plain,
% 0.46/0.69      (![X6 : $i, X7 : $i]:
% 0.46/0.69         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.69  thf('34', plain,
% 0.46/0.69      ((r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.46/0.69      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.69  thf('35', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.46/0.69           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.46/0.69          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.46/0.69      inference('split', [status(esa)], ['6'])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('39', plain,
% 0.46/0.69      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.69          | ~ (v2_tex_2 @ X14 @ X15)
% 0.46/0.69          | ~ (r1_tarski @ X16 @ X14)
% 0.46/0.69          | (v2_tex_2 @ X16 @ X15)
% 0.46/0.69          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.46/0.69          | ~ (l1_pre_topc @ X15))),
% 0.46/0.69      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.46/0.69  thf('40', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ sk_A)
% 0.46/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.69          | (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.69          | ~ (r1_tarski @ X0 @ sk_C)
% 0.46/0.69          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.46/0.69  thf('41', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('42', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.69          | (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.69          | ~ (r1_tarski @ X0 @ sk_C)
% 0.46/0.69          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 0.46/0.69      inference('demod', [status(thm)], ['40', '41'])).
% 0.46/0.69  thf('43', plain,
% 0.46/0.69      ((![X0 : $i]:
% 0.46/0.69          (~ (r1_tarski @ X0 @ sk_C)
% 0.46/0.69           | (v2_tex_2 @ X0 @ sk_A)
% 0.46/0.69           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.46/0.69         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['37', '42'])).
% 0.46/0.69  thf('44', plain,
% 0.46/0.69      ((![X0 : $i]:
% 0.46/0.69          ((v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ sk_A)
% 0.46/0.69           | ~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 0.46/0.69                sk_C)))
% 0.46/0.69         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['36', '43'])).
% 0.46/0.69  thf('45', plain,
% 0.46/0.69      (((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69            sk_C)
% 0.46/0.69         | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B) @ 
% 0.46/0.69            sk_A)))
% 0.46/0.69         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['35', '44'])).
% 0.46/0.69  thf('46', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.46/0.69           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.69  thf('47', plain,
% 0.46/0.69      (((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69            sk_C)
% 0.46/0.69         | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69            sk_A)))
% 0.46/0.69         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.46/0.69      inference('demod', [status(thm)], ['45', '46'])).
% 0.46/0.69  thf('48', plain,
% 0.46/0.69      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('49', plain,
% 0.46/0.69      ((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69           sk_C))
% 0.46/0.69         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 0.46/0.69      inference('clc', [status(thm)], ['47', '48'])).
% 0.46/0.69  thf('50', plain, (~ ((v2_tex_2 @ sk_C @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['34', '49'])).
% 0.46/0.69  thf('51', plain, (((v2_tex_2 @ sk_B @ sk_A)) | ((v2_tex_2 @ sk_C @ sk_A))),
% 0.46/0.69      inference('split', [status(esa)], ['6'])).
% 0.46/0.69  thf('52', plain, (((v2_tex_2 @ sk_B @ sk_A))),
% 0.46/0.69      inference('sat_resolution*', [status(thm)], ['50', '51'])).
% 0.46/0.69  thf('53', plain,
% 0.46/0.69      (~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.46/0.69      inference('simpl_trail', [status(thm)], ['19', '52'])).
% 0.46/0.69  thf('54', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('55', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('56', plain,
% 0.46/0.69      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.69          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ X12) @ X11 @ X13) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ X12 @ X13))))
% 0.46/0.69          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.46/0.69          | ~ (l1_pre_topc @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [t38_tops_2])).
% 0.46/0.69  thf('57', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (l1_pre_topc @ sk_A)
% 0.46/0.69          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.69          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.69  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('59', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.46/0.69          | (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.46/0.69             (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ X0)))))),
% 0.46/0.69      inference('demod', [status(thm)], ['57', '58'])).
% 0.46/0.69  thf('60', plain,
% 0.46/0.69      ((m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B) @ 
% 0.46/0.69        (k1_zfmisc_1 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.46/0.69      inference('sup-', [status(thm)], ['54', '59'])).
% 0.46/0.69  thf('61', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 0.46/0.69           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.69  thf('62', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('63', plain,
% 0.46/0.69      (![X9 : $i, X10 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.46/0.69          | ((u1_struct_0 @ (k1_pre_topc @ X10 @ X9)) = (X9))
% 0.46/0.69          | ~ (l1_pre_topc @ X10))),
% 0.46/0.69      inference('cnf', [status(esa)], [t29_pre_topc])).
% 0.46/0.69  thf('64', plain,
% 0.46/0.69      ((~ (l1_pre_topc @ sk_A)
% 0.46/0.69        | ((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.69  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('66', plain, (((u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.69  thf('67', plain,
% 0.46/0.69      ((m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69        (k1_zfmisc_1 @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['60', '61', '66'])).
% 0.46/0.69  thf('68', plain,
% 0.46/0.69      (![X6 : $i, X7 : $i]:
% 0.46/0.69         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.69  thf('69', plain,
% 0.46/0.69      ((r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.46/0.69      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.69  thf('70', plain, ($false), inference('demod', [status(thm)], ['53', '69'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.56/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
