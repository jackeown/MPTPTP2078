%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dm0bRktGlB

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:14 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 266 expanded)
%              Number of leaves         :   22 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          : 1391 (3938 expanded)
%              Number of equality atoms :   41 (  68 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( v2_tex_2 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
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

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('22',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('25',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t41_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X17 @ ( k4_subset_1 @ X17 @ X18 @ X16 ) ) @ ( k3_subset_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t33_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) )
            = ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k3_subset_1 @ X14 @ ( k7_subset_1 @ X14 @ X15 @ X13 ) )
        = ( k4_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X15 ) @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t32_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( k7_subset_1 @ A @ B @ C )
            = ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k7_subset_1 @ X11 @ X12 @ X10 )
        = ( k9_subset_1 @ X11 @ X12 @ ( k3_subset_1 @ X11 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('40',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('44',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['33','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k9_subset_1 @ X0 @ X2 @ X1 )
        = ( k9_subset_1 @ X0 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('56',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['28','45','52','53','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('60',plain,
    ( ( v2_tex_2 @ sk_C @ sk_A )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v2_tex_2 @ X19 @ X20 )
      | ~ ( r1_tarski @ X21 @ X19 )
      | ( v2_tex_2 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C )
      | ~ ( v2_tex_2 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_C )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ sk_A )
        | ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) @ sk_C ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['59','66'])).

thf('68',plain,
    ( ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_B ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['58','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('70',plain,
    ( ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
      | ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
   <= ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['57','72'])).

thf('74',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('75',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['19','75'])).

thf('77',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('78',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('79',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X17 @ ( k4_subset_1 @ X17 @ X18 @ X16 ) ) @ ( k3_subset_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_subset_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    r1_tarski @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('84',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( ( k3_subset_1 @ X14 @ ( k7_subset_1 @ X14 @ X15 @ X13 ) )
        = ( k4_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X15 ) @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t33_subset_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
        = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('89',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ( ( k7_subset_1 @ X11 @ X12 @ X10 )
        = ( k9_subset_1 @ X11 @ X12 @ ( k3_subset_1 @ X11 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_subset_1])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
        = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['86','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) ) )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['48','51'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('97',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('98',plain,(
    r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['81','94','95','96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['76','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dm0bRktGlB
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 2.72/2.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.72/2.96  % Solved by: fo/fo7.sh
% 2.72/2.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.72/2.96  % done 1824 iterations in 2.502s
% 2.72/2.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.72/2.96  % SZS output start Refutation
% 2.72/2.96  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 2.72/2.96  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.72/2.96  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 2.72/2.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 2.72/2.96  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.72/2.96  thf(sk_B_type, type, sk_B: $i).
% 2.72/2.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.72/2.96  thf(sk_A_type, type, sk_A: $i).
% 2.72/2.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.72/2.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.72/2.96  thf(sk_C_type, type, sk_C: $i).
% 2.72/2.96  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 2.72/2.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.72/2.96  thf(t29_tex_2, conjecture,
% 2.72/2.96    (![A:$i]:
% 2.72/2.96     ( ( l1_pre_topc @ A ) =>
% 2.72/2.96       ( ![B:$i]:
% 2.72/2.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.72/2.96           ( ![C:$i]:
% 2.72/2.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.72/2.96               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 2.72/2.96                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 2.72/2.96  thf(zf_stmt_0, negated_conjecture,
% 2.72/2.96    (~( ![A:$i]:
% 2.72/2.96        ( ( l1_pre_topc @ A ) =>
% 2.72/2.96          ( ![B:$i]:
% 2.72/2.96            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.72/2.96              ( ![C:$i]:
% 2.72/2.96                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.72/2.96                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 2.72/2.96                    ( v2_tex_2 @
% 2.72/2.96                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 2.72/2.96    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 2.72/2.96  thf('0', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf(commutativity_k9_subset_1, axiom,
% 2.72/2.96    (![A:$i,B:$i,C:$i]:
% 2.72/2.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 2.72/2.96  thf('1', plain,
% 2.72/2.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.96         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 2.72/2.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 2.72/2.96      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 2.72/2.96  thf('2', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.72/2.96      inference('sup-', [status(thm)], ['0', '1'])).
% 2.72/2.96  thf('3', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf(dt_k9_subset_1, axiom,
% 2.72/2.96    (![A:$i,B:$i,C:$i]:
% 2.72/2.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.72/2.96  thf('4', plain,
% 2.72/2.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 2.72/2.96         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 2.72/2.96          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 2.72/2.96      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 2.72/2.96  thf('5', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 2.72/2.96          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['3', '4'])).
% 2.72/2.96  thf('6', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C @ sk_A))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('7', plain, (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 2.72/2.96      inference('split', [status(esa)], ['6'])).
% 2.72/2.96  thf('8', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf(t28_tex_2, axiom,
% 2.72/2.96    (![A:$i]:
% 2.72/2.96     ( ( l1_pre_topc @ A ) =>
% 2.72/2.96       ( ![B:$i]:
% 2.72/2.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.72/2.96           ( ![C:$i]:
% 2.72/2.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.72/2.96               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 2.72/2.96                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 2.72/2.96  thf('9', plain,
% 2.72/2.96      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.72/2.96          | ~ (v2_tex_2 @ X19 @ X20)
% 2.72/2.96          | ~ (r1_tarski @ X21 @ X19)
% 2.72/2.96          | (v2_tex_2 @ X21 @ X20)
% 2.72/2.96          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.72/2.96          | ~ (l1_pre_topc @ X20))),
% 2.72/2.96      inference('cnf', [status(esa)], [t28_tex_2])).
% 2.72/2.96  thf('10', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (l1_pre_topc @ sk_A)
% 2.72/2.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | (v2_tex_2 @ X0 @ sk_A)
% 2.72/2.96          | ~ (r1_tarski @ X0 @ sk_B)
% 2.72/2.96          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 2.72/2.96      inference('sup-', [status(thm)], ['8', '9'])).
% 2.72/2.96  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('12', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | (v2_tex_2 @ X0 @ sk_A)
% 2.72/2.96          | ~ (r1_tarski @ X0 @ sk_B)
% 2.72/2.96          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 2.72/2.96      inference('demod', [status(thm)], ['10', '11'])).
% 2.72/2.96  thf('13', plain,
% 2.72/2.96      ((![X0 : $i]:
% 2.72/2.96          (~ (r1_tarski @ X0 @ sk_B)
% 2.72/2.96           | (v2_tex_2 @ X0 @ sk_A)
% 2.72/2.96           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 2.72/2.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['7', '12'])).
% 2.72/2.96  thf('14', plain,
% 2.72/2.96      ((![X0 : $i]:
% 2.72/2.96          ((v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ sk_A)
% 2.72/2.96           | ~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 2.72/2.96                sk_B)))
% 2.72/2.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['5', '13'])).
% 2.72/2.96  thf('15', plain,
% 2.72/2.96      (((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.72/2.96            sk_B)
% 2.72/2.96         | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B) @ 
% 2.72/2.96            sk_A)))
% 2.72/2.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['2', '14'])).
% 2.72/2.96  thf('16', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.72/2.96      inference('sup-', [status(thm)], ['0', '1'])).
% 2.72/2.96  thf('17', plain,
% 2.72/2.96      (((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.72/2.96            sk_B)
% 2.72/2.96         | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.72/2.96            sk_A)))
% 2.72/2.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 2.72/2.96      inference('demod', [status(thm)], ['15', '16'])).
% 2.72/2.96  thf('18', plain,
% 2.72/2.96      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('19', plain,
% 2.72/2.96      ((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.72/2.96           sk_B))
% 2.72/2.96         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 2.72/2.96      inference('clc', [status(thm)], ['17', '18'])).
% 2.72/2.96  thf('20', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf(dt_k3_subset_1, axiom,
% 2.72/2.96    (![A:$i,B:$i]:
% 2.72/2.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 2.72/2.96  thf('21', plain,
% 2.72/2.96      (![X3 : $i, X4 : $i]:
% 2.72/2.96         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 2.72/2.96          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 2.72/2.96      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.72/2.96  thf('22', plain,
% 2.72/2.96      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.72/2.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['20', '21'])).
% 2.72/2.96  thf('23', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('24', plain,
% 2.72/2.96      (![X3 : $i, X4 : $i]:
% 2.72/2.96         ((m1_subset_1 @ (k3_subset_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3))
% 2.72/2.96          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 2.72/2.96      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 2.72/2.96  thf('25', plain,
% 2.72/2.96      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.72/2.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['23', '24'])).
% 2.72/2.96  thf(t41_subset_1, axiom,
% 2.72/2.96    (![A:$i,B:$i]:
% 2.72/2.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96       ( ![C:$i]:
% 2.72/2.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96           ( r1_tarski @
% 2.72/2.96             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 2.72/2.96             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 2.72/2.96  thf('26', plain,
% 2.72/2.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.72/2.96          | (r1_tarski @ 
% 2.72/2.96             (k3_subset_1 @ X17 @ (k4_subset_1 @ X17 @ X18 @ X16)) @ 
% 2.72/2.96             (k3_subset_1 @ X17 @ X18))
% 2.72/2.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 2.72/2.96      inference('cnf', [status(esa)], [t41_subset_1])).
% 2.72/2.96  thf('27', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | (r1_tarski @ 
% 2.72/2.96             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 2.72/2.96             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['25', '26'])).
% 2.72/2.96  thf('28', plain,
% 2.72/2.96      ((r1_tarski @ 
% 2.72/2.96        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.72/2.96          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))) @ 
% 2.72/2.96        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['22', '27'])).
% 2.72/2.96  thf('29', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('30', plain,
% 2.72/2.96      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.72/2.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['23', '24'])).
% 2.72/2.96  thf(t33_subset_1, axiom,
% 2.72/2.96    (![A:$i,B:$i]:
% 2.72/2.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96       ( ![C:$i]:
% 2.72/2.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96           ( ( k3_subset_1 @ A @ ( k7_subset_1 @ A @ B @ C ) ) =
% 2.72/2.96             ( k4_subset_1 @ A @ ( k3_subset_1 @ A @ B ) @ C ) ) ) ) ))).
% 2.72/2.96  thf('31', plain,
% 2.72/2.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 2.72/2.96          | ((k3_subset_1 @ X14 @ (k7_subset_1 @ X14 @ X15 @ X13))
% 2.72/2.96              = (k4_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X15) @ X13))
% 2.72/2.96          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 2.72/2.96      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.72/2.96  thf('32', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 2.72/2.96              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 2.72/2.96                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 2.72/2.96      inference('sup-', [status(thm)], ['30', '31'])).
% 2.72/2.96  thf('33', plain,
% 2.72/2.96      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.72/2.96          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 2.72/2.96         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.72/2.96            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['29', '32'])).
% 2.72/2.96  thf('34', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('35', plain,
% 2.72/2.96      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.72/2.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['23', '24'])).
% 2.72/2.96  thf(t32_subset_1, axiom,
% 2.72/2.96    (![A:$i,B:$i]:
% 2.72/2.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96       ( ![C:$i]:
% 2.72/2.96         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96           ( ( k7_subset_1 @ A @ B @ C ) =
% 2.72/2.96             ( k9_subset_1 @ A @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 2.72/2.96  thf('36', plain,
% 2.72/2.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 2.72/2.96          | ((k7_subset_1 @ X11 @ X12 @ X10)
% 2.72/2.96              = (k9_subset_1 @ X11 @ X12 @ (k3_subset_1 @ X11 @ X10)))
% 2.72/2.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 2.72/2.96      inference('cnf', [status(esa)], [t32_subset_1])).
% 2.72/2.96  thf('37', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.72/2.96              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 2.72/2.96      inference('sup-', [status(thm)], ['35', '36'])).
% 2.72/2.96  thf('38', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf(involutiveness_k3_subset_1, axiom,
% 2.72/2.96    (![A:$i,B:$i]:
% 2.72/2.96     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.72/2.96       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 2.72/2.96  thf('39', plain,
% 2.72/2.96      (![X8 : $i, X9 : $i]:
% 2.72/2.96         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 2.72/2.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 2.72/2.96      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.72/2.96  thf('40', plain,
% 2.72/2.96      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 2.72/2.96      inference('sup-', [status(thm)], ['38', '39'])).
% 2.72/2.96  thf('41', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.72/2.96              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))),
% 2.72/2.96      inference('demod', [status(thm)], ['37', '40'])).
% 2.72/2.96  thf('42', plain,
% 2.72/2.96      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.72/2.96         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B))),
% 2.72/2.96      inference('sup-', [status(thm)], ['34', '41'])).
% 2.72/2.96  thf('43', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.72/2.96      inference('sup-', [status(thm)], ['0', '1'])).
% 2.72/2.96  thf('44', plain,
% 2.72/2.96      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 2.72/2.96         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 2.72/2.96      inference('demod', [status(thm)], ['42', '43'])).
% 2.72/2.96  thf('45', plain,
% 2.72/2.96      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 2.72/2.96         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.72/2.96            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.72/2.96      inference('demod', [status(thm)], ['33', '44'])).
% 2.72/2.96  thf('46', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('47', plain,
% 2.72/2.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.72/2.96         (((k9_subset_1 @ X0 @ X2 @ X1) = (k9_subset_1 @ X0 @ X1 @ X2))
% 2.72/2.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 2.72/2.96      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 2.72/2.96  thf('48', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0))),
% 2.72/2.96      inference('sup-', [status(thm)], ['46', '47'])).
% 2.72/2.96  thf('49', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 2.72/2.96          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['3', '4'])).
% 2.72/2.96  thf('50', plain,
% 2.72/2.96      (![X8 : $i, X9 : $i]:
% 2.72/2.96         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 2.72/2.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 2.72/2.96      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.72/2.96  thf('51', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B)))
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B))),
% 2.72/2.96      inference('sup-', [status(thm)], ['49', '50'])).
% 2.72/2.96  thf('52', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)))
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B))),
% 2.72/2.96      inference('sup+', [status(thm)], ['48', '51'])).
% 2.72/2.96  thf('53', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.72/2.96      inference('sup-', [status(thm)], ['0', '1'])).
% 2.72/2.96  thf('54', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('55', plain,
% 2.72/2.96      (![X8 : $i, X9 : $i]:
% 2.72/2.96         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 2.72/2.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 2.72/2.96      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 2.72/2.96  thf('56', plain,
% 2.72/2.96      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 2.72/2.96      inference('sup-', [status(thm)], ['54', '55'])).
% 2.72/2.96  thf('57', plain,
% 2.72/2.96      ((r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 2.72/2.96      inference('demod', [status(thm)], ['28', '45', '52', '53', '56'])).
% 2.72/2.96  thf('58', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.72/2.96      inference('sup-', [status(thm)], ['0', '1'])).
% 2.72/2.96  thf('59', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (m1_subset_1 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 2.72/2.96          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['3', '4'])).
% 2.72/2.96  thf('60', plain,
% 2.72/2.96      (((v2_tex_2 @ sk_C @ sk_A)) <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 2.72/2.96      inference('split', [status(esa)], ['6'])).
% 2.72/2.96  thf('61', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('62', plain,
% 2.72/2.96      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.72/2.96          | ~ (v2_tex_2 @ X19 @ X20)
% 2.72/2.96          | ~ (r1_tarski @ X21 @ X19)
% 2.72/2.96          | (v2_tex_2 @ X21 @ X20)
% 2.72/2.96          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 2.72/2.96          | ~ (l1_pre_topc @ X20))),
% 2.72/2.96      inference('cnf', [status(esa)], [t28_tex_2])).
% 2.72/2.96  thf('63', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (l1_pre_topc @ sk_A)
% 2.72/2.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | (v2_tex_2 @ X0 @ sk_A)
% 2.72/2.96          | ~ (r1_tarski @ X0 @ sk_C)
% 2.72/2.96          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 2.72/2.96      inference('sup-', [status(thm)], ['61', '62'])).
% 2.72/2.96  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('65', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | (v2_tex_2 @ X0 @ sk_A)
% 2.72/2.96          | ~ (r1_tarski @ X0 @ sk_C)
% 2.72/2.96          | ~ (v2_tex_2 @ sk_C @ sk_A))),
% 2.72/2.96      inference('demod', [status(thm)], ['63', '64'])).
% 2.72/2.96  thf('66', plain,
% 2.72/2.96      ((![X0 : $i]:
% 2.72/2.96          (~ (r1_tarski @ X0 @ sk_C)
% 2.72/2.96           | (v2_tex_2 @ X0 @ sk_A)
% 2.72/2.96           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 2.72/2.96         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['60', '65'])).
% 2.72/2.96  thf('67', plain,
% 2.72/2.96      ((![X0 : $i]:
% 2.72/2.96          ((v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ sk_A)
% 2.72/2.96           | ~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B) @ 
% 2.72/2.96                sk_C)))
% 2.72/2.96         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['59', '66'])).
% 2.72/2.96  thf('68', plain,
% 2.72/2.96      (((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.72/2.96            sk_C)
% 2.72/2.96         | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_B) @ 
% 2.72/2.96            sk_A)))
% 2.72/2.96         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['58', '67'])).
% 2.72/2.96  thf('69', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.72/2.96      inference('sup-', [status(thm)], ['0', '1'])).
% 2.72/2.96  thf('70', plain,
% 2.72/2.96      (((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.72/2.96            sk_C)
% 2.72/2.96         | (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.72/2.96            sk_A)))
% 2.72/2.96         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 2.72/2.96      inference('demod', [status(thm)], ['68', '69'])).
% 2.72/2.96  thf('71', plain,
% 2.72/2.96      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_A)),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('72', plain,
% 2.72/2.96      ((~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ 
% 2.72/2.96           sk_C))
% 2.72/2.96         <= (((v2_tex_2 @ sk_C @ sk_A)))),
% 2.72/2.96      inference('clc', [status(thm)], ['70', '71'])).
% 2.72/2.96  thf('73', plain, (~ ((v2_tex_2 @ sk_C @ sk_A))),
% 2.72/2.96      inference('sup-', [status(thm)], ['57', '72'])).
% 2.72/2.96  thf('74', plain, (((v2_tex_2 @ sk_B @ sk_A)) | ((v2_tex_2 @ sk_C @ sk_A))),
% 2.72/2.96      inference('split', [status(esa)], ['6'])).
% 2.72/2.96  thf('75', plain, (((v2_tex_2 @ sk_B @ sk_A))),
% 2.72/2.96      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 2.72/2.96  thf('76', plain,
% 2.72/2.96      (~ (r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 2.72/2.96      inference('simpl_trail', [status(thm)], ['19', '75'])).
% 2.72/2.96  thf('77', plain,
% 2.72/2.96      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.72/2.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['23', '24'])).
% 2.72/2.96  thf('78', plain,
% 2.72/2.96      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.72/2.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['20', '21'])).
% 2.72/2.96  thf('79', plain,
% 2.72/2.96      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.72/2.96          | (r1_tarski @ 
% 2.72/2.96             (k3_subset_1 @ X17 @ (k4_subset_1 @ X17 @ X18 @ X16)) @ 
% 2.72/2.96             (k3_subset_1 @ X17 @ X18))
% 2.72/2.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 2.72/2.96      inference('cnf', [status(esa)], [t41_subset_1])).
% 2.72/2.96  thf('80', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | (r1_tarski @ 
% 2.72/2.96             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96              (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))) @ 
% 2.72/2.96             (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['78', '79'])).
% 2.72/2.96  thf('81', plain,
% 2.72/2.96      ((r1_tarski @ 
% 2.72/2.96        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.72/2.96          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))) @ 
% 2.72/2.96        (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['77', '80'])).
% 2.72/2.96  thf('82', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('83', plain,
% 2.72/2.96      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.72/2.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['20', '21'])).
% 2.72/2.96  thf('84', plain,
% 2.72/2.96      (![X13 : $i, X14 : $i, X15 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 2.72/2.96          | ((k3_subset_1 @ X14 @ (k7_subset_1 @ X14 @ X15 @ X13))
% 2.72/2.96              = (k4_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X15) @ X13))
% 2.72/2.96          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X14)))),
% 2.72/2.96      inference('cnf', [status(esa)], [t33_subset_1])).
% 2.72/2.96  thf('85', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96              (k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96               (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 2.72/2.96              = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ X0) @ 
% 2.72/2.96                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 2.72/2.96      inference('sup-', [status(thm)], ['83', '84'])).
% 2.72/2.96  thf('86', plain,
% 2.72/2.96      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.72/2.96          (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 2.72/2.96         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.72/2.96            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['82', '85'])).
% 2.72/2.96  thf('87', plain,
% 2.72/2.96      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.72/2.96  thf('88', plain,
% 2.72/2.96      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 2.72/2.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 2.72/2.96      inference('sup-', [status(thm)], ['20', '21'])).
% 2.72/2.96  thf('89', plain,
% 2.72/2.96      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 2.72/2.96          | ((k7_subset_1 @ X11 @ X12 @ X10)
% 2.72/2.96              = (k9_subset_1 @ X11 @ X12 @ (k3_subset_1 @ X11 @ X10)))
% 2.72/2.96          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X11)))),
% 2.72/2.96      inference('cnf', [status(esa)], [t32_subset_1])).
% 2.72/2.96  thf('90', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 2.72/2.96              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96                 (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96                  (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 2.72/2.96      inference('sup-', [status(thm)], ['88', '89'])).
% 2.72/2.96  thf('91', plain,
% 2.72/2.96      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)) = (sk_C))),
% 2.72/2.96      inference('sup-', [status(thm)], ['54', '55'])).
% 2.72/2.96  thf('92', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 2.72/2.96          | ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 2.72/2.96              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 2.72/2.96              = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)))),
% 2.72/2.96      inference('demod', [status(thm)], ['90', '91'])).
% 2.72/2.96  thf('93', plain,
% 2.72/2.96      (((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 2.72/2.96         = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))),
% 2.72/2.96      inference('sup-', [status(thm)], ['87', '92'])).
% 2.72/2.96  thf('94', plain,
% 2.72/2.96      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C))
% 2.72/2.96         = (k4_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 2.72/2.96            (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 2.72/2.96      inference('demod', [status(thm)], ['86', '93'])).
% 2.72/2.96  thf('95', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96           (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)))
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_B))),
% 2.72/2.96      inference('sup+', [status(thm)], ['48', '51'])).
% 2.72/2.96  thf('96', plain,
% 2.72/2.96      (![X0 : $i]:
% 2.72/2.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C)
% 2.72/2.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0))),
% 2.72/2.96      inference('sup-', [status(thm)], ['0', '1'])).
% 2.72/2.96  thf('97', plain,
% 2.72/2.96      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 2.72/2.96         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B)) = (sk_B))),
% 2.72/2.96      inference('sup-', [status(thm)], ['38', '39'])).
% 2.72/2.96  thf('98', plain,
% 2.72/2.96      ((r1_tarski @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 2.72/2.96      inference('demod', [status(thm)], ['81', '94', '95', '96', '97'])).
% 2.72/2.96  thf('99', plain, ($false), inference('demod', [status(thm)], ['76', '98'])).
% 2.72/2.96  
% 2.72/2.96  % SZS output end Refutation
% 2.72/2.96  
% 2.79/2.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
