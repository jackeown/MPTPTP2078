%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fRhK9oUShC

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:11 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  149 (1618 expanded)
%              Number of leaves         :   29 ( 470 expanded)
%              Depth                    :   22
%              Number of atoms          : 1379 (24911 expanded)
%              Number of equality atoms :   40 (1046 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(u1_pre_topc_type,type,(
    u1_pre_topc: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(g1_pre_topc_type,type,(
    g1_pre_topc: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t25_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                 => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                        = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                      & ( C = D )
                      & ( v2_tex_2 @ C @ A ) )
                   => ( v2_tex_2 @ D @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( l1_pre_topc @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) )
                          = ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) )
                        & ( C = D )
                        & ( v2_tex_2 @ C @ A ) )
                     => ( v2_tex_2 @ D @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ( m1_pre_topc @ X24 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf(t65_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( l1_pre_topc @ B )
         => ( ( m1_pre_topc @ A @ B )
          <=> ( m1_pre_topc @ A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_pre_topc @ X16 )
      | ~ ( m1_pre_topc @ X17 @ X16 )
      | ( m1_pre_topc @ X17 @ ( g1_pre_topc @ ( u1_struct_0 @ X16 ) @ ( u1_pre_topc @ X16 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t65_pre_topc])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) )
         => ( m1_pre_topc @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
      | ( m1_pre_topc @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_pre_topc @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['10','11'])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('14',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,
    ( ~ ( r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) )
    = ( g1_pre_topc @ ( u1_struct_0 @ sk_B ) @ ( u1_pre_topc @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ X0 @ ( g1_pre_topc @ ( u1_struct_0 @ X0 ) @ ( u1_pre_topc @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('23',plain,
    ( ( m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_B ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_pre_topc @ sk_B @ ( g1_pre_topc @ ( u1_struct_0 @ sk_A ) @ ( u1_pre_topc @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_pre_topc @ X14 @ ( g1_pre_topc @ ( u1_struct_0 @ X15 ) @ ( u1_pre_topc @ X15 ) ) )
      | ( m1_pre_topc @ X14 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[t59_pre_topc])).

thf('27',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_pre_topc @ X22 @ X23 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf(d5_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ~ ( ( r1_tarski @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('37',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    ~ ( v2_tex_2 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ ( sk_D @ X27 @ X25 @ X26 ) )
        = X27 )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('52',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k9_subset_1 @ X3 @ X5 @ X4 )
        = ( k9_subset_1 @ X3 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('55',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( ( k3_xboole_0 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_C_1 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['49','50','57','58'])).

thf('60',plain,
    ( ( ( k3_xboole_0 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_C_1 )
      = ( sk_C @ sk_C_1 @ sk_B ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('63',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( sk_C @ X25 @ X26 ) @ X25 )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( r1_tarski @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf('68',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('69',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k3_xboole_0 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_C_1 )
    = ( sk_C @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['60','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('73',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_pre_topc @ X28 @ X26 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ X28 )
       != ( sk_C @ X25 @ X26 ) )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_B ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('77',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ X1 )
       != ( sk_C @ X0 @ sk_B ) )
      | ~ ( v3_pre_topc @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( v2_tex_2 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_C_1 )
      = ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_B )
      | ( ( k3_xboole_0 @ X0 @ sk_C_1 )
       != ( sk_C @ sk_C_1 @ sk_B ) )
      | ( v2_tex_2 @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( sk_C @ sk_C_1 @ sk_B )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['70','81'])).

thf('83',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('84',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ( m1_subset_1 @ ( sk_D @ X27 @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['67','68'])).

thf('92',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( sk_C @ sk_C_1 @ sk_B )
     != ( sk_C @ sk_C_1 @ sk_B ) )
    | ( v2_tex_2 @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['82','92'])).

thf('94',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ~ ( v2_tex_2 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('96',plain,(
    ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('98',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','35'])).

thf(t33_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_pre_topc @ C @ A )
             => ( ( v3_pre_topc @ B @ A )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                   => ( ( D = B )
                     => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) )).

thf('100',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( v3_pre_topc @ X20 @ X21 )
      | ( X20 != X18 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t33_tops_2])).

thf('101',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X19 )
      | ~ ( m1_pre_topc @ X21 @ X19 )
      | ( v3_pre_topc @ X18 @ X21 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( v3_pre_topc @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v3_pre_topc @ X0 @ X1 )
      | ( v3_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_B @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
      | ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','102'])).

thf('104',plain,
    ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B )
    | ~ ( m1_pre_topc @ sk_B @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['97','103'])).

thf('105',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['42','45'])).

thf('106',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v2_tex_2 @ X25 @ X26 )
      | ( v3_pre_topc @ ( sk_D @ X27 @ X25 @ X26 ) @ X26 )
      | ~ ( r1_tarski @ X27 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ( v3_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','109','110'])).

thf('112',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['105','111'])).

thf('113',plain,(
    r1_tarski @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['67','68'])).

thf('114',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['27','28'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['104','114','115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['96','117'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fRhK9oUShC
% 0.16/0.37  % Computer   : n021.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 16:33:19 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 746 iterations in 0.480s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.77/0.96  thf(u1_pre_topc_type, type, u1_pre_topc: $i > $i).
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.96  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.77/0.96  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(g1_pre_topc_type, type, g1_pre_topc: $i > $i > $i).
% 0.77/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.77/0.96  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.77/0.96  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.96  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.77/0.96  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.77/0.96  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.77/0.96  thf(t25_tex_2, conjecture,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( l1_pre_topc @ B ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96               ( ![D:$i]:
% 0.77/0.96                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.77/0.96                   ( ( ( ( g1_pre_topc @
% 0.77/0.96                           ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.77/0.96                         ( g1_pre_topc @
% 0.77/0.96                           ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.77/0.96                       ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.77/0.96                     ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i]:
% 0.77/0.96        ( ( l1_pre_topc @ A ) =>
% 0.77/0.96          ( ![B:$i]:
% 0.77/0.96            ( ( l1_pre_topc @ B ) =>
% 0.77/0.96              ( ![C:$i]:
% 0.77/0.96                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96                  ( ![D:$i]:
% 0.77/0.96                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.77/0.96                      ( ( ( ( g1_pre_topc @
% 0.77/0.96                              ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) =
% 0.77/0.96                            ( g1_pre_topc @
% 0.77/0.96                              ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) & 
% 0.77/0.96                          ( ( C ) = ( D ) ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.77/0.96                        ( v2_tex_2 @ D @ B ) ) ) ) ) ) ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t25_tex_2])).
% 0.77/0.96  thf('0', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t2_tsep_1, axiom,
% 0.77/0.96    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      (![X24 : $i]: ((m1_pre_topc @ X24 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.77/0.96      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.77/0.96  thf(t65_pre_topc, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( l1_pre_topc @ B ) =>
% 0.77/0.96           ( ( m1_pre_topc @ A @ B ) <=>
% 0.77/0.96             ( m1_pre_topc @
% 0.77/0.96               A @ ( g1_pre_topc @ ( u1_struct_0 @ B ) @ ( u1_pre_topc @ B ) ) ) ) ) ) ))).
% 0.77/0.96  thf('2', plain,
% 0.77/0.96      (![X16 : $i, X17 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ X16)
% 0.77/0.96          | ~ (m1_pre_topc @ X17 @ X16)
% 0.77/0.96          | (m1_pre_topc @ X17 @ 
% 0.77/0.96             (g1_pre_topc @ (u1_struct_0 @ X16) @ (u1_pre_topc @ X16)))
% 0.77/0.96          | ~ (l1_pre_topc @ X17))),
% 0.77/0.96      inference('cnf', [status(esa)], [t65_pre_topc])).
% 0.77/0.96  thf('3', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ X0)
% 0.77/0.96          | ~ (l1_pre_topc @ X0)
% 0.77/0.96          | (m1_pre_topc @ X0 @ 
% 0.77/0.96             (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.77/0.96          | ~ (l1_pre_topc @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['1', '2'])).
% 0.77/0.96  thf('4', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((m1_pre_topc @ X0 @ 
% 0.77/0.96           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.77/0.96          | ~ (l1_pre_topc @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['3'])).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.77/0.96         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t59_pre_topc, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_pre_topc @
% 0.77/0.96             B @ ( g1_pre_topc @ ( u1_struct_0 @ A ) @ ( u1_pre_topc @ A ) ) ) =>
% 0.77/0.96           ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.77/0.96  thf('6', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X14 @ 
% 0.77/0.96             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.77/0.96          | (m1_pre_topc @ X14 @ X15)
% 0.77/0.96          | ~ (l1_pre_topc @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X0 @ 
% 0.77/0.96             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.96          | ~ (l1_pre_topc @ sk_B)
% 0.77/0.96          | (m1_pre_topc @ X0 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['5', '6'])).
% 0.77/0.96  thf('8', plain, ((l1_pre_topc @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('9', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X0 @ 
% 0.77/0.96             (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.96          | (m1_pre_topc @ X0 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('10', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_A @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['4', '9'])).
% 0.77/0.96  thf('11', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('12', plain, ((m1_pre_topc @ sk_A @ sk_B)),
% 0.77/0.96      inference('demod', [status(thm)], ['10', '11'])).
% 0.77/0.96  thf(t1_tsep_1, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_pre_topc @ B @ A ) =>
% 0.77/0.96           ( m1_subset_1 @
% 0.77/0.96             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      (![X22 : $i, X23 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X22 @ X23)
% 0.77/0.96          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.77/0.96          | ~ (l1_pre_topc @ X23))),
% 0.77/0.96      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      ((~ (l1_pre_topc @ sk_B)
% 0.77/0.96        | (m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96           (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.96  thf('15', plain, ((l1_pre_topc @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('16', plain,
% 0.77/0.96      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_B)))),
% 0.77/0.96      inference('demod', [status(thm)], ['14', '15'])).
% 0.77/0.96  thf(t3_subset, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.77/0.96  thf('17', plain,
% 0.77/0.96      (![X9 : $i, X10 : $i]:
% 0.77/0.96         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.96  thf('18', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['16', '17'])).
% 0.77/0.96  thf(d10_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.77/0.96  thf('19', plain,
% 0.77/0.96      (![X0 : $i, X2 : $i]:
% 0.77/0.96         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.77/0.96      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.77/0.96  thf('20', plain,
% 0.77/0.96      ((~ (r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))
% 0.77/0.96        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['18', '19'])).
% 0.77/0.96  thf('21', plain,
% 0.77/0.96      (((g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A))
% 0.77/0.96         = (g1_pre_topc @ (u1_struct_0 @ sk_B) @ (u1_pre_topc @ sk_B)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((m1_pre_topc @ X0 @ 
% 0.77/0.96           (g1_pre_topc @ (u1_struct_0 @ X0) @ (u1_pre_topc @ X0)))
% 0.77/0.96          | ~ (l1_pre_topc @ X0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['3'])).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      (((m1_pre_topc @ sk_B @ 
% 0.77/0.96         (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))
% 0.77/0.96        | ~ (l1_pre_topc @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['21', '22'])).
% 0.77/0.96  thf('24', plain, ((l1_pre_topc @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('25', plain,
% 0.77/0.96      ((m1_pre_topc @ sk_B @ 
% 0.77/0.96        (g1_pre_topc @ (u1_struct_0 @ sk_A) @ (u1_pre_topc @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['23', '24'])).
% 0.77/0.96  thf('26', plain,
% 0.77/0.96      (![X14 : $i, X15 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X14 @ 
% 0.77/0.96             (g1_pre_topc @ (u1_struct_0 @ X15) @ (u1_pre_topc @ X15)))
% 0.77/0.96          | (m1_pre_topc @ X14 @ X15)
% 0.77/0.96          | ~ (l1_pre_topc @ X15))),
% 0.77/0.96      inference('cnf', [status(esa)], [t59_pre_topc])).
% 0.77/0.96  thf('27', plain, ((~ (l1_pre_topc @ sk_A) | (m1_pre_topc @ sk_B @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['25', '26'])).
% 0.77/0.96  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('29', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.77/0.96      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.96  thf('30', plain,
% 0.77/0.96      (![X22 : $i, X23 : $i]:
% 0.77/0.96         (~ (m1_pre_topc @ X22 @ X23)
% 0.77/0.96          | (m1_subset_1 @ (u1_struct_0 @ X22) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.77/0.96          | ~ (l1_pre_topc @ X23))),
% 0.77/0.96      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      ((~ (l1_pre_topc @ sk_A)
% 0.77/0.96        | (m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.77/0.96           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['29', '30'])).
% 0.77/0.96  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      ((m1_subset_1 @ (u1_struct_0 @ sk_B) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['31', '32'])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (![X9 : $i, X10 : $i]:
% 0.77/0.96         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t3_subset])).
% 0.77/0.96  thf('35', plain, ((r1_tarski @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['33', '34'])).
% 0.77/0.96  thf('36', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '35'])).
% 0.77/0.96  thf(d5_tex_2, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ( v2_tex_2 @ B @ A ) <=>
% 0.77/0.96             ( ![C:$i]:
% 0.77/0.96               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.77/0.96                      ( ![D:$i]:
% 0.77/0.96                        ( ( m1_subset_1 @
% 0.77/0.96                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.77/0.96                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.77/0.96                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X25 : $i, X26 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | (m1_subset_1 @ (sk_C @ X25 @ X26) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | (v2_tex_2 @ X25 @ X26)
% 0.77/0.96          | ~ (l1_pre_topc @ X26))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (l1_pre_topc @ sk_B)
% 0.77/0.96          | (v2_tex_2 @ X0 @ sk_B)
% 0.77/0.96          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['36', '37'])).
% 0.77/0.96  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('40', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '35'])).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | (v2_tex_2 @ X0 @ sk_B)
% 0.77/0.96          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.96      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.77/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['0', '41'])).
% 0.77/0.96  thf('43', plain, (~ (v2_tex_2 @ sk_D_1 @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('44', plain, (((sk_C_1) = (sk_D_1))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('45', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.77/0.96      inference('demod', [status(thm)], ['43', '44'])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('clc', [status(thm)], ['42', '45'])).
% 0.77/0.96  thf('47', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (v2_tex_2 @ X25 @ X26)
% 0.77/0.96          | ((k9_subset_1 @ (u1_struct_0 @ X26) @ X25 @ 
% 0.77/0.96              (sk_D @ X27 @ X25 @ X26)) = (X27))
% 0.77/0.96          | ~ (r1_tarski @ X27 @ X25)
% 0.77/0.96          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (l1_pre_topc @ X26))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ sk_A)
% 0.77/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.77/0.96          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ 
% 0.77/0.96              (sk_D @ X0 @ sk_C_1 @ sk_A)) = (X0))
% 0.77/0.96          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['47', '48'])).
% 0.77/0.96  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(commutativity_k9_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.77/0.96  thf('52', plain,
% 0.77/0.96      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.77/0.96         (((k9_subset_1 @ X3 @ X5 @ X4) = (k9_subset_1 @ X3 @ X4 @ X5))
% 0.77/0.96          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X3)))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.77/0.96  thf('53', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.77/0.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['51', '52'])).
% 0.77/0.96  thf('54', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(redefinition_k9_subset_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.77/0.96       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.77/0.96  thf('55', plain,
% 0.77/0.96      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.77/0.96         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.77/0.96          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.77/0.96      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.77/0.96  thf('56', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.77/0.96           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['54', '55'])).
% 0.77/0.96  thf('57', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X0 @ sk_C_1)
% 0.77/0.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['53', '56'])).
% 0.77/0.96  thf('58', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('59', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.77/0.96          | ((k3_xboole_0 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_C_1) = (X0)))),
% 0.77/0.96      inference('demod', [status(thm)], ['49', '50', '57', '58'])).
% 0.77/0.96  thf('60', plain,
% 0.77/0.96      ((((k3_xboole_0 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96          sk_C_1) = (sk_C @ sk_C_1 @ sk_B))
% 0.77/0.96        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['46', '59'])).
% 0.77/0.96  thf('61', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('62', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '35'])).
% 0.77/0.96  thf('63', plain,
% 0.77/0.96      (![X25 : $i, X26 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | (r1_tarski @ (sk_C @ X25 @ X26) @ X25)
% 0.77/0.96          | (v2_tex_2 @ X25 @ X26)
% 0.77/0.96          | ~ (l1_pre_topc @ X26))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.96  thf('64', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (l1_pre_topc @ sk_B)
% 0.77/0.96          | (v2_tex_2 @ X0 @ sk_B)
% 0.77/0.96          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['62', '63'])).
% 0.77/0.96  thf('65', plain, ((l1_pre_topc @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('66', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | (v2_tex_2 @ X0 @ sk_B)
% 0.77/0.96          | (r1_tarski @ (sk_C @ X0 @ sk_B) @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['64', '65'])).
% 0.77/0.96  thf('67', plain,
% 0.77/0.96      (((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)
% 0.77/0.96        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['61', '66'])).
% 0.77/0.96  thf('68', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.77/0.96      inference('demod', [status(thm)], ['43', '44'])).
% 0.77/0.96  thf('69', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.77/0.96      inference('clc', [status(thm)], ['67', '68'])).
% 0.77/0.96  thf('70', plain,
% 0.77/0.96      (((k3_xboole_0 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_C_1)
% 0.77/0.96         = (sk_C @ sk_C_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['60', '69'])).
% 0.77/0.96  thf('71', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('72', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '35'])).
% 0.77/0.96  thf('73', plain,
% 0.77/0.96      (![X25 : $i, X26 : $i, X28 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (v3_pre_topc @ X28 @ X26)
% 0.77/0.96          | ((k9_subset_1 @ (u1_struct_0 @ X26) @ X25 @ X28)
% 0.77/0.96              != (sk_C @ X25 @ X26))
% 0.77/0.96          | (v2_tex_2 @ X25 @ X26)
% 0.77/0.96          | ~ (l1_pre_topc @ X26))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.96  thf('74', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (l1_pre_topc @ sk_B)
% 0.77/0.96          | (v2_tex_2 @ X0 @ sk_B)
% 0.77/0.96          | ((k9_subset_1 @ (u1_struct_0 @ sk_B) @ X0 @ X1)
% 0.77/0.96              != (sk_C @ X0 @ sk_B))
% 0.77/0.96          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.77/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_B))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['72', '73'])).
% 0.77/0.96  thf('75', plain, ((l1_pre_topc @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('76', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '35'])).
% 0.77/0.96  thf('77', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '35'])).
% 0.77/0.96  thf('78', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | (v2_tex_2 @ X0 @ sk_B)
% 0.77/0.96          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ X1)
% 0.77/0.96              != (sk_C @ X0 @ sk_B))
% 0.77/0.96          | ~ (v3_pre_topc @ X1 @ sk_B)
% 0.77/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.96      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.77/0.96  thf('79', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.77/0.96          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0)
% 0.77/0.96              != (sk_C @ sk_C_1 @ sk_B))
% 0.77/0.96          | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.77/0.96      inference('sup-', [status(thm)], ['71', '78'])).
% 0.77/0.96  thf('80', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ X0 @ sk_C_1)
% 0.77/0.96           = (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C_1 @ X0))),
% 0.77/0.96      inference('demod', [status(thm)], ['53', '56'])).
% 0.77/0.96  thf('81', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (v3_pre_topc @ X0 @ sk_B)
% 0.77/0.96          | ((k3_xboole_0 @ X0 @ sk_C_1) != (sk_C @ sk_C_1 @ sk_B))
% 0.77/0.96          | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['79', '80'])).
% 0.77/0.96  thf('82', plain,
% 0.77/0.96      ((((sk_C @ sk_C_1 @ sk_B) != (sk_C @ sk_C_1 @ sk_B))
% 0.77/0.96        | (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.77/0.96        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96             sk_B)
% 0.77/0.96        | ~ (m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['70', '81'])).
% 0.77/0.96  thf('83', plain,
% 0.77/0.96      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('clc', [status(thm)], ['42', '45'])).
% 0.77/0.96  thf('84', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('85', plain,
% 0.77/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (v2_tex_2 @ X25 @ X26)
% 0.77/0.96          | (m1_subset_1 @ (sk_D @ X27 @ X25 @ X26) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (r1_tarski @ X27 @ X25)
% 0.77/0.96          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (l1_pre_topc @ X26))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.96  thf('86', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ sk_A)
% 0.77/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.77/0.96          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['84', '85'])).
% 0.77/0.96  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('88', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('89', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.77/0.96          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 0.77/0.96             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.96      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.77/0.96  thf('90', plain,
% 0.77/0.96      (((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['83', '89'])).
% 0.77/0.96  thf('91', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.77/0.96      inference('clc', [status(thm)], ['67', '68'])).
% 0.77/0.96  thf('92', plain,
% 0.77/0.96      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('93', plain,
% 0.77/0.96      ((((sk_C @ sk_C_1 @ sk_B) != (sk_C @ sk_C_1 @ sk_B))
% 0.77/0.96        | (v2_tex_2 @ sk_C_1 @ sk_B)
% 0.77/0.96        | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96             sk_B))),
% 0.77/0.96      inference('demod', [status(thm)], ['82', '92'])).
% 0.77/0.96  thf('94', plain,
% 0.77/0.96      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)
% 0.77/0.96        | (v2_tex_2 @ sk_C_1 @ sk_B))),
% 0.77/0.96      inference('simplify', [status(thm)], ['93'])).
% 0.77/0.96  thf('95', plain, (~ (v2_tex_2 @ sk_C_1 @ sk_B)),
% 0.77/0.96      inference('demod', [status(thm)], ['43', '44'])).
% 0.77/0.96  thf('96', plain,
% 0.77/0.96      (~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.77/0.96      inference('clc', [status(thm)], ['94', '95'])).
% 0.77/0.96  thf('97', plain,
% 0.77/0.96      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('98', plain,
% 0.77/0.96      ((m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('demod', [status(thm)], ['90', '91'])).
% 0.77/0.96  thf('99', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['20', '35'])).
% 0.77/0.96  thf(t33_tops_2, axiom,
% 0.77/0.96    (![A:$i]:
% 0.77/0.96     ( ( l1_pre_topc @ A ) =>
% 0.77/0.96       ( ![B:$i]:
% 0.77/0.96         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.96           ( ![C:$i]:
% 0.77/0.96             ( ( m1_pre_topc @ C @ A ) =>
% 0.77/0.96               ( ( v3_pre_topc @ B @ A ) =>
% 0.77/0.96                 ( ![D:$i]:
% 0.77/0.96                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.77/0.96                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.77/0.96  thf('100', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.77/0.96          | ~ (v3_pre_topc @ X18 @ X19)
% 0.77/0.96          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.77/0.96          | (v3_pre_topc @ X20 @ X21)
% 0.77/0.96          | ((X20) != (X18))
% 0.77/0.96          | ~ (m1_pre_topc @ X21 @ X19)
% 0.77/0.96          | ~ (l1_pre_topc @ X19))),
% 0.77/0.96      inference('cnf', [status(esa)], [t33_tops_2])).
% 0.77/0.96  thf('101', plain,
% 0.77/0.96      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ X19)
% 0.77/0.96          | ~ (m1_pre_topc @ X21 @ X19)
% 0.77/0.96          | (v3_pre_topc @ X18 @ X21)
% 0.77/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 0.77/0.96          | ~ (v3_pre_topc @ X18 @ X19)
% 0.77/0.96          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 0.77/0.96      inference('simplify', [status(thm)], ['100'])).
% 0.77/0.96  thf('102', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.77/0.96          | ~ (v3_pre_topc @ X0 @ X1)
% 0.77/0.96          | (v3_pre_topc @ X0 @ sk_B)
% 0.77/0.96          | ~ (m1_pre_topc @ sk_B @ X1)
% 0.77/0.96          | ~ (l1_pre_topc @ X1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['99', '101'])).
% 0.77/0.96  thf('103', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ X0)
% 0.77/0.96          | ~ (m1_pre_topc @ sk_B @ X0)
% 0.77/0.96          | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96             sk_B)
% 0.77/0.96          | ~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96               X0)
% 0.77/0.96          | ~ (m1_subset_1 @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ 
% 0.77/0.96               (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.77/0.96      inference('sup-', [status(thm)], ['98', '102'])).
% 0.77/0.96  thf('104', plain,
% 0.77/0.96      ((~ (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.77/0.96        | (v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)
% 0.77/0.96        | ~ (m1_pre_topc @ sk_B @ sk_A)
% 0.77/0.96        | ~ (l1_pre_topc @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['97', '103'])).
% 0.77/0.96  thf('105', plain,
% 0.77/0.96      ((m1_subset_1 @ (sk_C @ sk_C_1 @ sk_B) @ 
% 0.77/0.96        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('clc', [status(thm)], ['42', '45'])).
% 0.77/0.96  thf('106', plain,
% 0.77/0.96      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('107', plain,
% 0.77/0.96      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (v2_tex_2 @ X25 @ X26)
% 0.77/0.96          | (v3_pre_topc @ (sk_D @ X27 @ X25 @ X26) @ X26)
% 0.77/0.96          | ~ (r1_tarski @ X27 @ X25)
% 0.77/0.96          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.77/0.96          | ~ (l1_pre_topc @ X26))),
% 0.77/0.96      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.77/0.96  thf('108', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (l1_pre_topc @ sk_A)
% 0.77/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.77/0.96          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A)
% 0.77/0.96          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['106', '107'])).
% 0.77/0.96  thf('109', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('110', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('111', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.77/0.96          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.77/0.96          | (v3_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['108', '109', '110'])).
% 0.77/0.96  thf('112', plain,
% 0.77/0.96      (((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)
% 0.77/0.96        | ~ (r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['105', '111'])).
% 0.77/0.96  thf('113', plain, ((r1_tarski @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1)),
% 0.77/0.96      inference('clc', [status(thm)], ['67', '68'])).
% 0.77/0.96  thf('114', plain,
% 0.77/0.96      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_A)),
% 0.77/0.96      inference('demod', [status(thm)], ['112', '113'])).
% 0.77/0.96  thf('115', plain, ((m1_pre_topc @ sk_B @ sk_A)),
% 0.77/0.96      inference('demod', [status(thm)], ['27', '28'])).
% 0.77/0.96  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('117', plain,
% 0.77/0.96      ((v3_pre_topc @ (sk_D @ (sk_C @ sk_C_1 @ sk_B) @ sk_C_1 @ sk_A) @ sk_B)),
% 0.77/0.96      inference('demod', [status(thm)], ['104', '114', '115', '116'])).
% 0.77/0.96  thf('118', plain, ($false), inference('demod', [status(thm)], ['96', '117'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.82/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
