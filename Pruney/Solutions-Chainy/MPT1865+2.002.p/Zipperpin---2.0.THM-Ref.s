%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I8khUho2Q3

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:20 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 190 expanded)
%              Number of leaves         :   26 (  69 expanded)
%              Depth                    :   13
%              Number of atoms          :  736 (2473 expanded)
%              Number of equality atoms :   27 ( 113 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t33_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( v4_pre_topc @ D @ A )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                                = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tex_2])).

thf('0',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t60_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( ( r2_hidden @ C @ B )
          & ( A != C ) )
        | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k1_tarski @ A ) ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( X11 != X13 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X11 @ X13 ) @ X12 )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t60_zfmisc_1])).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ X13 @ X13 ) @ X12 )
        = ( k1_tarski @ X13 ) )
      | ~ ( r2_hidden @ X13 @ X12 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('11',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k3_xboole_0 @ ( k1_tarski @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tex_2,axiom,(
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
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X25 ) @ X24 @ ( sk_D @ X26 @ X24 @ X25 ) )
        = X26 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ X13 @ X13 ) @ X12 )
        = ( k1_tarski @ X13 ) )
      | ~ ( r2_hidden @ X13 @ X12 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('27',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C_1 ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('32',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['24','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('35',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ( m1_subset_1 @ ( sk_D @ X26 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X28: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X28 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X28 @ sk_A )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v2_tex_2 @ X24 @ X25 )
      | ( v4_pre_topc @ ( sk_D @ X26 @ X24 @ X25 ) @ X25 )
      | ~ ( r1_tarski @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference('sup+',[status(thm)],['30','31'])).

thf('55',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['45','55'])).

thf('57',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','57'])).

thf('59',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.I8khUho2Q3
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:36:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.27/1.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.27/1.49  % Solved by: fo/fo7.sh
% 1.27/1.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.49  % done 2058 iterations in 1.040s
% 1.27/1.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.27/1.49  % SZS output start Refutation
% 1.27/1.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.27/1.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.27/1.49  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.27/1.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.27/1.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.27/1.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.27/1.49  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.27/1.49  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.27/1.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.27/1.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.27/1.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.27/1.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.27/1.49  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.27/1.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.27/1.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.49  thf(t33_tex_2, conjecture,
% 1.27/1.49    (![A:$i]:
% 1.27/1.49     ( ( l1_pre_topc @ A ) =>
% 1.27/1.49       ( ![B:$i]:
% 1.27/1.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.49           ( ( v2_tex_2 @ B @ A ) =>
% 1.27/1.49             ( ![C:$i]:
% 1.27/1.49               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.27/1.49                 ( ~( ( r2_hidden @ C @ B ) & 
% 1.27/1.49                      ( ![D:$i]:
% 1.27/1.49                        ( ( m1_subset_1 @
% 1.27/1.49                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.49                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.27/1.49                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.27/1.49                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.27/1.49  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.49    (~( ![A:$i]:
% 1.27/1.49        ( ( l1_pre_topc @ A ) =>
% 1.27/1.49          ( ![B:$i]:
% 1.27/1.49            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.49              ( ( v2_tex_2 @ B @ A ) =>
% 1.27/1.49                ( ![C:$i]:
% 1.27/1.49                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.27/1.49                    ( ~( ( r2_hidden @ C @ B ) & 
% 1.27/1.49                         ( ![D:$i]:
% 1.27/1.49                           ( ( m1_subset_1 @
% 1.27/1.49                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.49                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.27/1.49                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.27/1.49                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.27/1.49    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 1.27/1.49  thf('0', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('1', plain,
% 1.27/1.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf(t5_subset, axiom,
% 1.27/1.49    (![A:$i,B:$i,C:$i]:
% 1.27/1.49     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.27/1.49          ( v1_xboole_0 @ C ) ) ))).
% 1.27/1.49  thf('2', plain,
% 1.27/1.49      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.27/1.49         (~ (r2_hidden @ X19 @ X20)
% 1.27/1.49          | ~ (v1_xboole_0 @ X21)
% 1.27/1.49          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.27/1.49      inference('cnf', [status(esa)], [t5_subset])).
% 1.27/1.49  thf('3', plain,
% 1.27/1.49      (![X0 : $i]:
% 1.27/1.49         (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 1.27/1.49      inference('sup-', [status(thm)], ['1', '2'])).
% 1.27/1.49  thf('4', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf(t2_subset, axiom,
% 1.27/1.49    (![A:$i,B:$i]:
% 1.27/1.49     ( ( m1_subset_1 @ A @ B ) =>
% 1.27/1.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.27/1.49  thf('5', plain,
% 1.27/1.49      (![X14 : $i, X15 : $i]:
% 1.27/1.49         ((r2_hidden @ X14 @ X15)
% 1.27/1.49          | (v1_xboole_0 @ X15)
% 1.27/1.49          | ~ (m1_subset_1 @ X14 @ X15))),
% 1.27/1.49      inference('cnf', [status(esa)], [t2_subset])).
% 1.27/1.49  thf('6', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | (r2_hidden @ sk_C_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('sup-', [status(thm)], ['4', '5'])).
% 1.27/1.49  thf(t60_zfmisc_1, axiom,
% 1.27/1.49    (![A:$i,B:$i,C:$i]:
% 1.27/1.49     ( ( r2_hidden @ A @ B ) =>
% 1.27/1.49       ( ( ( r2_hidden @ C @ B ) & ( ( A ) != ( C ) ) ) | 
% 1.27/1.49         ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k1_tarski @ A ) ) ) ))).
% 1.27/1.49  thf('7', plain,
% 1.27/1.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.27/1.49         (~ (r2_hidden @ X11 @ X12)
% 1.27/1.49          | ((X11) != (X13))
% 1.27/1.49          | ((k3_xboole_0 @ (k2_tarski @ X11 @ X13) @ X12) = (k1_tarski @ X11)))),
% 1.27/1.49      inference('cnf', [status(esa)], [t60_zfmisc_1])).
% 1.27/1.49  thf('8', plain,
% 1.27/1.49      (![X12 : $i, X13 : $i]:
% 1.27/1.49         (((k3_xboole_0 @ (k2_tarski @ X13 @ X13) @ X12) = (k1_tarski @ X13))
% 1.27/1.49          | ~ (r2_hidden @ X13 @ X12))),
% 1.27/1.49      inference('simplify', [status(thm)], ['7'])).
% 1.27/1.49  thf('9', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | ((k3_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 1.27/1.49            = (k1_tarski @ sk_C_1)))),
% 1.27/1.49      inference('sup-', [status(thm)], ['6', '8'])).
% 1.27/1.49  thf(t69_enumset1, axiom,
% 1.27/1.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.27/1.49  thf('10', plain,
% 1.27/1.49      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 1.27/1.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.27/1.49  thf('11', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | ((k3_xboole_0 @ (k1_tarski @ sk_C_1) @ (u1_struct_0 @ sk_A))
% 1.27/1.49            = (k1_tarski @ sk_C_1)))),
% 1.27/1.49      inference('demod', [status(thm)], ['9', '10'])).
% 1.27/1.49  thf(commutativity_k3_xboole_0, axiom,
% 1.27/1.49    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.27/1.49  thf('12', plain,
% 1.27/1.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.49  thf(t17_xboole_1, axiom,
% 1.27/1.49    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.27/1.49  thf('13', plain,
% 1.27/1.49      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.27/1.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.27/1.49  thf(t3_subset, axiom,
% 1.27/1.49    (![A:$i,B:$i]:
% 1.27/1.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.27/1.49  thf('14', plain,
% 1.27/1.49      (![X16 : $i, X18 : $i]:
% 1.27/1.49         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 1.27/1.49      inference('cnf', [status(esa)], [t3_subset])).
% 1.27/1.49  thf('15', plain,
% 1.27/1.49      (![X0 : $i, X1 : $i]:
% 1.27/1.49         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.27/1.49      inference('sup-', [status(thm)], ['13', '14'])).
% 1.27/1.49  thf('16', plain,
% 1.27/1.49      (![X0 : $i, X1 : $i]:
% 1.27/1.49         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.27/1.49      inference('sup+', [status(thm)], ['12', '15'])).
% 1.27/1.49  thf('17', plain,
% 1.27/1.49      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 1.27/1.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('sup+', [status(thm)], ['11', '16'])).
% 1.27/1.49  thf('18', plain,
% 1.27/1.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf(d6_tex_2, axiom,
% 1.27/1.49    (![A:$i]:
% 1.27/1.49     ( ( l1_pre_topc @ A ) =>
% 1.27/1.49       ( ![B:$i]:
% 1.27/1.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.49           ( ( v2_tex_2 @ B @ A ) <=>
% 1.27/1.49             ( ![C:$i]:
% 1.27/1.49               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.49                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.27/1.49                      ( ![D:$i]:
% 1.27/1.49                        ( ( m1_subset_1 @
% 1.27/1.49                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.27/1.49                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 1.27/1.49                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.27/1.49                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.27/1.49  thf('19', plain,
% 1.27/1.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.27/1.49         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.27/1.49          | ~ (v2_tex_2 @ X24 @ X25)
% 1.27/1.49          | ((k9_subset_1 @ (u1_struct_0 @ X25) @ X24 @ 
% 1.27/1.49              (sk_D @ X26 @ X24 @ X25)) = (X26))
% 1.27/1.49          | ~ (r1_tarski @ X26 @ X24)
% 1.27/1.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.27/1.49          | ~ (l1_pre_topc @ X25))),
% 1.27/1.49      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.27/1.49  thf('20', plain,
% 1.27/1.49      (![X0 : $i]:
% 1.27/1.49         (~ (l1_pre_topc @ sk_A)
% 1.27/1.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49          | ~ (r1_tarski @ X0 @ sk_B)
% 1.27/1.49          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.27/1.49              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 1.27/1.49          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.27/1.49      inference('sup-', [status(thm)], ['18', '19'])).
% 1.27/1.49  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('22', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('23', plain,
% 1.27/1.49      (![X0 : $i]:
% 1.27/1.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49          | ~ (r1_tarski @ X0 @ sk_B)
% 1.27/1.49          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.27/1.49              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 1.27/1.49      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.27/1.49  thf('24', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.27/1.49            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 1.27/1.49        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 1.27/1.49      inference('sup-', [status(thm)], ['17', '23'])).
% 1.27/1.49  thf('25', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('26', plain,
% 1.27/1.49      (![X12 : $i, X13 : $i]:
% 1.27/1.49         (((k3_xboole_0 @ (k2_tarski @ X13 @ X13) @ X12) = (k1_tarski @ X13))
% 1.27/1.49          | ~ (r2_hidden @ X13 @ X12))),
% 1.27/1.49      inference('simplify', [status(thm)], ['7'])).
% 1.27/1.49  thf('27', plain,
% 1.27/1.49      (((k3_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_B)
% 1.27/1.49         = (k1_tarski @ sk_C_1))),
% 1.27/1.49      inference('sup-', [status(thm)], ['25', '26'])).
% 1.27/1.49  thf('28', plain,
% 1.27/1.49      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 1.27/1.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.27/1.49  thf('29', plain,
% 1.27/1.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.27/1.49      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.49  thf('30', plain,
% 1.27/1.49      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C_1)) = (k1_tarski @ sk_C_1))),
% 1.27/1.49      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.27/1.49  thf('31', plain,
% 1.27/1.49      (![X3 : $i, X4 : $i]: (r1_tarski @ (k3_xboole_0 @ X3 @ X4) @ X3)),
% 1.27/1.49      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.27/1.49  thf('32', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 1.27/1.49      inference('sup+', [status(thm)], ['30', '31'])).
% 1.27/1.49  thf('33', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.27/1.49            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1)))),
% 1.27/1.49      inference('demod', [status(thm)], ['24', '32'])).
% 1.27/1.49  thf('34', plain,
% 1.27/1.49      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 1.27/1.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('sup+', [status(thm)], ['11', '16'])).
% 1.27/1.49  thf('35', plain,
% 1.27/1.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('36', plain,
% 1.27/1.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.27/1.49         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.27/1.49          | ~ (v2_tex_2 @ X24 @ X25)
% 1.27/1.49          | (m1_subset_1 @ (sk_D @ X26 @ X24 @ X25) @ 
% 1.27/1.49             (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.27/1.49          | ~ (r1_tarski @ X26 @ X24)
% 1.27/1.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.27/1.49          | ~ (l1_pre_topc @ X25))),
% 1.27/1.49      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.27/1.49  thf('37', plain,
% 1.27/1.49      (![X0 : $i]:
% 1.27/1.49         (~ (l1_pre_topc @ sk_A)
% 1.27/1.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49          | ~ (r1_tarski @ X0 @ sk_B)
% 1.27/1.49          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 1.27/1.49             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.27/1.49      inference('sup-', [status(thm)], ['35', '36'])).
% 1.27/1.49  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('39', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('40', plain,
% 1.27/1.49      (![X0 : $i]:
% 1.27/1.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49          | ~ (r1_tarski @ X0 @ sk_B)
% 1.27/1.49          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 1.27/1.49             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.27/1.49      inference('demod', [status(thm)], ['37', '38', '39'])).
% 1.27/1.49  thf('41', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 1.27/1.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 1.27/1.49      inference('sup-', [status(thm)], ['34', '40'])).
% 1.27/1.49  thf('42', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 1.27/1.49      inference('sup+', [status(thm)], ['30', '31'])).
% 1.27/1.49  thf('43', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | (m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 1.27/1.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.27/1.49      inference('demod', [status(thm)], ['41', '42'])).
% 1.27/1.49  thf('44', plain,
% 1.27/1.49      (![X28 : $i]:
% 1.27/1.49         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X28)
% 1.27/1.49            != (k1_tarski @ sk_C_1))
% 1.27/1.49          | ~ (v4_pre_topc @ X28 @ sk_A)
% 1.27/1.49          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('45', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | ~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 1.27/1.49        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.27/1.49            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 1.27/1.49            != (k1_tarski @ sk_C_1)))),
% 1.27/1.49      inference('sup-', [status(thm)], ['43', '44'])).
% 1.27/1.49  thf('46', plain,
% 1.27/1.49      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 1.27/1.49         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('sup+', [status(thm)], ['11', '16'])).
% 1.27/1.49  thf('47', plain,
% 1.27/1.49      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('48', plain,
% 1.27/1.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.27/1.49         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.27/1.49          | ~ (v2_tex_2 @ X24 @ X25)
% 1.27/1.49          | (v4_pre_topc @ (sk_D @ X26 @ X24 @ X25) @ X25)
% 1.27/1.49          | ~ (r1_tarski @ X26 @ X24)
% 1.27/1.49          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.27/1.49          | ~ (l1_pre_topc @ X25))),
% 1.27/1.49      inference('cnf', [status(esa)], [d6_tex_2])).
% 1.27/1.49  thf('49', plain,
% 1.27/1.49      (![X0 : $i]:
% 1.27/1.49         (~ (l1_pre_topc @ sk_A)
% 1.27/1.49          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49          | ~ (r1_tarski @ X0 @ sk_B)
% 1.27/1.49          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 1.27/1.49          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 1.27/1.49      inference('sup-', [status(thm)], ['47', '48'])).
% 1.27/1.49  thf('50', plain, ((l1_pre_topc @ sk_A)),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('51', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 1.27/1.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.49  thf('52', plain,
% 1.27/1.49      (![X0 : $i]:
% 1.27/1.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.27/1.49          | ~ (r1_tarski @ X0 @ sk_B)
% 1.27/1.49          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 1.27/1.49      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.27/1.49  thf('53', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 1.27/1.49        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 1.27/1.49      inference('sup-', [status(thm)], ['46', '52'])).
% 1.27/1.49  thf('54', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 1.27/1.49      inference('sup+', [status(thm)], ['30', '31'])).
% 1.27/1.49  thf('55', plain,
% 1.27/1.49      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 1.27/1.49        | (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A))),
% 1.27/1.49      inference('demod', [status(thm)], ['53', '54'])).
% 1.27/1.49  thf('56', plain,
% 1.27/1.49      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 1.27/1.49          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_1))
% 1.27/1.49        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.27/1.49      inference('clc', [status(thm)], ['45', '55'])).
% 1.27/1.49  thf('57', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.27/1.49      inference('clc', [status(thm)], ['33', '56'])).
% 1.27/1.49  thf('58', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B)),
% 1.27/1.49      inference('demod', [status(thm)], ['3', '57'])).
% 1.27/1.49  thf('59', plain, ($false), inference('sup-', [status(thm)], ['0', '58'])).
% 1.27/1.49  
% 1.27/1.49  % SZS output end Refutation
% 1.27/1.49  
% 1.27/1.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
