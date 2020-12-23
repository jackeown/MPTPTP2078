%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oLJPiyFwOY

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:36 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 254 expanded)
%              Number of leaves         :   37 (  94 expanded)
%              Depth                    :   19
%              Number of atoms          :  737 (2052 expanded)
%              Number of equality atoms :   40 (  98 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc10_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ) )).

thf('0',plain,(
    ! [X25: $i] :
      ( ( v3_pre_topc @ ( k2_struct_0 @ X25 ) @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc10_tops_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( u1_struct_0 @ X23 ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X9 ) @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k2_subset_1 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ ( sk_C @ X26 @ X27 ) @ X26 )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('8',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t35_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( v2_tex_2 @ B @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t35_tex_2])).

thf('10',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('13',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X26 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_pre_topc @ X29 @ X27 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 @ X29 )
       != ( sk_C @ X26 @ X27 ) )
      | ( v2_tex_2 @ X26 @ X27 )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ X0 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('33',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('42',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('43',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','53'])).

thf('55',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','56'])).

thf('58',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('59',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['24','57','58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    ~ ( v3_pre_topc @ ( u1_struct_0 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','65'])).

thf('67',plain,
    ( ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('69',plain,(
    ! [X24: $i] :
      ( ( l1_struct_0 @ X24 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v3_pre_topc @ ( k2_struct_0 @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['0','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['72','73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oLJPiyFwOY
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:48:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.99/1.20  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.99/1.20  % Solved by: fo/fo7.sh
% 0.99/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.20  % done 1543 iterations in 0.736s
% 0.99/1.20  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.99/1.20  % SZS output start Refutation
% 0.99/1.20  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.99/1.20  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.99/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.20  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.99/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.20  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.99/1.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.99/1.20  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.99/1.20  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.99/1.20  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.99/1.20  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.99/1.20  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.99/1.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.99/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.20  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.99/1.20  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.99/1.20  thf(sk_B_type, type, sk_B: $i > $i).
% 0.99/1.20  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.99/1.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.99/1.20  thf(fc10_tops_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( v3_pre_topc @ ( k2_struct_0 @ A ) @ A ) ))).
% 0.99/1.20  thf('0', plain,
% 0.99/1.20      (![X25 : $i]:
% 0.99/1.20         ((v3_pre_topc @ (k2_struct_0 @ X25) @ X25)
% 0.99/1.20          | ~ (l1_pre_topc @ X25)
% 0.99/1.20          | ~ (v2_pre_topc @ X25))),
% 0.99/1.20      inference('cnf', [status(esa)], [fc10_tops_1])).
% 0.99/1.20  thf(d3_struct_0, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.99/1.20  thf('1', plain,
% 0.99/1.20      (![X23 : $i]:
% 0.99/1.20         (((k2_struct_0 @ X23) = (u1_struct_0 @ X23)) | ~ (l1_struct_0 @ X23))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.99/1.20  thf(dt_k2_subset_1, axiom,
% 0.99/1.20    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.99/1.20  thf('2', plain,
% 0.99/1.20      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.99/1.20  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.99/1.20  thf('3', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.99/1.20      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.99/1.20  thf('4', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.99/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.20  thf(t4_subset_1, axiom,
% 0.99/1.20    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.99/1.20  thf('5', plain,
% 0.99/1.20      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.20  thf(d5_tex_2, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( l1_pre_topc @ A ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20           ( ( v2_tex_2 @ B @ A ) <=>
% 0.99/1.20             ( ![C:$i]:
% 0.99/1.20               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.99/1.20                      ( ![D:$i]:
% 0.99/1.20                        ( ( m1_subset_1 @
% 0.99/1.20                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.99/1.20                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.99/1.20                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.99/1.20                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.99/1.20  thf('6', plain,
% 0.99/1.20      (![X26 : $i, X27 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.20          | (r1_tarski @ (sk_C @ X26 @ X27) @ X26)
% 0.99/1.20          | (v2_tex_2 @ X26 @ X27)
% 0.99/1.20          | ~ (l1_pre_topc @ X27))),
% 0.99/1.20      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.99/1.20  thf('7', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X0)
% 0.99/1.20          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.99/1.20          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['5', '6'])).
% 0.99/1.20  thf(t3_xboole_1, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.99/1.20  thf('8', plain,
% 0.99/1.20      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.99/1.20      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.99/1.20  thf('9', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 0.99/1.20  thf(t35_tex_2, conjecture,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.99/1.20       ( ![B:$i]:
% 0.99/1.20         ( ( ( v1_xboole_0 @ B ) & 
% 0.99/1.20             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.20           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.99/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.20    (~( ![A:$i]:
% 0.99/1.20        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.99/1.20            ( l1_pre_topc @ A ) ) =>
% 0.99/1.20          ( ![B:$i]:
% 0.99/1.20            ( ( ( v1_xboole_0 @ B ) & 
% 0.99/1.20                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.99/1.20              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.99/1.20    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.99/1.20  thf('10', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('11', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(l13_xboole_0, axiom,
% 0.99/1.20    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.99/1.20  thf('12', plain,
% 0.99/1.20      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.99/1.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.99/1.20  thf('13', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['11', '12'])).
% 0.99/1.20  thf('14', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.99/1.20      inference('demod', [status(thm)], ['10', '13'])).
% 0.99/1.20  thf('15', plain,
% 0.99/1.20      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0)) | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['9', '14'])).
% 0.99/1.20  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('17', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.99/1.20      inference('demod', [status(thm)], ['15', '16'])).
% 0.99/1.20  thf('18', plain,
% 0.99/1.20      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.20  thf('19', plain,
% 0.99/1.20      (![X26 : $i, X27 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.20          | (m1_subset_1 @ (sk_C @ X26 @ X27) @ 
% 0.99/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.20          | (v2_tex_2 @ X26 @ X27)
% 0.99/1.20          | ~ (l1_pre_topc @ X27))),
% 0.99/1.20      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.99/1.20  thf('20', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (l1_pre_topc @ X0)
% 0.99/1.20          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.99/1.20          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 0.99/1.20             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['18', '19'])).
% 0.99/1.20  thf('21', plain,
% 0.99/1.20      (![X26 : $i, X27 : $i, X29 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.20          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.99/1.20          | ~ (v3_pre_topc @ X29 @ X27)
% 0.99/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X27) @ X26 @ X29)
% 0.99/1.20              != (sk_C @ X26 @ X27))
% 0.99/1.20          | (v2_tex_2 @ X26 @ X27)
% 0.99/1.20          | ~ (l1_pre_topc @ X27))),
% 0.99/1.20      inference('cnf', [status(esa)], [d5_tex_2])).
% 0.99/1.20  thf('22', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.99/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 0.99/1.20              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 0.99/1.20          | ~ (v3_pre_topc @ X1 @ X0)
% 0.99/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['20', '21'])).
% 0.99/1.20  thf('23', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.99/1.20          | ~ (v3_pre_topc @ X1 @ X0)
% 0.99/1.20          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 0.99/1.20              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 0.99/1.20          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 0.99/1.20          | ~ (l1_pre_topc @ X0)
% 0.99/1.20          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.99/1.20      inference('simplify', [status(thm)], ['22'])).
% 0.99/1.20  thf('24', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ X0)
% 0.99/1.20            != (sk_C @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))
% 0.99/1.20          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.99/1.20          | ~ (l1_pre_topc @ sk_A)
% 0.99/1.20          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.99/1.20          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.99/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['17', '23'])).
% 0.99/1.20  thf('25', plain,
% 0.99/1.20      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.20  thf(commutativity_k9_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.20       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.99/1.20  thf('26', plain,
% 0.99/1.20      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.99/1.20         (((k9_subset_1 @ X5 @ X7 @ X6) = (k9_subset_1 @ X5 @ X6 @ X7))
% 0.99/1.20          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.99/1.20      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.99/1.20  thf('27', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.99/1.20           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['25', '26'])).
% 0.99/1.20  thf('28', plain,
% 0.99/1.20      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.99/1.20      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.99/1.20  thf(redefinition_k9_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.20       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.99/1.20  thf('29', plain,
% 0.99/1.20      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.20         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.99/1.20          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.99/1.20      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.99/1.20  thf('30', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.99/1.20           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['28', '29'])).
% 0.99/1.20  thf('31', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.99/1.20           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.99/1.20      inference('demod', [status(thm)], ['27', '30'])).
% 0.99/1.20  thf('32', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.99/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.20  thf('33', plain,
% 0.99/1.20      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.99/1.20         (((k9_subset_1 @ X5 @ X7 @ X6) = (k9_subset_1 @ X5 @ X6 @ X7))
% 0.99/1.20          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.99/1.20      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.99/1.20  thf('34', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k9_subset_1 @ X0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['32', '33'])).
% 0.99/1.20  thf('35', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.99/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.20  thf('36', plain,
% 0.99/1.20      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.99/1.20         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.99/1.20          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.99/1.20      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.99/1.20  thf('37', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 0.99/1.20  thf('38', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k3_xboole_0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.99/1.20      inference('demod', [status(thm)], ['34', '37'])).
% 0.99/1.20  thf('39', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.99/1.20           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['28', '29'])).
% 0.99/1.20  thf('40', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['38', '39'])).
% 0.99/1.20  thf('41', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['38', '39'])).
% 0.99/1.20  thf(d1_xboole_0, axiom,
% 0.99/1.20    (![A:$i]:
% 0.99/1.20     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.99/1.20  thf('42', plain,
% 0.99/1.20      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.99/1.20      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.99/1.20  thf('43', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.99/1.20      inference('demod', [status(thm)], ['2', '3'])).
% 0.99/1.20  thf(dt_k9_subset_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.99/1.20       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.99/1.20  thf('44', plain,
% 0.99/1.20      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.99/1.20         ((m1_subset_1 @ (k9_subset_1 @ X10 @ X11 @ X12) @ (k1_zfmisc_1 @ X10))
% 0.99/1.20          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.99/1.20  thf('45', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['43', '44'])).
% 0.99/1.20  thf('46', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 0.99/1.20  thf('47', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.99/1.20      inference('demod', [status(thm)], ['45', '46'])).
% 0.99/1.20  thf(t5_subset, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.99/1.20          ( v1_xboole_0 @ C ) ) ))).
% 0.99/1.20  thf('48', plain,
% 0.99/1.20      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.99/1.20         (~ (r2_hidden @ X20 @ X21)
% 0.99/1.20          | ~ (v1_xboole_0 @ X22)
% 0.99/1.20          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t5_subset])).
% 0.99/1.20  thf('49', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.20         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['47', '48'])).
% 0.99/1.20  thf('50', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['42', '49'])).
% 0.99/1.20  thf('51', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         ((v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.99/1.20          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['41', '50'])).
% 0.99/1.20  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.99/1.20  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.99/1.20      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.99/1.20  thf('53', plain,
% 0.99/1.20      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.99/1.20      inference('demod', [status(thm)], ['51', '52'])).
% 0.99/1.20  thf('54', plain,
% 0.99/1.20      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['40', '53'])).
% 0.99/1.20  thf('55', plain,
% 0.99/1.20      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.99/1.20      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.99/1.20  thf('56', plain,
% 0.99/1.20      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['54', '55'])).
% 0.99/1.20  thf('57', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.99/1.20      inference('demod', [status(thm)], ['31', '56'])).
% 0.99/1.20  thf('58', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.99/1.20      inference('demod', [status(thm)], ['15', '16'])).
% 0.99/1.20  thf('59', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.99/1.20      inference('demod', [status(thm)], ['15', '16'])).
% 0.99/1.20  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('61', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.99/1.20      inference('demod', [status(thm)], ['15', '16'])).
% 0.99/1.20  thf('62', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.20          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.99/1.20          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 0.99/1.20          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.99/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.20      inference('demod', [status(thm)], ['24', '57', '58', '59', '60', '61'])).
% 0.99/1.20  thf('63', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.99/1.20          | ~ (v3_pre_topc @ X0 @ sk_A)
% 0.99/1.20          | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.99/1.20      inference('simplify', [status(thm)], ['62'])).
% 0.99/1.20  thf('64', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.99/1.20      inference('demod', [status(thm)], ['10', '13'])).
% 0.99/1.20  thf('65', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (v3_pre_topc @ X0 @ sk_A)
% 0.99/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.99/1.20      inference('clc', [status(thm)], ['63', '64'])).
% 0.99/1.20  thf('66', plain, (~ (v3_pre_topc @ (u1_struct_0 @ sk_A) @ sk_A)),
% 0.99/1.20      inference('sup-', [status(thm)], ['4', '65'])).
% 0.99/1.20  thf('67', plain,
% 0.99/1.20      ((~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['1', '66'])).
% 0.99/1.20  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(dt_l1_pre_topc, axiom,
% 0.99/1.20    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.99/1.20  thf('69', plain,
% 0.99/1.20      (![X24 : $i]: ((l1_struct_0 @ X24) | ~ (l1_pre_topc @ X24))),
% 0.99/1.20      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.99/1.20  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.99/1.20      inference('sup-', [status(thm)], ['68', '69'])).
% 0.99/1.20  thf('71', plain, (~ (v3_pre_topc @ (k2_struct_0 @ sk_A) @ sk_A)),
% 0.99/1.20      inference('demod', [status(thm)], ['67', '70'])).
% 0.99/1.20  thf('72', plain, ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A))),
% 0.99/1.20      inference('sup-', [status(thm)], ['0', '71'])).
% 0.99/1.20  thf('73', plain, ((v2_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('74', plain, ((l1_pre_topc @ sk_A)),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf('75', plain, ($false),
% 0.99/1.20      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.99/1.20  
% 0.99/1.20  % SZS output end Refutation
% 0.99/1.20  
% 0.99/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
