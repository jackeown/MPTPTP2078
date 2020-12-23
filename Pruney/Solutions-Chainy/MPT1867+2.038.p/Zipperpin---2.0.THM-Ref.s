%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tJSETjlOjQ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:31 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 436 expanded)
%              Number of leaves         :   32 ( 156 expanded)
%              Depth                    :   22
%              Number of atoms          :  914 (3069 expanded)
%              Number of equality atoms :   48 ( 179 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

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

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

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
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v4_pre_topc @ X23 @ X24 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k9_subset_1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('30',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k9_subset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k9_subset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['28','43'])).

thf('45',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','47'])).

thf('49',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('50',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( r1_tarski @ ( sk_C_1 @ X25 @ X26 ) @ X25 )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
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

thf('55',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,
    ( ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,
    ( ( sk_C_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X25: $i,X26: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v4_pre_topc @ X28 @ X26 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 @ X28 )
       != ( sk_C_1 @ X25 @ X26 ) )
      | ( v2_tex_2 @ X25 @ X26 )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X2 )
       != ( sk_C_1 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 ) )
      | ~ ( v4_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('72',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k9_subset_1 @ X5 @ X7 @ X6 )
        = ( k9_subset_1 @ X5 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k9_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('75',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k9_subset_1 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 )
      | ( ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) )
       != ( sk_C_1 @ ( k3_xboole_0 @ X1 @ ( u1_struct_0 @ X0 ) ) @ X0 ) )
      | ~ ( v4_pre_topc @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['70','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','46'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_A )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ ( u1_struct_0 @ sk_A ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','47'])).

thf('87',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','58'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tex_2 @ ( k3_xboole_0 @ X1 @ X0 ) @ sk_A )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v4_pre_topc @ k1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['85','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['90','91','92','93'])).

thf('95',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tJSETjlOjQ
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.91/1.14  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.14  % Solved by: fo/fo7.sh
% 0.91/1.14  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.14  % done 1409 iterations in 0.697s
% 0.91/1.14  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.14  % SZS output start Refutation
% 0.91/1.14  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.14  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.14  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.14  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.14  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.91/1.14  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.14  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.14  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.91/1.14  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.91/1.14  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.91/1.14  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.91/1.14  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.14  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.14  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.91/1.14  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.91/1.14  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.14  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.14  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.14  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.14  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.14  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.14      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.14  thf(d3_tarski, axiom,
% 0.91/1.14    (![A:$i,B:$i]:
% 0.91/1.14     ( ( r1_tarski @ A @ B ) <=>
% 0.91/1.14       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.91/1.14  thf('1', plain,
% 0.91/1.14      (![X1 : $i, X3 : $i]:
% 0.91/1.14         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.91/1.14      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.14  thf(dt_k2_subset_1, axiom,
% 0.91/1.14    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.91/1.14  thf('2', plain,
% 0.91/1.14      (![X9 : $i]: (m1_subset_1 @ (k2_subset_1 @ X9) @ (k1_zfmisc_1 @ X9))),
% 0.91/1.14      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.91/1.14  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.91/1.14  thf('3', plain, (![X8 : $i]: ((k2_subset_1 @ X8) = (X8))),
% 0.91/1.14      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.91/1.14  thf('4', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.91/1.14      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.14  thf(t5_subset, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.91/1.14          ( v1_xboole_0 @ C ) ) ))).
% 0.91/1.14  thf('5', plain,
% 0.91/1.14      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.91/1.14         (~ (r2_hidden @ X20 @ X21)
% 0.91/1.14          | ~ (v1_xboole_0 @ X22)
% 0.91/1.14          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.91/1.14      inference('cnf', [status(esa)], [t5_subset])).
% 0.91/1.14  thf('6', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.14  thf('7', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['1', '6'])).
% 0.91/1.14  thf(t3_xboole_1, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.14  thf('8', plain,
% 0.91/1.14      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.91/1.14      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.14  thf('9', plain,
% 0.91/1.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf(t4_subset_1, axiom,
% 0.91/1.14    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.91/1.14  thf('10', plain,
% 0.91/1.14      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.91/1.14      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.14  thf('11', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.14      inference('sup+', [status(thm)], ['9', '10'])).
% 0.91/1.14  thf(cc2_pre_topc, axiom,
% 0.91/1.14    (![A:$i]:
% 0.91/1.14     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.14       ( ![B:$i]:
% 0.91/1.14         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.14           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.91/1.14  thf('12', plain,
% 0.91/1.14      (![X23 : $i, X24 : $i]:
% 0.91/1.14         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.91/1.14          | (v4_pre_topc @ X23 @ X24)
% 0.91/1.14          | ~ (v1_xboole_0 @ X23)
% 0.91/1.14          | ~ (l1_pre_topc @ X24)
% 0.91/1.14          | ~ (v2_pre_topc @ X24))),
% 0.91/1.14      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.91/1.14  thf('13', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         (~ (v1_xboole_0 @ X1)
% 0.91/1.14          | ~ (v2_pre_topc @ X0)
% 0.91/1.14          | ~ (l1_pre_topc @ X0)
% 0.91/1.14          | ~ (v1_xboole_0 @ X1)
% 0.91/1.14          | (v4_pre_topc @ X1 @ X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['11', '12'])).
% 0.91/1.14  thf('14', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((v4_pre_topc @ X1 @ X0)
% 0.91/1.14          | ~ (l1_pre_topc @ X0)
% 0.91/1.14          | ~ (v2_pre_topc @ X0)
% 0.91/1.14          | ~ (v1_xboole_0 @ X1))),
% 0.91/1.14      inference('simplify', [status(thm)], ['13'])).
% 0.91/1.14  thf('15', plain,
% 0.91/1.14      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.91/1.14      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.14  thf('16', plain,
% 0.91/1.14      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.14      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.14  thf('17', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.91/1.14      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.14  thf(commutativity_k9_subset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.14       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.91/1.14  thf('18', plain,
% 0.91/1.14      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.14         (((k9_subset_1 @ X5 @ X7 @ X6) = (k9_subset_1 @ X5 @ X6 @ X7))
% 0.91/1.14          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.91/1.14      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.91/1.14  thf('19', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k9_subset_1 @ X0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.91/1.14      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.14  thf('20', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.91/1.14      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.14  thf(redefinition_k9_subset_1, axiom,
% 0.91/1.14    (![A:$i,B:$i,C:$i]:
% 0.91/1.14     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.14       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.91/1.14  thf('21', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.14         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.91/1.14          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.91/1.14  thf('22', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.14  thf('23', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k3_xboole_0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.91/1.14      inference('demod', [status(thm)], ['19', '22'])).
% 0.91/1.14  thf('24', plain,
% 0.91/1.14      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.91/1.14      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.14  thf('25', plain,
% 0.91/1.14      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.14         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.91/1.14          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.91/1.14      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.91/1.14  thf('26', plain,
% 0.91/1.14      (![X0 : $i, X1 : $i]:
% 0.91/1.14         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.91/1.14           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.91/1.14      inference('sup-', [status(thm)], ['24', '25'])).
% 0.91/1.15  thf('27', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['23', '26'])).
% 0.91/1.15  thf('28', plain,
% 0.91/1.15      (![X1 : $i, X3 : $i]:
% 0.91/1.15         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.91/1.15      inference('cnf', [status(esa)], [d3_tarski])).
% 0.91/1.15  thf('29', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k9_subset_1 @ X0 @ X1 @ X0) = (k9_subset_1 @ X0 @ X0 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['17', '18'])).
% 0.91/1.15  thf('30', plain,
% 0.91/1.15      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.91/1.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.15  thf('31', plain,
% 0.91/1.15      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.15         (((k9_subset_1 @ X5 @ X7 @ X6) = (k9_subset_1 @ X5 @ X6 @ X7))
% 0.91/1.15          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.91/1.15  thf('32', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.91/1.15           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['30', '31'])).
% 0.91/1.15  thf('33', plain, (![X9 : $i]: (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X9))),
% 0.91/1.15      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.15  thf(dt_k9_subset_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.15       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.91/1.15  thf('34', plain,
% 0.91/1.15      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.91/1.15         ((m1_subset_1 @ (k9_subset_1 @ X10 @ X11 @ X12) @ (k1_zfmisc_1 @ X10))
% 0.91/1.15          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X10)))),
% 0.91/1.15      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.91/1.15  thf('35', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.15  thf('36', plain,
% 0.91/1.15      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X20 @ X21)
% 0.91/1.15          | ~ (v1_xboole_0 @ X22)
% 0.91/1.15          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X22)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t5_subset])).
% 0.91/1.15  thf('37', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         (~ (v1_xboole_0 @ X0)
% 0.91/1.15          | ~ (r2_hidden @ X2 @ (k9_subset_1 @ X0 @ X1 @ X0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.15  thf('38', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X1 @ (k9_subset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))
% 0.91/1.15          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['32', '37'])).
% 0.91/1.15  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.15      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.15  thf('40', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ~ (r2_hidden @ X1 @ (k9_subset_1 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['38', '39'])).
% 0.91/1.15  thf('41', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ~ (r2_hidden @ X1 @ (k9_subset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['29', '40'])).
% 0.91/1.15  thf('42', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.15  thf('43', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['41', '42'])).
% 0.91/1.15  thf('44', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)),
% 0.91/1.15      inference('sup-', [status(thm)], ['28', '43'])).
% 0.91/1.15  thf('45', plain,
% 0.91/1.15      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.91/1.15      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.15  thf('46', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['44', '45'])).
% 0.91/1.15  thf('47', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['27', '46'])).
% 0.91/1.15  thf('48', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['16', '47'])).
% 0.91/1.15  thf('49', plain,
% 0.91/1.15      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.91/1.15      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.15  thf(d6_tex_2, axiom,
% 0.91/1.15    (![A:$i]:
% 0.91/1.15     ( ( l1_pre_topc @ A ) =>
% 0.91/1.15       ( ![B:$i]:
% 0.91/1.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.15           ( ( v2_tex_2 @ B @ A ) <=>
% 0.91/1.15             ( ![C:$i]:
% 0.91/1.15               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.15                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.91/1.15                      ( ![D:$i]:
% 0.91/1.15                        ( ( m1_subset_1 @
% 0.91/1.15                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.15                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.91/1.15                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.91/1.15                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.15  thf('50', plain,
% 0.91/1.15      (![X25 : $i, X26 : $i]:
% 0.91/1.15         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.91/1.15          | (r1_tarski @ (sk_C_1 @ X25 @ X26) @ X25)
% 0.91/1.15          | (v2_tex_2 @ X25 @ X26)
% 0.91/1.15          | ~ (l1_pre_topc @ X26))),
% 0.91/1.15      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.91/1.15  thf('51', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (l1_pre_topc @ X0)
% 0.91/1.15          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.91/1.15          | (r1_tarski @ (sk_C_1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.15  thf('52', plain,
% 0.91/1.15      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ k1_xboole_0))),
% 0.91/1.15      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.91/1.15  thf('53', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.91/1.15          | ~ (l1_pre_topc @ X0)
% 0.91/1.15          | ((sk_C_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['51', '52'])).
% 0.91/1.15  thf('54', plain,
% 0.91/1.15      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.15  thf(t35_tex_2, conjecture,
% 0.91/1.15    (![A:$i]:
% 0.91/1.15     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.91/1.15       ( ![B:$i]:
% 0.91/1.15         ( ( ( v1_xboole_0 @ B ) & 
% 0.91/1.15             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.15           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.91/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.15    (~( ![A:$i]:
% 0.91/1.15        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.91/1.15            ( l1_pre_topc @ A ) ) =>
% 0.91/1.15          ( ![B:$i]:
% 0.91/1.15            ( ( ( v1_xboole_0 @ B ) & 
% 0.91/1.15                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.15              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.91/1.15    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.91/1.15  thf('55', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('56', plain, ((v1_xboole_0 @ sk_B)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('57', plain,
% 0.91/1.15      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((X0) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.15  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['56', '57'])).
% 0.91/1.15  thf('59', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.91/1.15      inference('demod', [status(thm)], ['55', '58'])).
% 0.91/1.15  thf('60', plain,
% 0.91/1.15      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['54', '59'])).
% 0.91/1.15  thf('61', plain,
% 0.91/1.15      ((((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.91/1.15        | ~ (l1_pre_topc @ sk_A)
% 0.91/1.15        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['53', '60'])).
% 0.91/1.15  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.15      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.15  thf('64', plain, (((sk_C_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.91/1.15  thf('65', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (((sk_C_1 @ (k3_xboole_0 @ X1 @ X0) @ sk_A) = (k1_xboole_0))
% 0.91/1.15          | ~ (v1_xboole_0 @ X1))),
% 0.91/1.15      inference('sup+', [status(thm)], ['48', '64'])).
% 0.91/1.15  thf('66', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['33', '34'])).
% 0.91/1.15  thf('67', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['20', '21'])).
% 0.91/1.15  thf('68', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['66', '67'])).
% 0.91/1.15  thf('69', plain,
% 0.91/1.15      (![X25 : $i, X26 : $i, X28 : $i]:
% 0.91/1.15         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.91/1.15          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.91/1.15          | ~ (v4_pre_topc @ X28 @ X26)
% 0.91/1.15          | ((k9_subset_1 @ (u1_struct_0 @ X26) @ X25 @ X28)
% 0.91/1.15              != (sk_C_1 @ X25 @ X26))
% 0.91/1.15          | (v2_tex_2 @ X25 @ X26)
% 0.91/1.15          | ~ (l1_pre_topc @ X26))),
% 0.91/1.15      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.91/1.15  thf('70', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         (~ (l1_pre_topc @ X0)
% 0.91/1.15          | (v2_tex_2 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 0.91/1.15          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.91/1.15              (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X2)
% 0.91/1.15              != (sk_C_1 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0))
% 0.91/1.15          | ~ (v4_pre_topc @ X2 @ X0)
% 0.91/1.15          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['68', '69'])).
% 0.91/1.15  thf('71', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['66', '67'])).
% 0.91/1.15  thf('72', plain,
% 0.91/1.15      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.15         (((k9_subset_1 @ X5 @ X7 @ X6) = (k9_subset_1 @ X5 @ X6 @ X7))
% 0.91/1.15          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X5)))),
% 0.91/1.15      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.91/1.15  thf('73', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((k9_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.15           = (k9_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.91/1.15      inference('sup-', [status(thm)], ['71', '72'])).
% 0.91/1.15  thf('74', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.15      inference('demod', [status(thm)], ['66', '67'])).
% 0.91/1.15  thf('75', plain,
% 0.91/1.15      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.91/1.15         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.91/1.15          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.91/1.15      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.91/1.15  thf('76', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((k9_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.15           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['74', '75'])).
% 0.91/1.15  thf('77', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.91/1.15           = (k9_subset_1 @ X0 @ (k3_xboole_0 @ X1 @ X0) @ X2))),
% 0.91/1.15      inference('demod', [status(thm)], ['73', '76'])).
% 0.91/1.15  thf('78', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.15         (~ (l1_pre_topc @ X0)
% 0.91/1.15          | (v2_tex_2 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0)
% 0.91/1.15          | ((k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)))
% 0.91/1.15              != (sk_C_1 @ (k3_xboole_0 @ X1 @ (u1_struct_0 @ X0)) @ X0))
% 0.91/1.15          | ~ (v4_pre_topc @ X2 @ X0)
% 0.91/1.15          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.91/1.15      inference('demod', [status(thm)], ['70', '77'])).
% 0.91/1.15  thf('79', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))
% 0.91/1.15            != (k1_xboole_0))
% 0.91/1.15          | ~ (v1_xboole_0 @ X0)
% 0.91/1.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.15          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.91/1.15          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.91/1.15          | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.15      inference('sup-', [status(thm)], ['65', '78'])).
% 0.91/1.15  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('81', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)))
% 0.91/1.15            != (k1_xboole_0))
% 0.91/1.15          | ~ (v1_xboole_0 @ X0)
% 0.91/1.15          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.15          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.91/1.15          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_A))),
% 0.91/1.15      inference('demod', [status(thm)], ['79', '80'])).
% 0.91/1.15  thf('82', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((v2_tex_2 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.91/1.15          | ~ (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 0.91/1.15          | ~ (v1_xboole_0 @ X0)
% 0.91/1.15          | ((k3_xboole_0 @ k1_xboole_0 @ 
% 0.91/1.15              (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_A))) != (k1_xboole_0)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['15', '81'])).
% 0.91/1.15  thf('83', plain,
% 0.91/1.15      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['27', '46'])).
% 0.91/1.15  thf('84', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((v2_tex_2 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_A)
% 0.91/1.15          | ~ (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 0.91/1.15          | ~ (v1_xboole_0 @ X0)
% 0.91/1.15          | ((k1_xboole_0) != (k1_xboole_0)))),
% 0.91/1.15      inference('demod', [status(thm)], ['82', '83'])).
% 0.91/1.15  thf('85', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (v1_xboole_0 @ X0)
% 0.91/1.15          | ~ (v4_pre_topc @ k1_xboole_0 @ sk_A)
% 0.91/1.15          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ (u1_struct_0 @ sk_A)) @ sk_A))),
% 0.91/1.15      inference('simplify', [status(thm)], ['84'])).
% 0.91/1.15  thf('86', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.15      inference('sup+', [status(thm)], ['16', '47'])).
% 0.91/1.15  thf('87', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.91/1.15      inference('demod', [status(thm)], ['55', '58'])).
% 0.91/1.15  thf('88', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (~ (v2_tex_2 @ (k3_xboole_0 @ X1 @ X0) @ sk_A) | ~ (v1_xboole_0 @ X1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['86', '87'])).
% 0.91/1.15  thf('89', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (v4_pre_topc @ k1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.91/1.15      inference('clc', [status(thm)], ['85', '88'])).
% 0.91/1.15  thf('90', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.91/1.15          | ~ (v2_pre_topc @ sk_A)
% 0.91/1.15          | ~ (l1_pre_topc @ sk_A)
% 0.91/1.15          | ~ (v1_xboole_0 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['14', '89'])).
% 0.91/1.15  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.15      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.15  thf('92', plain, ((v2_pre_topc @ sk_A)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('94', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.91/1.15      inference('demod', [status(thm)], ['90', '91', '92', '93'])).
% 0.91/1.15  thf('95', plain, ($false), inference('sup-', [status(thm)], ['0', '94'])).
% 0.91/1.15  
% 0.91/1.15  % SZS output end Refutation
% 0.91/1.15  
% 0.91/1.15  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
