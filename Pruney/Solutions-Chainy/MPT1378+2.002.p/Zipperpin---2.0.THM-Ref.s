%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HoG807GWJ1

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:45 EST 2020

% Result     : Theorem 0.84s
% Output     : Refutation 0.84s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 185 expanded)
%              Number of leaves         :   25 (  62 expanded)
%              Depth                    :   16
%              Number of atoms          :  851 (3201 expanded)
%              Number of equality atoms :   22 (  49 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t3_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( m1_connsp_2 @ C @ A @ B )
                      & ( m1_connsp_2 @ D @ A @ B ) )
                   => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( m1_connsp_2 @ C @ A @ B )
                        & ( m1_connsp_2 @ D @ A @ B ) )
                     => ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_connsp_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ ( k4_subset_1 @ X13 @ X12 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) )
      | ( ( k4_subset_1 @ X16 @ X15 @ X17 )
        = ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('14',plain,(
    m1_subset_1 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ X0 )
        = ( k2_xboole_0 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_C )
    = ( k2_xboole_0 @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( r1_tarski @ X18 @ X20 )
      | ( r1_tarski @ ( k1_tops_1 @ X19 @ X18 ) @ ( k1_tops_1 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_C @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ sk_C @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('26',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['24'])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ X0 ) )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['22','30','31'])).

thf('33',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','32'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_tarski @ X10 @ ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
    = ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_connsp_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ( r2_hidden @ X21 @ ( k1_tops_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) )
      | ~ ( m1_connsp_2 @ sk_C @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X5 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('51',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    r2_hidden @ sk_B @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['37','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf('55',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r2_hidden @ X21 @ ( k1_tops_1 @ X22 @ X23 ) )
      | ( m1_connsp_2 @ X23 @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d1_connsp_2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tops_1 @ sk_A @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( m1_connsp_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_C @ sk_D_1 )
    = ( k2_xboole_0 @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('65',plain,(
    ~ ( m1_connsp_2 @ ( k2_xboole_0 @ sk_C @ sk_D_1 ) @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    v2_struct_0 @ sk_A ),
    inference(clc,[status(thm)],['62','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HoG807GWJ1
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:33 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.84/1.01  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.84/1.01  % Solved by: fo/fo7.sh
% 0.84/1.01  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.84/1.01  % done 746 iterations in 0.548s
% 0.84/1.01  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.84/1.01  % SZS output start Refutation
% 0.84/1.01  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.84/1.01  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.84/1.01  thf(m1_connsp_2_type, type, m1_connsp_2: $i > $i > $i > $o).
% 0.84/1.01  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.84/1.01  thf(sk_A_type, type, sk_A: $i).
% 0.84/1.01  thf(sk_C_type, type, sk_C: $i).
% 0.84/1.01  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.84/1.01  thf(sk_B_type, type, sk_B: $i).
% 0.84/1.01  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.84/1.01  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.84/1.01  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.84/1.01  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.84/1.01  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.84/1.01  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.84/1.01  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.84/1.01  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.84/1.01  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.84/1.01  thf(t3_connsp_2, conjecture,
% 0.84/1.01    (![A:$i]:
% 0.84/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.01       ( ![B:$i]:
% 0.84/1.01         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.01           ( ![C:$i]:
% 0.84/1.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.01               ( ![D:$i]:
% 0.84/1.01                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.01                   ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.84/1.01                       ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.84/1.01                     ( m1_connsp_2 @
% 0.84/1.01                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ))).
% 0.84/1.01  thf(zf_stmt_0, negated_conjecture,
% 0.84/1.01    (~( ![A:$i]:
% 0.84/1.01        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.84/1.01            ( l1_pre_topc @ A ) ) =>
% 0.84/1.01          ( ![B:$i]:
% 0.84/1.01            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.01              ( ![C:$i]:
% 0.84/1.01                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.01                  ( ![D:$i]:
% 0.84/1.01                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.01                      ( ( ( m1_connsp_2 @ C @ A @ B ) & 
% 0.84/1.01                          ( m1_connsp_2 @ D @ A @ B ) ) =>
% 0.84/1.01                        ( m1_connsp_2 @
% 0.84/1.01                          ( k4_subset_1 @ ( u1_struct_0 @ A ) @ C @ D ) @ A @ B ) ) ) ) ) ) ) ) ) )),
% 0.84/1.01    inference('cnf.neg', [status(esa)], [t3_connsp_2])).
% 0.84/1.01  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('1', plain,
% 0.84/1.01      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('2', plain,
% 0.84/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf(dt_k4_subset_1, axiom,
% 0.84/1.01    (![A:$i,B:$i,C:$i]:
% 0.84/1.01     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.84/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.84/1.01       ( m1_subset_1 @ ( k4_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.84/1.01  thf('3', plain,
% 0.84/1.01      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.84/1.01         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.84/1.01          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13))
% 0.84/1.01          | (m1_subset_1 @ (k4_subset_1 @ X13 @ X12 @ X14) @ 
% 0.84/1.01             (k1_zfmisc_1 @ X13)))),
% 0.84/1.01      inference('cnf', [status(esa)], [dt_k4_subset_1])).
% 0.84/1.01  thf('4', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.84/1.01           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.84/1.01  thf('5', plain,
% 0.84/1.01      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 0.84/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('sup-', [status(thm)], ['1', '4'])).
% 0.84/1.01  thf('6', plain,
% 0.84/1.01      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('7', plain,
% 0.84/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf(redefinition_k4_subset_1, axiom,
% 0.84/1.01    (![A:$i,B:$i,C:$i]:
% 0.84/1.01     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.84/1.01         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.84/1.01       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.84/1.01  thf('8', plain,
% 0.84/1.01      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.84/1.01         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.84/1.01          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16))
% 0.84/1.01          | ((k4_subset_1 @ X16 @ X15 @ X17) = (k2_xboole_0 @ X15 @ X17)))),
% 0.84/1.01      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.84/1.01  thf('9', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.84/1.01            = (k2_xboole_0 @ sk_C @ X0))
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.01  thf('10', plain,
% 0.84/1.01      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 0.84/1.01         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 0.84/1.01      inference('sup-', [status(thm)], ['6', '9'])).
% 0.84/1.01  thf('11', plain,
% 0.84/1.01      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 0.84/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('demod', [status(thm)], ['5', '10'])).
% 0.84/1.01  thf('12', plain,
% 0.84/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('13', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0) @ 
% 0.84/1.01           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.01      inference('sup-', [status(thm)], ['2', '3'])).
% 0.84/1.01  thf('14', plain,
% 0.84/1.01      ((m1_subset_1 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C) @ 
% 0.84/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('sup-', [status(thm)], ['12', '13'])).
% 0.84/1.01  thf('15', plain,
% 0.84/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('16', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ X0)
% 0.84/1.01            = (k2_xboole_0 @ sk_C @ X0))
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.84/1.01      inference('sup-', [status(thm)], ['7', '8'])).
% 0.84/1.01  thf('17', plain,
% 0.84/1.01      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_C)
% 0.84/1.01         = (k2_xboole_0 @ sk_C @ sk_C))),
% 0.84/1.01      inference('sup-', [status(thm)], ['15', '16'])).
% 0.84/1.01  thf('18', plain,
% 0.84/1.01      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_C) @ 
% 0.84/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('demod', [status(thm)], ['14', '17'])).
% 0.84/1.01  thf(t48_tops_1, axiom,
% 0.84/1.01    (![A:$i]:
% 0.84/1.01     ( ( l1_pre_topc @ A ) =>
% 0.84/1.01       ( ![B:$i]:
% 0.84/1.01         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.01           ( ![C:$i]:
% 0.84/1.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.01               ( ( r1_tarski @ B @ C ) =>
% 0.84/1.01                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.84/1.01  thf('19', plain,
% 0.84/1.01      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.84/1.01         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.84/1.01          | ~ (r1_tarski @ X18 @ X20)
% 0.84/1.01          | (r1_tarski @ (k1_tops_1 @ X19 @ X18) @ (k1_tops_1 @ X19 @ X20))
% 0.84/1.01          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.84/1.01          | ~ (l1_pre_topc @ X19))),
% 0.84/1.01      inference('cnf', [status(esa)], [t48_tops_1])).
% 0.84/1.01  thf('20', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (~ (l1_pre_topc @ sk_A)
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.01          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_C)) @ 
% 0.84/1.01             (k1_tops_1 @ sk_A @ X0))
% 0.84/1.01          | ~ (r1_tarski @ (k2_xboole_0 @ sk_C @ sk_C) @ X0))),
% 0.84/1.01      inference('sup-', [status(thm)], ['18', '19'])).
% 0.84/1.01  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('22', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.01          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_C)) @ 
% 0.84/1.01             (k1_tops_1 @ sk_A @ X0))
% 0.84/1.01          | ~ (r1_tarski @ (k2_xboole_0 @ sk_C @ sk_C) @ X0))),
% 0.84/1.01      inference('demod', [status(thm)], ['20', '21'])).
% 0.84/1.01  thf(d3_xboole_0, axiom,
% 0.84/1.01    (![A:$i,B:$i,C:$i]:
% 0.84/1.01     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.84/1.01       ( ![D:$i]:
% 0.84/1.01         ( ( r2_hidden @ D @ C ) <=>
% 0.84/1.01           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.84/1.01  thf('23', plain,
% 0.84/1.01      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.01         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.01          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.84/1.01          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.84/1.01          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.01      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.01  thf('24', plain,
% 0.84/1.01      (![X0 : $i, X1 : $i]:
% 0.84/1.01         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.84/1.01          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.84/1.01          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 0.84/1.01      inference('eq_fact', [status(thm)], ['23'])).
% 0.84/1.01  thf('25', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.84/1.01          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 0.84/1.01      inference('eq_fact', [status(thm)], ['24'])).
% 0.84/1.01  thf('26', plain,
% 0.84/1.01      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.84/1.01         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.84/1.01          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.84/1.01          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.84/1.01      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.01  thf('27', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.84/1.01          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.84/1.01          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 0.84/1.01      inference('sup-', [status(thm)], ['25', '26'])).
% 0.84/1.01  thf('28', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.84/1.01          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 0.84/1.01      inference('simplify', [status(thm)], ['27'])).
% 0.84/1.01  thf('29', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.84/1.01          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 0.84/1.01      inference('eq_fact', [status(thm)], ['24'])).
% 0.84/1.01  thf('30', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.84/1.01      inference('clc', [status(thm)], ['28', '29'])).
% 0.84/1.01  thf('31', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.84/1.01      inference('clc', [status(thm)], ['28', '29'])).
% 0.84/1.01  thf('32', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.84/1.01          | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ (k1_tops_1 @ sk_A @ X0))
% 0.84/1.01          | ~ (r1_tarski @ sk_C @ X0))),
% 0.84/1.01      inference('demod', [status(thm)], ['22', '30', '31'])).
% 0.84/1.01  thf('33', plain,
% 0.84/1.01      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ sk_C @ sk_D_1))
% 0.84/1.01        | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.84/1.01           (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1))))),
% 0.84/1.01      inference('sup-', [status(thm)], ['11', '32'])).
% 0.84/1.01  thf(t7_xboole_1, axiom,
% 0.84/1.01    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.84/1.01  thf('34', plain,
% 0.84/1.01      (![X10 : $i, X11 : $i]: (r1_tarski @ X10 @ (k2_xboole_0 @ X10 @ X11))),
% 0.84/1.01      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.84/1.01  thf('35', plain,
% 0.84/1.01      ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.84/1.01        (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.84/1.01      inference('demod', [status(thm)], ['33', '34'])).
% 0.84/1.01  thf(t12_xboole_1, axiom,
% 0.84/1.01    (![A:$i,B:$i]:
% 0.84/1.01     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.84/1.01  thf('36', plain,
% 0.84/1.01      (![X8 : $i, X9 : $i]:
% 0.84/1.01         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.84/1.01      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.84/1.01  thf('37', plain,
% 0.84/1.01      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ 
% 0.84/1.01         (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 0.84/1.01         = (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.84/1.01      inference('sup-', [status(thm)], ['35', '36'])).
% 0.84/1.01  thf('38', plain, ((m1_connsp_2 @ sk_C @ sk_A @ sk_B)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('39', plain,
% 0.84/1.01      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf(d1_connsp_2, axiom,
% 0.84/1.01    (![A:$i]:
% 0.84/1.01     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.84/1.01       ( ![B:$i]:
% 0.84/1.01         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.84/1.01           ( ![C:$i]:
% 0.84/1.01             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.84/1.01               ( ( m1_connsp_2 @ C @ A @ B ) <=>
% 0.84/1.01                 ( r2_hidden @ B @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 0.84/1.01  thf('40', plain,
% 0.84/1.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.84/1.01         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.84/1.01          | ~ (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.84/1.01          | (r2_hidden @ X21 @ (k1_tops_1 @ X22 @ X23))
% 0.84/1.01          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.84/1.01          | ~ (l1_pre_topc @ X22)
% 0.84/1.01          | ~ (v2_pre_topc @ X22)
% 0.84/1.01          | (v2_struct_0 @ X22))),
% 0.84/1.01      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.84/1.01  thf('41', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         ((v2_struct_0 @ sk_A)
% 0.84/1.01          | ~ (v2_pre_topc @ sk_A)
% 0.84/1.01          | ~ (l1_pre_topc @ sk_A)
% 0.84/1.01          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.84/1.01          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('sup-', [status(thm)], ['39', '40'])).
% 0.84/1.01  thf('42', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('44', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         ((v2_struct_0 @ sk_A)
% 0.84/1.01          | (r2_hidden @ X0 @ (k1_tops_1 @ sk_A @ sk_C))
% 0.84/1.01          | ~ (m1_connsp_2 @ sk_C @ sk_A @ X0)
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.84/1.01  thf('45', plain,
% 0.84/1.01      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.84/1.01        | (r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))
% 0.84/1.01        | (v2_struct_0 @ sk_A))),
% 0.84/1.01      inference('sup-', [status(thm)], ['38', '44'])).
% 0.84/1.01  thf('46', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('47', plain,
% 0.84/1.01      (((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C)) | (v2_struct_0 @ sk_A))),
% 0.84/1.01      inference('demod', [status(thm)], ['45', '46'])).
% 0.84/1.01  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('49', plain, ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ sk_C))),
% 0.84/1.01      inference('clc', [status(thm)], ['47', '48'])).
% 0.84/1.01  thf('50', plain,
% 0.84/1.01      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.84/1.01         (~ (r2_hidden @ X2 @ X5)
% 0.84/1.01          | (r2_hidden @ X2 @ X4)
% 0.84/1.01          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.84/1.01      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.84/1.01  thf('51', plain,
% 0.84/1.01      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.84/1.01         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X5))),
% 0.84/1.01      inference('simplify', [status(thm)], ['50'])).
% 0.84/1.01  thf('52', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         (r2_hidden @ sk_B @ (k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ X0))),
% 0.84/1.01      inference('sup-', [status(thm)], ['49', '51'])).
% 0.84/1.01  thf('53', plain,
% 0.84/1.01      ((r2_hidden @ sk_B @ (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))),
% 0.84/1.01      inference('sup+', [status(thm)], ['37', '52'])).
% 0.84/1.01  thf('54', plain,
% 0.84/1.01      ((m1_subset_1 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ 
% 0.84/1.01        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('demod', [status(thm)], ['5', '10'])).
% 0.84/1.01  thf('55', plain,
% 0.84/1.01      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.84/1.01         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.84/1.01          | ~ (r2_hidden @ X21 @ (k1_tops_1 @ X22 @ X23))
% 0.84/1.01          | (m1_connsp_2 @ X23 @ X22 @ X21)
% 0.84/1.01          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.84/1.01          | ~ (l1_pre_topc @ X22)
% 0.84/1.01          | ~ (v2_pre_topc @ X22)
% 0.84/1.01          | (v2_struct_0 @ X22))),
% 0.84/1.01      inference('cnf', [status(esa)], [d1_connsp_2])).
% 0.84/1.01  thf('56', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         ((v2_struct_0 @ sk_A)
% 0.84/1.01          | ~ (v2_pre_topc @ sk_A)
% 0.84/1.01          | ~ (l1_pre_topc @ sk_A)
% 0.84/1.01          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ X0)
% 0.84/1.01          | ~ (r2_hidden @ X0 @ 
% 0.84/1.01               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('sup-', [status(thm)], ['54', '55'])).
% 0.84/1.01  thf('57', plain, ((v2_pre_topc @ sk_A)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('59', plain,
% 0.84/1.01      (![X0 : $i]:
% 0.84/1.01         ((v2_struct_0 @ sk_A)
% 0.84/1.01          | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ X0)
% 0.84/1.01          | ~ (r2_hidden @ X0 @ 
% 0.84/1.01               (k1_tops_1 @ sk_A @ (k2_xboole_0 @ sk_C @ sk_D_1)))
% 0.84/1.01          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.84/1.01      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.84/1.01  thf('60', plain,
% 0.84/1.01      ((~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.84/1.01        | (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 0.84/1.01        | (v2_struct_0 @ sk_A))),
% 0.84/1.01      inference('sup-', [status(thm)], ['53', '59'])).
% 0.84/1.01  thf('61', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('62', plain,
% 0.84/1.01      (((m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)
% 0.84/1.01        | (v2_struct_0 @ sk_A))),
% 0.84/1.01      inference('demod', [status(thm)], ['60', '61'])).
% 0.84/1.01  thf('63', plain,
% 0.84/1.01      (~ (m1_connsp_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1) @ 
% 0.84/1.01          sk_A @ sk_B)),
% 0.84/1.01      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.84/1.01  thf('64', plain,
% 0.84/1.01      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_C @ sk_D_1)
% 0.84/1.01         = (k2_xboole_0 @ sk_C @ sk_D_1))),
% 0.84/1.01      inference('sup-', [status(thm)], ['6', '9'])).
% 0.84/1.01  thf('65', plain,
% 0.84/1.01      (~ (m1_connsp_2 @ (k2_xboole_0 @ sk_C @ sk_D_1) @ sk_A @ sk_B)),
% 0.84/1.01      inference('demod', [status(thm)], ['63', '64'])).
% 0.84/1.01  thf('66', plain, ((v2_struct_0 @ sk_A)),
% 0.84/1.01      inference('clc', [status(thm)], ['62', '65'])).
% 0.84/1.01  thf('67', plain, ($false), inference('demod', [status(thm)], ['0', '66'])).
% 0.84/1.01  
% 0.84/1.01  % SZS output end Refutation
% 0.84/1.01  
% 0.84/1.02  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
