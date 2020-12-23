%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iyR87nz9Iv

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:33 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 153 expanded)
%              Number of leaves         :   30 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :  643 (1473 expanded)
%              Number of equality atoms :   23 (  62 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(t33_tops_2,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_pre_topc @ C @ A )
               => ( ( v3_pre_topc @ B @ A )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                     => ( ( D = B )
                       => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tops_2])).

thf('0',plain,(
    ~ ( v3_pre_topc @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( v3_pre_topc @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('3',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('7',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t32_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( v3_pre_topc @ C @ B )
              <=> ? [D: $i] :
                    ( ( ( k9_subset_1 @ ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) )
                      = C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_pre_topc @ X23 @ X24 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) )
       != X25 )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( v3_pre_topc @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t32_tops_2])).

thf('9',plain,(
    ! [X23: $i,X24: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X23 ) @ X26 @ ( k2_struct_0 @ X23 ) ) @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v3_pre_topc @ X26 @ X24 )
      | ~ ( m1_pre_topc @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k9_subset_1 @ ( k2_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('14',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k9_subset_1 @ X16 @ X14 @ X15 )
        = ( k3_xboole_0 @ X14 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X2 )
      | ~ ( v3_pre_topc @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X2 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_B @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ sk_B @ ( k2_struct_0 @ X0 ) ) @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','27'])).

thf('29',plain,(
    m1_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('30',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_pre_topc @ X21 @ X22 )
      | ( l1_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    l1_pre_topc @ sk_C_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('34',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('35',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v3_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,
    ( ( v3_pre_topc @ ( k9_subset_1 @ ( k2_struct_0 @ sk_C_1 ) @ sk_B @ ( k2_struct_0 @ sk_C_1 ) ) @ sk_C_1 )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['3','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('39',plain,(
    ! [X19: $i] :
      ( ( ( k2_struct_0 @ X19 )
        = ( u1_struct_0 @ X19 ) )
      | ~ ( l1_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    sk_D_1 = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,
    ( ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['48'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('50',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,
    ( ( k3_xboole_0 @ sk_B @ ( u1_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
      = sk_B )
    | ~ ( l1_struct_0 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['39','51'])).

thf('53',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('54',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k2_struct_0 @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    l1_struct_0 @ sk_C_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('56',plain,(
    v3_pre_topc @ sk_B @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38','54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['2','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iyR87nz9Iv
% 0.15/0.37  % Computer   : n021.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:18:49 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.44/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.71  % Solved by: fo/fo7.sh
% 0.44/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.71  % done 539 iterations in 0.222s
% 0.44/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.71  % SZS output start Refutation
% 0.44/0.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.71  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.44/0.71  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.44/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.71  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.44/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.71  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.44/0.71  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.44/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.71  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.44/0.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.71  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.44/0.71  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.44/0.71  thf(t33_tops_2, conjecture,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( l1_pre_topc @ A ) =>
% 0.44/0.71       ( ![B:$i]:
% 0.44/0.71         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.71           ( ![C:$i]:
% 0.44/0.71             ( ( m1_pre_topc @ C @ A ) =>
% 0.44/0.71               ( ( v3_pre_topc @ B @ A ) =>
% 0.44/0.71                 ( ![D:$i]:
% 0.44/0.71                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.44/0.71                     ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.71    (~( ![A:$i]:
% 0.44/0.71        ( ( l1_pre_topc @ A ) =>
% 0.44/0.71          ( ![B:$i]:
% 0.44/0.71            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.44/0.71              ( ![C:$i]:
% 0.44/0.71                ( ( m1_pre_topc @ C @ A ) =>
% 0.44/0.71                  ( ( v3_pre_topc @ B @ A ) =>
% 0.44/0.71                    ( ![D:$i]:
% 0.44/0.71                      ( ( m1_subset_1 @
% 0.44/0.71                          D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) ) =>
% 0.44/0.71                        ( ( ( D ) = ( B ) ) => ( v3_pre_topc @ D @ C ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.71    inference('cnf.neg', [status(esa)], [t33_tops_2])).
% 0.44/0.71  thf('0', plain, (~ (v3_pre_topc @ sk_D_1 @ sk_C_1)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('1', plain, (((sk_D_1) = (sk_B))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('2', plain, (~ (v3_pre_topc @ sk_B @ sk_C_1)),
% 0.44/0.71      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.71  thf(d3_struct_0, axiom,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.44/0.71  thf('3', plain,
% 0.44/0.71      (![X19 : $i]:
% 0.44/0.71         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.71  thf('4', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('5', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('6', plain,
% 0.44/0.71      (![X19 : $i]:
% 0.44/0.71         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.71  thf('7', plain,
% 0.44/0.71      (![X19 : $i]:
% 0.44/0.71         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.71  thf(t32_tops_2, axiom,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( l1_pre_topc @ A ) =>
% 0.44/0.71       ( ![B:$i]:
% 0.44/0.71         ( ( m1_pre_topc @ B @ A ) =>
% 0.44/0.71           ( ![C:$i]:
% 0.44/0.71             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.44/0.71               ( ( v3_pre_topc @ C @ B ) <=>
% 0.44/0.71                 ( ?[D:$i]:
% 0.44/0.71                   ( ( ( k9_subset_1 @
% 0.44/0.71                         ( u1_struct_0 @ B ) @ D @ ( k2_struct_0 @ B ) ) =
% 0.44/0.71                       ( C ) ) & 
% 0.44/0.71                     ( v3_pre_topc @ D @ A ) & 
% 0.44/0.71                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.71  thf('8', plain,
% 0.44/0.71      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.71         (~ (m1_pre_topc @ X23 @ X24)
% 0.44/0.71          | ((k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23))
% 0.44/0.71              != (X25))
% 0.44/0.71          | ~ (v3_pre_topc @ X26 @ X24)
% 0.44/0.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.44/0.71          | (v3_pre_topc @ X25 @ X23)
% 0.44/0.71          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.44/0.71          | ~ (l1_pre_topc @ X24))),
% 0.44/0.71      inference('cnf', [status(esa)], [t32_tops_2])).
% 0.44/0.71  thf('9', plain,
% 0.44/0.71      (![X23 : $i, X24 : $i, X26 : $i]:
% 0.44/0.71         (~ (l1_pre_topc @ X24)
% 0.44/0.71          | ~ (m1_subset_1 @ 
% 0.44/0.71               (k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23)) @ 
% 0.44/0.71               (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 0.44/0.71          | (v3_pre_topc @ 
% 0.44/0.71             (k9_subset_1 @ (u1_struct_0 @ X23) @ X26 @ (k2_struct_0 @ X23)) @ 
% 0.44/0.71             X23)
% 0.44/0.71          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.44/0.71          | ~ (v3_pre_topc @ X26 @ X24)
% 0.44/0.71          | ~ (m1_pre_topc @ X23 @ X24))),
% 0.44/0.71      inference('simplify', [status(thm)], ['8'])).
% 0.44/0.71  thf('10', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ 
% 0.44/0.71             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ 
% 0.44/0.71             (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.44/0.71          | ~ (l1_struct_0 @ X0)
% 0.44/0.71          | ~ (m1_pre_topc @ X0 @ X2)
% 0.44/0.71          | ~ (v3_pre_topc @ X1 @ X2)
% 0.44/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.44/0.71          | (v3_pre_topc @ 
% 0.44/0.71             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 0.44/0.71          | ~ (l1_pre_topc @ X2))),
% 0.44/0.71      inference('sup-', [status(thm)], ['7', '9'])).
% 0.44/0.71  thf('11', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (~ (m1_subset_1 @ 
% 0.44/0.71             (k9_subset_1 @ (k2_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ 
% 0.44/0.71             (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.44/0.71          | ~ (l1_struct_0 @ X0)
% 0.44/0.71          | ~ (l1_pre_topc @ X2)
% 0.44/0.71          | (v3_pre_topc @ 
% 0.44/0.71             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 0.44/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.44/0.71          | ~ (v3_pre_topc @ X1 @ X2)
% 0.44/0.71          | ~ (m1_pre_topc @ X0 @ X2)
% 0.44/0.71          | ~ (l1_struct_0 @ X0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['6', '10'])).
% 0.44/0.71  thf(dt_k2_subset_1, axiom,
% 0.44/0.71    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.44/0.71  thf('12', plain,
% 0.44/0.71      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.44/0.71      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.44/0.71  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.44/0.71  thf('13', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.44/0.71      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.44/0.71  thf('14', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.44/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.71  thf(redefinition_k9_subset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.71       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.44/0.71  thf('15', plain,
% 0.44/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.71         (((k9_subset_1 @ X16 @ X14 @ X15) = (k3_xboole_0 @ X14 @ X15))
% 0.44/0.71          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.44/0.71      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.44/0.71  thf('16', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.71  thf('17', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.44/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.71  thf(dt_k9_subset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i,C:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.71       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.44/0.71  thf('18', plain,
% 0.44/0.71      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.44/0.71         ((m1_subset_1 @ (k9_subset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X8))
% 0.44/0.71          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X8)))),
% 0.44/0.71      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.44/0.71  thf('19', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.71  thf('20', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.71  thf('21', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['19', '20'])).
% 0.44/0.71  thf('22', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (~ (l1_struct_0 @ X0)
% 0.44/0.71          | ~ (l1_pre_topc @ X2)
% 0.44/0.71          | (v3_pre_topc @ 
% 0.44/0.71             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 0.44/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.44/0.71          | ~ (v3_pre_topc @ X1 @ X2)
% 0.44/0.71          | ~ (m1_pre_topc @ X0 @ X2)
% 0.44/0.71          | ~ (l1_struct_0 @ X0))),
% 0.44/0.71      inference('demod', [status(thm)], ['11', '16', '21'])).
% 0.44/0.71  thf('23', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (~ (m1_pre_topc @ X0 @ X2)
% 0.44/0.71          | ~ (v3_pre_topc @ X1 @ X2)
% 0.44/0.71          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X2)))
% 0.44/0.71          | (v3_pre_topc @ 
% 0.44/0.71             (k9_subset_1 @ (u1_struct_0 @ X0) @ X1 @ (k2_struct_0 @ X0)) @ X0)
% 0.44/0.71          | ~ (l1_pre_topc @ X2)
% 0.44/0.71          | ~ (l1_struct_0 @ X0))),
% 0.44/0.71      inference('simplify', [status(thm)], ['22'])).
% 0.44/0.71  thf('24', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (l1_struct_0 @ X0)
% 0.44/0.71          | ~ (l1_pre_topc @ sk_A)
% 0.44/0.71          | (v3_pre_topc @ 
% 0.44/0.71             (k9_subset_1 @ (u1_struct_0 @ X0) @ sk_B @ (k2_struct_0 @ X0)) @ 
% 0.44/0.71             X0)
% 0.44/0.71          | ~ (v3_pre_topc @ sk_B @ sk_A)
% 0.44/0.71          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.44/0.71      inference('sup-', [status(thm)], ['5', '23'])).
% 0.44/0.71  thf('25', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('26', plain, ((v3_pre_topc @ sk_B @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('27', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         (~ (l1_struct_0 @ X0)
% 0.44/0.71          | (v3_pre_topc @ 
% 0.44/0.71             (k9_subset_1 @ (u1_struct_0 @ X0) @ sk_B @ (k2_struct_0 @ X0)) @ 
% 0.44/0.71             X0)
% 0.44/0.71          | ~ (m1_pre_topc @ X0 @ sk_A))),
% 0.44/0.71      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.44/0.71  thf('28', plain,
% 0.44/0.71      (((v3_pre_topc @ 
% 0.44/0.71         (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ (k2_struct_0 @ sk_C_1)) @ 
% 0.44/0.71         sk_C_1)
% 0.44/0.71        | ~ (l1_struct_0 @ sk_C_1))),
% 0.44/0.71      inference('sup-', [status(thm)], ['4', '27'])).
% 0.44/0.71  thf('29', plain, ((m1_pre_topc @ sk_C_1 @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf(dt_m1_pre_topc, axiom,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( l1_pre_topc @ A ) =>
% 0.44/0.71       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.44/0.71  thf('30', plain,
% 0.44/0.71      (![X21 : $i, X22 : $i]:
% 0.44/0.71         (~ (m1_pre_topc @ X21 @ X22)
% 0.44/0.71          | (l1_pre_topc @ X21)
% 0.44/0.71          | ~ (l1_pre_topc @ X22))),
% 0.44/0.71      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.44/0.71  thf('31', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_C_1))),
% 0.44/0.71      inference('sup-', [status(thm)], ['29', '30'])).
% 0.44/0.71  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('33', plain, ((l1_pre_topc @ sk_C_1)),
% 0.44/0.71      inference('demod', [status(thm)], ['31', '32'])).
% 0.44/0.71  thf(dt_l1_pre_topc, axiom,
% 0.44/0.71    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.44/0.71  thf('34', plain,
% 0.44/0.71      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.44/0.71      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.44/0.71  thf('35', plain, ((l1_struct_0 @ sk_C_1)),
% 0.44/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.71  thf('36', plain,
% 0.44/0.71      ((v3_pre_topc @ 
% 0.44/0.71        (k9_subset_1 @ (u1_struct_0 @ sk_C_1) @ sk_B @ (k2_struct_0 @ sk_C_1)) @ 
% 0.44/0.71        sk_C_1)),
% 0.44/0.71      inference('demod', [status(thm)], ['28', '35'])).
% 0.44/0.71  thf('37', plain,
% 0.44/0.71      (((v3_pre_topc @ 
% 0.44/0.71         (k9_subset_1 @ (k2_struct_0 @ sk_C_1) @ sk_B @ (k2_struct_0 @ sk_C_1)) @ 
% 0.44/0.71         sk_C_1)
% 0.44/0.71        | ~ (l1_struct_0 @ sk_C_1))),
% 0.44/0.71      inference('sup+', [status(thm)], ['3', '36'])).
% 0.44/0.71  thf('38', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.44/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.71  thf('39', plain,
% 0.44/0.71      (![X19 : $i]:
% 0.44/0.71         (((k2_struct_0 @ X19) = (u1_struct_0 @ X19)) | ~ (l1_struct_0 @ X19))),
% 0.44/0.71      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.44/0.71  thf(d3_tarski, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.71  thf('40', plain,
% 0.44/0.71      (![X1 : $i, X3 : $i]:
% 0.44/0.71         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.44/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.71  thf('41', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('42', plain, (((sk_D_1) = (sk_B))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('43', plain,
% 0.44/0.71      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_C_1)))),
% 0.44/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.44/0.71  thf(l3_subset_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.71       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.44/0.71  thf('44', plain,
% 0.44/0.71      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.44/0.71         (~ (r2_hidden @ X11 @ X12)
% 0.44/0.71          | (r2_hidden @ X11 @ X13)
% 0.44/0.71          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.44/0.71      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.44/0.71  thf('45', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.44/0.71         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_C_1)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.44/0.71      inference('sup-', [status(thm)], ['43', '44'])).
% 0.44/0.71  thf('46', plain,
% 0.44/0.71      (![X0 : $i]:
% 0.54/0.71         ((r1_tarski @ sk_B @ X0)
% 0.54/0.71          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (u1_struct_0 @ sk_C_1)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['40', '45'])).
% 0.54/0.71  thf('47', plain,
% 0.54/0.71      (![X1 : $i, X3 : $i]:
% 0.54/0.71         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.54/0.71      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.71  thf('48', plain,
% 0.54/0.71      (((r1_tarski @ sk_B @ (u1_struct_0 @ sk_C_1))
% 0.54/0.71        | (r1_tarski @ sk_B @ (u1_struct_0 @ sk_C_1)))),
% 0.54/0.71      inference('sup-', [status(thm)], ['46', '47'])).
% 0.54/0.71  thf('49', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_C_1))),
% 0.54/0.71      inference('simplify', [status(thm)], ['48'])).
% 0.54/0.71  thf(t28_xboole_1, axiom,
% 0.54/0.71    (![A:$i,B:$i]:
% 0.54/0.71     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.71  thf('50', plain,
% 0.54/0.71      (![X4 : $i, X5 : $i]:
% 0.54/0.71         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.54/0.71      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.71  thf('51', plain, (((k3_xboole_0 @ sk_B @ (u1_struct_0 @ sk_C_1)) = (sk_B))),
% 0.54/0.71      inference('sup-', [status(thm)], ['49', '50'])).
% 0.54/0.71  thf('52', plain,
% 0.54/0.71      ((((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))
% 0.54/0.71        | ~ (l1_struct_0 @ sk_C_1))),
% 0.54/0.71      inference('sup+', [status(thm)], ['39', '51'])).
% 0.54/0.71  thf('53', plain, ((l1_struct_0 @ sk_C_1)),
% 0.54/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.71  thf('54', plain, (((k3_xboole_0 @ sk_B @ (k2_struct_0 @ sk_C_1)) = (sk_B))),
% 0.54/0.71      inference('demod', [status(thm)], ['52', '53'])).
% 0.54/0.71  thf('55', plain, ((l1_struct_0 @ sk_C_1)),
% 0.54/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.54/0.71  thf('56', plain, ((v3_pre_topc @ sk_B @ sk_C_1)),
% 0.54/0.71      inference('demod', [status(thm)], ['37', '38', '54', '55'])).
% 0.54/0.71  thf('57', plain, ($false), inference('demod', [status(thm)], ['2', '56'])).
% 0.54/0.71  
% 0.54/0.71  % SZS output end Refutation
% 0.54/0.71  
% 0.54/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
