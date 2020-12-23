%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7BdFZzI6zv

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:26 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 201 expanded)
%              Number of leaves         :   28 (  74 expanded)
%              Depth                    :   20
%              Number of atoms          :  688 (1595 expanded)
%              Number of equality atoms :   42 (  76 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

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

thf('0',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
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

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( r1_tarski @ ( sk_C @ X18 @ X19 ) @ X18 )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( r1_tarski @ ( sk_C @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','23'])).

thf(rc2_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v4_pre_topc @ B @ A )
          & ( v3_pre_topc @ B @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('25',plain,(
    ! [X17: $i] :
      ( ( v4_pre_topc @ ( sk_B @ X17 ) @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc2_tops_1])).

thf('26',plain,(
    ! [X17: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X17 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[rc2_tops_1])).

thf('27',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( v4_pre_topc @ X21 @ X19 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X19 ) @ X18 @ X21 )
       != ( sk_C @ X18 @ X19 ) )
      | ( v2_tex_2 @ X18 @ X19 )
      | ~ ( l1_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 @ X1 )
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k9_subset_1 @ X2 @ X4 @ X3 )
        = ( k9_subset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k9_subset_1 @ X10 @ X8 @ X9 )
        = ( k3_xboole_0 @ X8 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k9_subset_1 @ X0 @ X2 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','53'])).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('56',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('58',plain,(
    ! [X1: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['29','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( v4_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( k1_xboole_0
       != ( sk_C @ k1_xboole_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('69',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68','69','70'])).

thf('72',plain,(
    v2_tex_2 @ k1_xboole_0 @ sk_A ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['4','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7BdFZzI6zv
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 17:00:51 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.78/1.03  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.78/1.03  % Solved by: fo/fo7.sh
% 0.78/1.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/1.03  % done 950 iterations in 0.599s
% 0.78/1.03  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.78/1.03  % SZS output start Refutation
% 0.78/1.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/1.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/1.03  thf(sk_A_type, type, sk_A: $i).
% 0.78/1.03  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.78/1.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.78/1.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/1.03  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.78/1.03  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.78/1.03  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.78/1.03  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.78/1.03  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.78/1.03  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.78/1.03  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.78/1.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.78/1.03  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.86/1.03  thf(sk_B_type, type, sk_B: $i > $i).
% 0.86/1.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.86/1.03  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.86/1.03  thf(t35_tex_2, conjecture,
% 0.86/1.03    (![A:$i]:
% 0.86/1.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.86/1.03       ( ![B:$i]:
% 0.86/1.03         ( ( ( v1_xboole_0 @ B ) & 
% 0.86/1.03             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.86/1.03           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.86/1.03  thf(zf_stmt_0, negated_conjecture,
% 0.86/1.03    (~( ![A:$i]:
% 0.86/1.03        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.86/1.03            ( l1_pre_topc @ A ) ) =>
% 0.86/1.03          ( ![B:$i]:
% 0.86/1.03            ( ( ( v1_xboole_0 @ B ) & 
% 0.86/1.03                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.86/1.03              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.86/1.03    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.86/1.03  thf('0', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.86/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.03  thf('1', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.86/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.03  thf(l13_xboole_0, axiom,
% 0.86/1.03    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.86/1.03  thf('2', plain,
% 0.86/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.86/1.03  thf('3', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.86/1.03  thf('4', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.86/1.03      inference('demod', [status(thm)], ['0', '3'])).
% 0.86/1.03  thf('5', plain,
% 0.86/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.86/1.03  thf(t4_subset_1, axiom,
% 0.86/1.03    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.86/1.03  thf('6', plain,
% 0.86/1.03      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.86/1.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.86/1.03  thf(d6_tex_2, axiom,
% 0.86/1.03    (![A:$i]:
% 0.86/1.03     ( ( l1_pre_topc @ A ) =>
% 0.86/1.03       ( ![B:$i]:
% 0.86/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.03           ( ( v2_tex_2 @ B @ A ) <=>
% 0.86/1.03             ( ![C:$i]:
% 0.86/1.03               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.03                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.86/1.03                      ( ![D:$i]:
% 0.86/1.03                        ( ( m1_subset_1 @
% 0.86/1.03                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.86/1.03                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.86/1.03                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.86/1.03                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.86/1.03  thf('7', plain,
% 0.86/1.03      (![X18 : $i, X19 : $i]:
% 0.86/1.03         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.86/1.03          | (r1_tarski @ (sk_C @ X18 @ X19) @ X18)
% 0.86/1.03          | (v2_tex_2 @ X18 @ X19)
% 0.86/1.03          | ~ (l1_pre_topc @ X19))),
% 0.86/1.03      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.86/1.03  thf('8', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         (~ (l1_pre_topc @ X0)
% 0.86/1.03          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.86/1.03          | (r1_tarski @ (sk_C @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['6', '7'])).
% 0.86/1.03  thf('9', plain,
% 0.86/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.86/1.03  thf(t3_xboole_1, axiom,
% 0.86/1.03    (![A:$i]:
% 0.86/1.03     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.86/1.03  thf('10', plain,
% 0.86/1.03      (![X1 : $i]: (((X1) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ k1_xboole_0))),
% 0.86/1.03      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.86/1.03  thf('11', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (~ (r1_tarski @ X1 @ X0)
% 0.86/1.03          | ~ (v1_xboole_0 @ X0)
% 0.86/1.03          | ((X1) = (k1_xboole_0)))),
% 0.86/1.03      inference('sup-', [status(thm)], ['9', '10'])).
% 0.86/1.03  thf('12', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.86/1.03          | ~ (l1_pre_topc @ X0)
% 0.86/1.03          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.86/1.03          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['8', '11'])).
% 0.86/1.03  thf('13', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.86/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.03  thf('14', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['1', '2'])).
% 0.86/1.03  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.86/1.03  thf('16', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.86/1.03          | ~ (l1_pre_topc @ X0)
% 0.86/1.03          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.86/1.03      inference('demod', [status(thm)], ['12', '15'])).
% 0.86/1.03  thf('17', plain,
% 0.86/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.86/1.03  thf('18', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.86/1.03      inference('demod', [status(thm)], ['0', '3'])).
% 0.86/1.03  thf('19', plain,
% 0.86/1.03      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['17', '18'])).
% 0.86/1.03  thf('20', plain,
% 0.86/1.03      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 0.86/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.86/1.03        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['16', '19'])).
% 0.86/1.03  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.03  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.86/1.03  thf('23', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 0.86/1.03      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.86/1.03  thf('24', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('sup+', [status(thm)], ['5', '23'])).
% 0.86/1.03  thf(rc2_tops_1, axiom,
% 0.86/1.03    (![A:$i]:
% 0.86/1.03     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.86/1.03       ( ?[B:$i]:
% 0.86/1.03         ( ( v4_pre_topc @ B @ A ) & ( v3_pre_topc @ B @ A ) & 
% 0.86/1.03           ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.86/1.03  thf('25', plain,
% 0.86/1.03      (![X17 : $i]:
% 0.86/1.03         ((v4_pre_topc @ (sk_B @ X17) @ X17)
% 0.86/1.03          | ~ (l1_pre_topc @ X17)
% 0.86/1.03          | ~ (v2_pre_topc @ X17))),
% 0.86/1.03      inference('cnf', [status(esa)], [rc2_tops_1])).
% 0.86/1.03  thf('26', plain,
% 0.86/1.03      (![X17 : $i]:
% 0.86/1.03         ((m1_subset_1 @ (sk_B @ X17) @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.86/1.03          | ~ (l1_pre_topc @ X17)
% 0.86/1.03          | ~ (v2_pre_topc @ X17))),
% 0.86/1.03      inference('cnf', [status(esa)], [rc2_tops_1])).
% 0.86/1.03  thf('27', plain,
% 0.86/1.03      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.86/1.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.86/1.03  thf('28', plain,
% 0.86/1.03      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.86/1.03         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.86/1.03          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.86/1.03          | ~ (v4_pre_topc @ X21 @ X19)
% 0.86/1.03          | ((k9_subset_1 @ (u1_struct_0 @ X19) @ X18 @ X21)
% 0.86/1.03              != (sk_C @ X18 @ X19))
% 0.86/1.03          | (v2_tex_2 @ X18 @ X19)
% 0.86/1.03          | ~ (l1_pre_topc @ X19))),
% 0.86/1.03      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.86/1.03  thf('29', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (~ (l1_pre_topc @ X0)
% 0.86/1.03          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.86/1.03          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0 @ X1)
% 0.86/1.03              != (sk_C @ k1_xboole_0 @ X0))
% 0.86/1.03          | ~ (v4_pre_topc @ X1 @ X0)
% 0.86/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.86/1.03      inference('sup-', [status(thm)], ['27', '28'])).
% 0.86/1.03  thf('30', plain,
% 0.86/1.03      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.86/1.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.86/1.03  thf(commutativity_k9_subset_1, axiom,
% 0.86/1.03    (![A:$i,B:$i,C:$i]:
% 0.86/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.86/1.03       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 0.86/1.03  thf('31', plain,
% 0.86/1.03      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.86/1.03         (((k9_subset_1 @ X2 @ X4 @ X3) = (k9_subset_1 @ X2 @ X3 @ X4))
% 0.86/1.03          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X2)))),
% 0.86/1.03      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 0.86/1.03  thf('32', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.86/1.03           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.86/1.03      inference('sup-', [status(thm)], ['30', '31'])).
% 0.86/1.03  thf('33', plain,
% 0.86/1.03      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.86/1.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.86/1.03  thf(redefinition_k9_subset_1, axiom,
% 0.86/1.03    (![A:$i,B:$i,C:$i]:
% 0.86/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.86/1.03       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.86/1.03  thf('34', plain,
% 0.86/1.03      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.86/1.03         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.86/1.03          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.86/1.03      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.86/1.03  thf('35', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.86/1.03           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['33', '34'])).
% 0.86/1.03  thf('36', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.86/1.03           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.86/1.03      inference('demod', [status(thm)], ['32', '35'])).
% 0.86/1.03  thf('37', plain,
% 0.86/1.03      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.86/1.03      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.86/1.03  thf(dt_k9_subset_1, axiom,
% 0.86/1.03    (![A:$i,B:$i,C:$i]:
% 0.86/1.03     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.86/1.03       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.86/1.03  thf('38', plain,
% 0.86/1.03      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.86/1.03         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 0.86/1.03          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.86/1.03      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.86/1.03  thf('39', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ 
% 0.86/1.03          (k1_zfmisc_1 @ X0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['37', '38'])).
% 0.86/1.03  thf('40', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.86/1.03           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['33', '34'])).
% 0.86/1.03  thf('41', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (m1_subset_1 @ (k3_xboole_0 @ X1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.86/1.03      inference('demod', [status(thm)], ['39', '40'])).
% 0.86/1.03  thf('42', plain,
% 0.86/1.03      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.86/1.03         (((k9_subset_1 @ X10 @ X8 @ X9) = (k3_xboole_0 @ X8 @ X9))
% 0.86/1.03          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.86/1.03      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.86/1.03  thf('43', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.03         ((k9_subset_1 @ X0 @ X2 @ (k3_xboole_0 @ X1 @ k1_xboole_0))
% 0.86/1.03           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.86/1.03      inference('sup-', [status(thm)], ['41', '42'])).
% 0.86/1.03  thf('44', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         ((k3_xboole_0 @ X1 @ k1_xboole_0)
% 0.86/1.03           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.86/1.03      inference('demod', [status(thm)], ['32', '35'])).
% 0.86/1.03  thf('45', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.86/1.03           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.86/1.03      inference('sup+', [status(thm)], ['43', '44'])).
% 0.86/1.03  thf('46', plain,
% 0.86/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.86/1.03  thf('47', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0) @ 
% 0.86/1.03          (k1_zfmisc_1 @ X0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['37', '38'])).
% 0.86/1.03  thf(cc1_subset_1, axiom,
% 0.86/1.03    (![A:$i]:
% 0.86/1.03     ( ( v1_xboole_0 @ A ) =>
% 0.86/1.03       ( ![B:$i]:
% 0.86/1.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.86/1.03  thf('48', plain,
% 0.86/1.03      (![X12 : $i, X13 : $i]:
% 0.86/1.03         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.86/1.03          | (v1_xboole_0 @ X12)
% 0.86/1.03          | ~ (v1_xboole_0 @ X13))),
% 0.86/1.03      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.86/1.03  thf('49', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (~ (v1_xboole_0 @ X0)
% 0.86/1.03          | (v1_xboole_0 @ (k9_subset_1 @ X0 @ X1 @ k1_xboole_0)))),
% 0.86/1.03      inference('sup-', [status(thm)], ['47', '48'])).
% 0.86/1.03  thf('50', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.86/1.03           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['33', '34'])).
% 0.86/1.03  thf('51', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (~ (v1_xboole_0 @ X0)
% 0.86/1.03          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.86/1.03      inference('demod', [status(thm)], ['49', '50'])).
% 0.86/1.03  thf('52', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.86/1.03         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 0.86/1.03          | ~ (v1_xboole_0 @ X0)
% 0.86/1.03          | ~ (v1_xboole_0 @ X2))),
% 0.86/1.03      inference('sup+', [status(thm)], ['46', '51'])).
% 0.86/1.03  thf('53', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('condensation', [status(thm)], ['52'])).
% 0.86/1.03  thf('54', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         ((v1_xboole_0 @ 
% 0.86/1.03           (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))
% 0.86/1.03          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.86/1.03      inference('sup+', [status(thm)], ['45', '53'])).
% 0.86/1.03  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.86/1.03  thf('56', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         (v1_xboole_0 @ 
% 0.86/1.03          (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.86/1.03      inference('demod', [status(thm)], ['54', '55'])).
% 0.86/1.03  thf('57', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (~ (v1_xboole_0 @ X0)
% 0.86/1.03          | (v1_xboole_0 @ (k3_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.86/1.03      inference('demod', [status(thm)], ['49', '50'])).
% 0.86/1.03  thf('58', plain,
% 0.86/1.03      (![X1 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['56', '57'])).
% 0.86/1.03  thf('59', plain,
% 0.86/1.03      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.86/1.03      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.86/1.03  thf('60', plain,
% 0.86/1.03      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['58', '59'])).
% 0.86/1.03  thf('61', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 0.86/1.03      inference('demod', [status(thm)], ['36', '60'])).
% 0.86/1.03  thf('62', plain,
% 0.86/1.03      (![X0 : $i, X1 : $i]:
% 0.86/1.03         (~ (l1_pre_topc @ X0)
% 0.86/1.03          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.86/1.03          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.86/1.03          | ~ (v4_pre_topc @ X1 @ X0)
% 0.86/1.03          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.86/1.03      inference('demod', [status(thm)], ['29', '61'])).
% 0.86/1.03  thf('63', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         (~ (v2_pre_topc @ X0)
% 0.86/1.03          | ~ (l1_pre_topc @ X0)
% 0.86/1.03          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.86/1.03          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.86/1.03          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.86/1.03          | ~ (l1_pre_topc @ X0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['26', '62'])).
% 0.86/1.03  thf('64', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.86/1.03          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.86/1.03          | ~ (v4_pre_topc @ (sk_B @ X0) @ X0)
% 0.86/1.03          | ~ (l1_pre_topc @ X0)
% 0.86/1.03          | ~ (v2_pre_topc @ X0))),
% 0.86/1.03      inference('simplify', [status(thm)], ['63'])).
% 0.86/1.03  thf('65', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         (~ (v2_pre_topc @ X0)
% 0.86/1.03          | ~ (l1_pre_topc @ X0)
% 0.86/1.03          | ~ (v2_pre_topc @ X0)
% 0.86/1.03          | ~ (l1_pre_topc @ X0)
% 0.86/1.03          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.86/1.03          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 0.86/1.03      inference('sup-', [status(thm)], ['25', '64'])).
% 0.86/1.03  thf('66', plain,
% 0.86/1.03      (![X0 : $i]:
% 0.86/1.03         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.86/1.03          | ((k1_xboole_0) != (sk_C @ k1_xboole_0 @ X0))
% 0.86/1.03          | ~ (l1_pre_topc @ X0)
% 0.86/1.03          | ~ (v2_pre_topc @ X0))),
% 0.86/1.03      inference('simplify', [status(thm)], ['65'])).
% 0.86/1.03  thf('67', plain,
% 0.86/1.03      ((((k1_xboole_0) != (k1_xboole_0))
% 0.86/1.03        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.86/1.03        | ~ (v2_pre_topc @ sk_A)
% 0.86/1.03        | ~ (l1_pre_topc @ sk_A)
% 0.86/1.03        | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.86/1.03      inference('sup-', [status(thm)], ['24', '66'])).
% 0.86/1.03  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.86/1.03      inference('demod', [status(thm)], ['13', '14'])).
% 0.86/1.03  thf('69', plain, ((v2_pre_topc @ sk_A)),
% 0.86/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.03  thf('70', plain, ((l1_pre_topc @ sk_A)),
% 0.86/1.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.86/1.03  thf('71', plain,
% 0.86/1.03      ((((k1_xboole_0) != (k1_xboole_0)) | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 0.86/1.03      inference('demod', [status(thm)], ['67', '68', '69', '70'])).
% 0.86/1.03  thf('72', plain, ((v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.86/1.03      inference('simplify', [status(thm)], ['71'])).
% 0.86/1.03  thf('73', plain, ($false), inference('demod', [status(thm)], ['4', '72'])).
% 0.86/1.03  
% 0.86/1.03  % SZS output end Refutation
% 0.86/1.03  
% 0.86/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
