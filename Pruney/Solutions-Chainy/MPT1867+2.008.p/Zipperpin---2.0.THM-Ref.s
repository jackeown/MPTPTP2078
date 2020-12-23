%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c0uXD4gC8Z

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:26 EST 2020

% Result     : Theorem 4.59s
% Output     : Refutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 229 expanded)
%              Number of leaves         :   29 (  85 expanded)
%              Depth                    :   15
%              Number of atoms          :  647 (1823 expanded)
%              Number of equality atoms :   38 (  88 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(cc1_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v3_pre_topc @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v3_pre_topc @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc1_tops_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v3_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v3_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r1_tarski @ ( sk_C @ X21 @ X22 ) @ X21 )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ X1 @ X0 )
      | ( r1_tarski @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( sk_C @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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

thf('16',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_xboole_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('19',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,
    ( ( ( sk_C @ k1_xboole_0 @ sk_A )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','25'])).

thf('27',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('28',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ k1_xboole_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v3_pre_topc @ X24 @ X22 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ X24 )
       != ( sk_C @ X21 @ X22 ) )
      | ( v2_tex_2 @ X21 @ X22 )
      | ~ ( l1_pre_topc @ X22 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v3_pre_topc @ X1 @ X0 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) @ X1 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 @ X0 )
       != ( sk_C @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_tex_2 @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(commutativity_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k9_subset_1 @ A @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k9_subset_1 @ X9 @ X11 @ X10 )
        = ( k9_subset_1 @ X9 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k9_subset_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k9_subset_1 @ X14 @ X12 @ X13 )
        = ( k3_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ ( k4_xboole_0 @ X7 @ X8 ) )
      = ( k3_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('41',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('42',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k9_subset_1 @ X0 @ k1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['36','47'])).

thf('49',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('50',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_C @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['33','48','49','50','51','52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v3_pre_topc @ X0 @ sk_A )
      | ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v3_pre_topc @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v3_pre_topc @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','57'])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['59','60','61','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c0uXD4gC8Z
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:32:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.59/4.84  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.59/4.84  % Solved by: fo/fo7.sh
% 4.59/4.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.59/4.84  % done 9103 iterations in 4.378s
% 4.59/4.84  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.59/4.84  % SZS output start Refutation
% 4.59/4.84  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.59/4.84  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.59/4.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.59/4.84  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.59/4.84  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 4.59/4.84  thf(sk_B_type, type, sk_B: $i).
% 4.59/4.84  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 4.59/4.84  thf(sk_A_type, type, sk_A: $i).
% 4.59/4.84  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 4.59/4.84  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.59/4.84  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.59/4.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.59/4.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.59/4.84  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 4.59/4.84  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 4.59/4.84  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.59/4.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.59/4.84  thf(l13_xboole_0, axiom,
% 4.59/4.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.59/4.84  thf('0', plain,
% 4.59/4.84      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 4.59/4.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.59/4.84  thf(t4_subset_1, axiom,
% 4.59/4.84    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.59/4.84  thf('1', plain,
% 4.59/4.84      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 4.59/4.84      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.59/4.84  thf('2', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 4.59/4.84      inference('sup+', [status(thm)], ['0', '1'])).
% 4.59/4.84  thf(cc1_tops_1, axiom,
% 4.59/4.84    (![A:$i]:
% 4.59/4.84     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.59/4.84       ( ![B:$i]:
% 4.59/4.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.59/4.84           ( ( v1_xboole_0 @ B ) => ( v3_pre_topc @ B @ A ) ) ) ) ))).
% 4.59/4.84  thf('3', plain,
% 4.59/4.84      (![X19 : $i, X20 : $i]:
% 4.59/4.84         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 4.59/4.84          | (v3_pre_topc @ X19 @ X20)
% 4.59/4.84          | ~ (v1_xboole_0 @ X19)
% 4.59/4.84          | ~ (l1_pre_topc @ X20)
% 4.59/4.84          | ~ (v2_pre_topc @ X20))),
% 4.59/4.84      inference('cnf', [status(esa)], [cc1_tops_1])).
% 4.59/4.84  thf('4', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         (~ (v1_xboole_0 @ X1)
% 4.59/4.84          | ~ (v2_pre_topc @ X0)
% 4.59/4.84          | ~ (l1_pre_topc @ X0)
% 4.59/4.84          | ~ (v1_xboole_0 @ X1)
% 4.59/4.84          | (v3_pre_topc @ X1 @ X0))),
% 4.59/4.84      inference('sup-', [status(thm)], ['2', '3'])).
% 4.59/4.84  thf('5', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         ((v3_pre_topc @ X1 @ X0)
% 4.59/4.84          | ~ (l1_pre_topc @ X0)
% 4.59/4.84          | ~ (v2_pre_topc @ X0)
% 4.59/4.84          | ~ (v1_xboole_0 @ X1))),
% 4.59/4.84      inference('simplify', [status(thm)], ['4'])).
% 4.59/4.84  thf('6', plain,
% 4.59/4.84      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 4.59/4.84      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.59/4.84  thf('7', plain,
% 4.59/4.84      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 4.59/4.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.59/4.84  thf('8', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 4.59/4.84      inference('sup+', [status(thm)], ['0', '1'])).
% 4.59/4.84  thf(d5_tex_2, axiom,
% 4.59/4.84    (![A:$i]:
% 4.59/4.84     ( ( l1_pre_topc @ A ) =>
% 4.59/4.84       ( ![B:$i]:
% 4.59/4.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.59/4.84           ( ( v2_tex_2 @ B @ A ) <=>
% 4.59/4.84             ( ![C:$i]:
% 4.59/4.84               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.59/4.84                 ( ~( ( r1_tarski @ C @ B ) & 
% 4.59/4.84                      ( ![D:$i]:
% 4.59/4.84                        ( ( m1_subset_1 @
% 4.59/4.84                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.59/4.84                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 4.59/4.84                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 4.59/4.84                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 4.59/4.84  thf('9', plain,
% 4.59/4.84      (![X21 : $i, X22 : $i]:
% 4.59/4.84         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 4.59/4.84          | (r1_tarski @ (sk_C @ X21 @ X22) @ X21)
% 4.59/4.84          | (v2_tex_2 @ X21 @ X22)
% 4.59/4.84          | ~ (l1_pre_topc @ X22))),
% 4.59/4.84      inference('cnf', [status(esa)], [d5_tex_2])).
% 4.59/4.84  thf('10', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         (~ (v1_xboole_0 @ X1)
% 4.59/4.84          | ~ (l1_pre_topc @ X0)
% 4.59/4.84          | (v2_tex_2 @ X1 @ X0)
% 4.59/4.84          | (r1_tarski @ (sk_C @ X1 @ X0) @ X1))),
% 4.59/4.84      inference('sup-', [status(thm)], ['8', '9'])).
% 4.59/4.84  thf(t3_xboole_1, axiom,
% 4.59/4.84    (![A:$i]:
% 4.59/4.84     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 4.59/4.84  thf('11', plain,
% 4.59/4.84      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 4.59/4.84      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.59/4.84  thf('12', plain,
% 4.59/4.84      (![X0 : $i]:
% 4.59/4.84         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 4.59/4.84          | ~ (l1_pre_topc @ X0)
% 4.59/4.84          | ~ (v1_xboole_0 @ k1_xboole_0)
% 4.59/4.84          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 4.59/4.84      inference('sup-', [status(thm)], ['10', '11'])).
% 4.59/4.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.59/4.84  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.59/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.59/4.84  thf('14', plain,
% 4.59/4.84      (![X0 : $i]:
% 4.59/4.84         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 4.59/4.84          | ~ (l1_pre_topc @ X0)
% 4.59/4.84          | ((sk_C @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 4.59/4.84      inference('demod', [status(thm)], ['12', '13'])).
% 4.59/4.84  thf('15', plain,
% 4.59/4.84      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 4.59/4.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.59/4.84  thf(t35_tex_2, conjecture,
% 4.59/4.84    (![A:$i]:
% 4.59/4.84     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 4.59/4.84       ( ![B:$i]:
% 4.59/4.84         ( ( ( v1_xboole_0 @ B ) & 
% 4.59/4.84             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.59/4.84           ( v2_tex_2 @ B @ A ) ) ) ))).
% 4.59/4.84  thf(zf_stmt_0, negated_conjecture,
% 4.59/4.84    (~( ![A:$i]:
% 4.59/4.84        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 4.59/4.84            ( l1_pre_topc @ A ) ) =>
% 4.59/4.84          ( ![B:$i]:
% 4.59/4.84            ( ( ( v1_xboole_0 @ B ) & 
% 4.59/4.84                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 4.59/4.84              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 4.59/4.84    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 4.59/4.84  thf('16', plain, (~ (v2_tex_2 @ sk_B @ sk_A)),
% 4.59/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.84  thf('17', plain, ((v1_xboole_0 @ sk_B)),
% 4.59/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.84  thf('18', plain,
% 4.59/4.84      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X2))),
% 4.59/4.84      inference('cnf', [status(esa)], [l13_xboole_0])).
% 4.59/4.84  thf('19', plain, (((sk_B) = (k1_xboole_0))),
% 4.59/4.84      inference('sup-', [status(thm)], ['17', '18'])).
% 4.59/4.84  thf('20', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 4.59/4.84      inference('demod', [status(thm)], ['16', '19'])).
% 4.59/4.84  thf('21', plain,
% 4.59/4.84      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 4.59/4.84      inference('sup-', [status(thm)], ['15', '20'])).
% 4.59/4.84  thf('22', plain,
% 4.59/4.84      ((((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))
% 4.59/4.84        | ~ (l1_pre_topc @ sk_A)
% 4.59/4.84        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 4.59/4.84      inference('sup-', [status(thm)], ['14', '21'])).
% 4.59/4.84  thf('23', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.84  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.59/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.59/4.84  thf('25', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 4.59/4.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 4.59/4.84  thf('26', plain,
% 4.59/4.84      (![X0 : $i]:
% 4.59/4.84         (((sk_C @ X0 @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 4.59/4.84      inference('sup+', [status(thm)], ['7', '25'])).
% 4.59/4.84  thf('27', plain,
% 4.59/4.84      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 4.59/4.84      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.59/4.84  thf('28', plain,
% 4.59/4.84      (![X21 : $i, X22 : $i]:
% 4.59/4.84         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 4.59/4.84          | (m1_subset_1 @ (sk_C @ X21 @ X22) @ 
% 4.59/4.84             (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 4.59/4.84          | (v2_tex_2 @ X21 @ X22)
% 4.59/4.84          | ~ (l1_pre_topc @ X22))),
% 4.59/4.84      inference('cnf', [status(esa)], [d5_tex_2])).
% 4.59/4.84  thf('29', plain,
% 4.59/4.84      (![X0 : $i]:
% 4.59/4.84         (~ (l1_pre_topc @ X0)
% 4.59/4.84          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 4.59/4.84          | (m1_subset_1 @ (sk_C @ k1_xboole_0 @ X0) @ 
% 4.59/4.84             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.59/4.84      inference('sup-', [status(thm)], ['27', '28'])).
% 4.59/4.84  thf('30', plain,
% 4.59/4.84      (![X21 : $i, X22 : $i, X24 : $i]:
% 4.59/4.84         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 4.59/4.84          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 4.59/4.84          | ~ (v3_pre_topc @ X24 @ X22)
% 4.59/4.84          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ X24)
% 4.59/4.84              != (sk_C @ X21 @ X22))
% 4.59/4.84          | (v2_tex_2 @ X21 @ X22)
% 4.59/4.84          | ~ (l1_pre_topc @ X22))),
% 4.59/4.84      inference('cnf', [status(esa)], [d5_tex_2])).
% 4.59/4.84  thf('31', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 4.59/4.84          | ~ (l1_pre_topc @ X0)
% 4.59/4.84          | ~ (l1_pre_topc @ X0)
% 4.59/4.84          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 4.59/4.84          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 4.59/4.84              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 4.59/4.84          | ~ (v3_pre_topc @ X1 @ X0)
% 4.59/4.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 4.59/4.84      inference('sup-', [status(thm)], ['29', '30'])).
% 4.59/4.84  thf('32', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 4.59/4.84          | ~ (v3_pre_topc @ X1 @ X0)
% 4.59/4.84          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0) @ X1)
% 4.59/4.84              != (sk_C @ (sk_C @ k1_xboole_0 @ X0) @ X0))
% 4.59/4.84          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ X0) @ X0)
% 4.59/4.84          | ~ (l1_pre_topc @ X0)
% 4.59/4.84          | (v2_tex_2 @ k1_xboole_0 @ X0))),
% 4.59/4.84      inference('simplify', [status(thm)], ['31'])).
% 4.59/4.84  thf('33', plain,
% 4.59/4.84      (![X0 : $i]:
% 4.59/4.84         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0 @ X0)
% 4.59/4.84            != (sk_C @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))
% 4.59/4.84          | ~ (v1_xboole_0 @ k1_xboole_0)
% 4.59/4.84          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 4.59/4.84          | ~ (l1_pre_topc @ sk_A)
% 4.59/4.84          | (v2_tex_2 @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 4.59/4.84          | ~ (v3_pre_topc @ X0 @ sk_A)
% 4.59/4.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.59/4.84      inference('sup-', [status(thm)], ['26', '32'])).
% 4.59/4.84  thf('34', plain,
% 4.59/4.84      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 4.59/4.84      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.59/4.84  thf(commutativity_k9_subset_1, axiom,
% 4.59/4.84    (![A:$i,B:$i,C:$i]:
% 4.59/4.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.59/4.84       ( ( k9_subset_1 @ A @ B @ C ) = ( k9_subset_1 @ A @ C @ B ) ) ))).
% 4.59/4.84  thf('35', plain,
% 4.59/4.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.59/4.84         (((k9_subset_1 @ X9 @ X11 @ X10) = (k9_subset_1 @ X9 @ X10 @ X11))
% 4.59/4.84          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X9)))),
% 4.59/4.84      inference('cnf', [status(esa)], [commutativity_k9_subset_1])).
% 4.59/4.84  thf('36', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 4.59/4.84           = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 4.59/4.84      inference('sup-', [status(thm)], ['34', '35'])).
% 4.59/4.84  thf('37', plain,
% 4.59/4.84      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 4.59/4.84      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.59/4.84  thf(redefinition_k9_subset_1, axiom,
% 4.59/4.84    (![A:$i,B:$i,C:$i]:
% 4.59/4.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.59/4.84       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 4.59/4.84  thf('38', plain,
% 4.59/4.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.59/4.84         (((k9_subset_1 @ X14 @ X12 @ X13) = (k3_xboole_0 @ X12 @ X13))
% 4.59/4.84          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 4.59/4.84      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 4.59/4.84  thf('39', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 4.59/4.84           = (k3_xboole_0 @ X1 @ k1_xboole_0))),
% 4.59/4.84      inference('sup-', [status(thm)], ['37', '38'])).
% 4.59/4.84  thf(t48_xboole_1, axiom,
% 4.59/4.84    (![A:$i,B:$i]:
% 4.59/4.84     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 4.59/4.84  thf('40', plain,
% 4.59/4.84      (![X7 : $i, X8 : $i]:
% 4.59/4.84         ((k4_xboole_0 @ X7 @ (k4_xboole_0 @ X7 @ X8))
% 4.59/4.84           = (k3_xboole_0 @ X7 @ X8))),
% 4.59/4.84      inference('cnf', [status(esa)], [t48_xboole_1])).
% 4.59/4.84  thf(t36_xboole_1, axiom,
% 4.59/4.84    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 4.59/4.84  thf('41', plain,
% 4.59/4.84      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 4.59/4.84      inference('cnf', [status(esa)], [t36_xboole_1])).
% 4.59/4.84  thf('42', plain,
% 4.59/4.84      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ k1_xboole_0))),
% 4.59/4.84      inference('cnf', [status(esa)], [t3_xboole_1])).
% 4.59/4.84  thf('43', plain,
% 4.59/4.84      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.59/4.84      inference('sup-', [status(thm)], ['41', '42'])).
% 4.59/4.84  thf('44', plain,
% 4.59/4.84      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 4.59/4.84      inference('sup+', [status(thm)], ['40', '43'])).
% 4.59/4.84  thf(commutativity_k3_xboole_0, axiom,
% 4.59/4.84    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.59/4.84  thf('45', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.59/4.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.59/4.84  thf('46', plain,
% 4.59/4.84      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.84      inference('sup+', [status(thm)], ['44', '45'])).
% 4.59/4.84  thf('47', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.59/4.84      inference('demod', [status(thm)], ['39', '46'])).
% 4.59/4.84  thf('48', plain,
% 4.59/4.84      (![X0 : $i, X1 : $i]:
% 4.59/4.84         ((k1_xboole_0) = (k9_subset_1 @ X0 @ k1_xboole_0 @ X1))),
% 4.59/4.84      inference('demod', [status(thm)], ['36', '47'])).
% 4.59/4.84  thf('49', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 4.59/4.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 4.59/4.84  thf('50', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 4.59/4.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 4.59/4.84  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.59/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.59/4.84  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.84  thf('53', plain, (((sk_C @ k1_xboole_0 @ sk_A) = (k1_xboole_0))),
% 4.59/4.84      inference('demod', [status(thm)], ['22', '23', '24'])).
% 4.59/4.84  thf('54', plain,
% 4.59/4.84      (![X0 : $i]:
% 4.59/4.84         (((k1_xboole_0) != (k1_xboole_0))
% 4.59/4.84          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 4.59/4.84          | (v2_tex_2 @ k1_xboole_0 @ sk_A)
% 4.59/4.84          | ~ (v3_pre_topc @ X0 @ sk_A)
% 4.59/4.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.59/4.84      inference('demod', [status(thm)],
% 4.59/4.84                ['33', '48', '49', '50', '51', '52', '53'])).
% 4.59/4.84  thf('55', plain,
% 4.59/4.84      (![X0 : $i]:
% 4.59/4.84         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 4.59/4.84          | ~ (v3_pre_topc @ X0 @ sk_A)
% 4.59/4.84          | (v2_tex_2 @ k1_xboole_0 @ sk_A))),
% 4.59/4.84      inference('simplify', [status(thm)], ['54'])).
% 4.59/4.84  thf('56', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 4.59/4.84      inference('demod', [status(thm)], ['16', '19'])).
% 4.59/4.84  thf('57', plain,
% 4.59/4.84      (![X0 : $i]:
% 4.59/4.84         (~ (v3_pre_topc @ X0 @ sk_A)
% 4.59/4.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 4.59/4.84      inference('clc', [status(thm)], ['55', '56'])).
% 4.59/4.84  thf('58', plain, (~ (v3_pre_topc @ k1_xboole_0 @ sk_A)),
% 4.59/4.84      inference('sup-', [status(thm)], ['6', '57'])).
% 4.59/4.84  thf('59', plain,
% 4.59/4.84      ((~ (v1_xboole_0 @ k1_xboole_0)
% 4.59/4.84        | ~ (v2_pre_topc @ sk_A)
% 4.59/4.84        | ~ (l1_pre_topc @ sk_A))),
% 4.59/4.84      inference('sup-', [status(thm)], ['5', '58'])).
% 4.59/4.84  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.59/4.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.59/4.84  thf('61', plain, ((v2_pre_topc @ sk_A)),
% 4.59/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.84  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 4.59/4.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.59/4.84  thf('63', plain, ($false),
% 4.59/4.84      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 4.59/4.84  
% 4.59/4.84  % SZS output end Refutation
% 4.59/4.84  
% 4.59/4.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
