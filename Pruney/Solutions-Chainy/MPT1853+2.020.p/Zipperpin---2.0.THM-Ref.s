%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dNEf6g5rEK

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 544 expanded)
%              Number of leaves         :   36 ( 163 expanded)
%              Depth                    :   21
%              Number of atoms          : 1479 (6535 expanded)
%              Number of equality atoms :   32 (  92 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tex_2_type,type,(
    k1_tex_2: $i > $i > $i )).

thf(t20_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
          <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A )
            <=> ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t20_tex_2])).

thf('0',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X1 ) @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k6_domain_1 @ X11 @ X12 )
        = ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('11',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('16',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('17',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('19',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
        = ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('24',plain,(
    ! [X9: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v7_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('25',plain,
    ( ( ~ ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v7_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('27',plain,
    ( ( ~ ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v7_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('29',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('30',plain,
    ( ( ( ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 )
        = ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('32',plain,
    ( ( ( ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 )
        = ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('34',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('35',plain,
    ( ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('37',plain,
    ( ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k6_domain_1 @ ( k1_tarski @ sk_B_1 ) @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['32','39'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
       != ( k6_domain_1 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( v1_zfmisc_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('42',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_tarski @ sk_B_1 )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( ( ( k1_tarski @ sk_B_1 )
       != ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf('47',plain,
    ( ( ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( v1_xboole_0 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('49',plain,
    ( ( v1_zfmisc_1 @ ( k1_tarski @ sk_B_1 ) )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( v7_struct_0 @ sk_A )
   <= ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','49'])).

thf('51',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) )
        & ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ) )).

thf('54',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( m1_pre_topc @ ( k1_tex_2 @ X22 @ X23 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('55',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf(cc10_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v7_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ~ ( v2_struct_0 @ B )
           => ( ~ ( v2_struct_0 @ B )
              & ~ ( v1_tex_2 @ B @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( v1_tex_2 @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v7_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc10_tex_2])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v7_struct_0 @ sk_A )
    | ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( v7_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( l1_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( v2_struct_0 @ ( k1_tex_2 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tex_2])).

thf('67',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ~ ( v2_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( v7_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['64','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v7_struct_0 @ sk_A )
   <= ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','74'])).

thf('76',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['51'])).

thf('77',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf(d3_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v1_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('78',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( ( sk_C @ X17 @ X18 )
        = ( u1_struct_0 @ X17 ) )
      | ( v1_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('79',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('83',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('85',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( m1_subset_1 @ ( sk_C @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v1_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('86',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['83','88'])).

thf('90',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('91',plain,
    ( ( m1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( v1_subset_1 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('93',plain,
    ( ( ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
        = ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( ( sk_C @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      = ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('95',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ~ ( v1_subset_1 @ ( sk_C @ X17 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ( v1_tex_2 @ X17 @ X18 )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('96',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      | ~ ( m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf('99',plain,
    ( ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ~ ( v1_subset_1 @ ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( u1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(clc,[status(thm)],['93','101'])).

thf(fc7_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('103',plain,(
    ! [X10: $i] :
      ( ( v1_zfmisc_1 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ~ ( v7_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc7_struct_0])).

thf('104',plain,
    ( ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc2_tex_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v2_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) )
        & ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ) )).

thf('106',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l1_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( v7_struct_0 @ ( k1_tex_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_tex_2])).

thf('107',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v7_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    m1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(clc,[status(thm)],['57','58'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('113',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('114',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X5: $i] :
      ( ( l1_struct_0 @ X5 )
      | ~ ( l1_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('118',plain,(
    l1_struct_0 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['104','111','118'])).

thf('120',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['51'])).

thf(t6_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf('121',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ~ ( v1_subset_1 @ ( k6_domain_1 @ X27 @ X26 ) @ X27 )
      | ~ ( v1_zfmisc_1 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t6_tex_2])).

thf('122',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['119','124'])).

thf('126',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('127',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A )
      & ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ ( k1_tex_2 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','75','76','131'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dNEf6g5rEK
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:40:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 190 iterations in 0.081s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.20/0.53  thf(v1_tex_2_type, type, v1_tex_2: $i > $i > $o).
% 0.20/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.53  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.53  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.20/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(k1_tex_2_type, type, k1_tex_2: $i > $i > $i).
% 0.20/0.53  thf(t20_tex_2, conjecture,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53           ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.53             ( v1_subset_1 @
% 0.20/0.53               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i]:
% 0.20/0.53        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53          ( ![B:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.53              ( ( v1_tex_2 @ ( k1_tex_2 @ A @ B ) @ A ) <=>
% 0.20/0.53                ( v1_subset_1 @
% 0.20/0.53                  ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.20/0.53                  ( u1_struct_0 @ A ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t20_tex_2])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A))
% 0.20/0.53        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t2_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         ((r2_hidden @ X3 @ X4)
% 0.20/0.53          | (v1_xboole_0 @ X4)
% 0.20/0.53          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (r2_hidden @ sk_B_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf(t63_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X1 : $i, X2 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k1_tarski @ X1) @ (k1_zfmisc_1 @ X2))
% 0.20/0.53          | ~ (r2_hidden @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (m1_subset_1 @ (k1_tarski @ sk_B_1) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.53  thf(d7_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (((X21) = (X20))
% 0.20/0.53          | (v1_subset_1 @ X21 @ X20)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.53        | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k6_domain_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i]:
% 0.20/0.53         ((v1_xboole_0 @ X11)
% 0.20/0.53          | ~ (m1_subset_1 @ X12 @ X11)
% 0.20/0.53          | ((k6_domain_1 @ X11 @ X12) = (k1_tarski @ X12)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (((~ (v1_subset_1 @ (k1_tarski @ sk_B_1) @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.53  thf(fc2_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X8 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.20/0.53          | ~ (l1_struct_0 @ X8)
% 0.20/0.53          | (v2_struct_0 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A))
% 0.20/0.53         | (v2_struct_0 @ sk_A)
% 0.20/0.53         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_l1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.53  thf('19', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.53  thf('22', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf(fc6_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X9 : $i]:
% 0.20/0.53         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X9))
% 0.20/0.53          | ~ (l1_struct_0 @ X9)
% 0.20/0.53          | (v7_struct_0 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (((~ (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v7_struct_0 @ sk_A)
% 0.20/0.53         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (((~ (v1_zfmisc_1 @ (k1_tarski @ sk_B_1)) | (v7_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.20/0.53        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((((k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (((((k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X8 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.20/0.53          | ~ (l1_struct_0 @ X8)
% 0.20/0.53          | (v2_struct_0 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v2_struct_0 @ sk_A)
% 0.20/0.53         | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (((~ (v1_xboole_0 @ (k1_tarski @ sk_B_1)) | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['35', '36'])).
% 0.20/0.53  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((k6_domain_1 @ (k1_tarski @ sk_B_1) @ sk_B_1) = (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['32', '39'])).
% 0.20/0.53  thf(d1_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ( v1_zfmisc_1 @ A ) <=>
% 0.20/0.53         ( ?[B:$i]:
% 0.20/0.53           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]:
% 0.20/0.53         (((X15) != (k6_domain_1 @ X15 @ X16))
% 0.20/0.53          | ~ (m1_subset_1 @ X16 @ X15)
% 0.20/0.53          | (v1_zfmisc_1 @ X15)
% 0.20/0.53          | (v1_xboole_0 @ X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.20/0.53         | ~ (m1_subset_1 @ sk_B_1 @ (k1_tarski @ sk_B_1))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      ((((k1_tarski @ sk_B_1) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.53  thf('44', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (((m1_subset_1 @ sk_B_1 @ (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (((((k1_tarski @ sk_B_1) != (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v1_zfmisc_1 @ (k1_tarski @ sk_B_1))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['42', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      ((((v1_zfmisc_1 @ (k1_tarski @ sk_B_1))
% 0.20/0.53         | (v1_xboole_0 @ (k1_tarski @ sk_B_1))))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((~ (v1_xboole_0 @ (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      (((v1_zfmisc_1 @ (k1_tarski @ sk_B_1)))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((v7_struct_0 @ sk_A))
% 0.20/0.53         <= (~
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))
% 0.20/0.53        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.53         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['51'])).
% 0.20/0.53  thf('53', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k1_tex_2, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.53         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.53         ( m1_pre_topc @ ( k1_tex_2 @ A @ B ) @ A ) ) ))).
% 0.20/0.53  thf('54', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X22)
% 0.20/0.53          | (v2_struct_0 @ X22)
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.53          | (m1_pre_topc @ (k1_tex_2 @ X22 @ X23) @ X22))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.53  thf('55', plain,
% 0.20/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('57', plain,
% 0.20/0.53      (((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['55', '56'])).
% 0.20/0.53  thf('58', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('59', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf(cc10_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v7_struct_0 @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ( ~( v2_struct_0 @ B ) ) =>
% 0.20/0.53             ( ( ~( v2_struct_0 @ B ) ) & ( ~( v1_tex_2 @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.53  thf('60', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.53          | ~ (v1_tex_2 @ X13 @ X14)
% 0.20/0.53          | (v2_struct_0 @ X13)
% 0.20/0.53          | ~ (l1_pre_topc @ X14)
% 0.20/0.53          | ~ (v7_struct_0 @ X14)
% 0.20/0.53          | (v2_struct_0 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc10_tex_2])).
% 0.20/0.53  thf('61', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v7_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.53        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.53  thf('62', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('63', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (v7_struct_0 @ sk_A)
% 0.20/0.53        | (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.53        | ~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.53  thf('64', plain,
% 0.20/0.53      ((((v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.53         | ~ (v7_struct_0 @ sk_A)
% 0.20/0.53         | (v2_struct_0 @ sk_A)))
% 0.20/0.53         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['52', '63'])).
% 0.20/0.53  thf('65', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('66', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X22)
% 0.20/0.53          | (v2_struct_0 @ X22)
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.20/0.53          | ~ (v2_struct_0 @ (k1_tex_2 @ X22 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k1_tex_2])).
% 0.20/0.53  thf('67', plain,
% 0.20/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.53  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('69', plain,
% 0.20/0.53      ((~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['67', '68'])).
% 0.20/0.53  thf('70', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('71', plain, (~ (v2_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['69', '70'])).
% 0.20/0.53  thf('72', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A) | ~ (v7_struct_0 @ sk_A)))
% 0.20/0.53         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['64', '71'])).
% 0.20/0.53  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('74', plain,
% 0.20/0.53      ((~ (v7_struct_0 @ sk_A))
% 0.20/0.53         <= (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['72', '73'])).
% 0.20/0.53  thf('75', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '74'])).
% 0.20/0.53  thf('76', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('split', [status(esa)], ['51'])).
% 0.20/0.53  thf('77', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf(d3_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.53           ( ( v1_tex_2 @ B @ A ) <=>
% 0.20/0.53             ( ![C:$i]:
% 0.20/0.53               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53                 ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.20/0.53                   ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.20/0.53  thf('78', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.53          | ((sk_C @ X17 @ X18) = (u1_struct_0 @ X17))
% 0.20/0.53          | (v1_tex_2 @ X17 @ X18)
% 0.20/0.53          | ~ (l1_pre_topc @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.53  thf('79', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['77', '78'])).
% 0.20/0.53  thf('80', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('81', plain,
% 0.20/0.53      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53        | ((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53            = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))),
% 0.20/0.53      inference('demod', [status(thm)], ['79', '80'])).
% 0.20/0.53  thf('82', plain,
% 0.20/0.53      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('83', plain,
% 0.20/0.53      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('84', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('85', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.53          | (m1_subset_1 @ (sk_C @ X17 @ X18) @ 
% 0.20/0.53             (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.20/0.53          | (v1_tex_2 @ X17 @ X18)
% 0.20/0.53          | ~ (l1_pre_topc @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.53  thf('86', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A)
% 0.20/0.53        | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.53  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('88', plain,
% 0.20/0.53      (((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53        | (m1_subset_1 @ (sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A) @ 
% 0.20/0.53           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['86', '87'])).
% 0.20/0.53  thf('89', plain,
% 0.20/0.53      ((((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['83', '88'])).
% 0.20/0.53  thf('90', plain,
% 0.20/0.53      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('91', plain,
% 0.20/0.53      (((m1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.53         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.53  thf('92', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i]:
% 0.20/0.53         (((X21) = (X20))
% 0.20/0.53          | (v1_subset_1 @ X21 @ X20)
% 0.20/0.53          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.53  thf('93', plain,
% 0.20/0.53      ((((v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.53          (u1_struct_0 @ sk_A))
% 0.20/0.53         | ((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['91', '92'])).
% 0.20/0.53  thf('94', plain,
% 0.20/0.53      ((((sk_C @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53          = (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['81', '82'])).
% 0.20/0.53  thf('95', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.53          | ~ (v1_subset_1 @ (sk_C @ X17 @ X18) @ (u1_struct_0 @ X18))
% 0.20/0.53          | (v1_tex_2 @ X17 @ X18)
% 0.20/0.53          | ~ (l1_pre_topc @ X18))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tex_2])).
% 0.20/0.53  thf('96', plain,
% 0.20/0.53      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.53            (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (l1_pre_topc @ sk_A)
% 0.20/0.53         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)
% 0.20/0.53         | ~ (m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['94', '95'])).
% 0.20/0.53  thf('97', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('98', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf('99', plain,
% 0.20/0.53      (((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.53            (u1_struct_0 @ sk_A))
% 0.20/0.53         | (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.53  thf('100', plain,
% 0.20/0.53      ((~ (v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('101', plain,
% 0.20/0.53      ((~ (v1_subset_1 @ (u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) @ 
% 0.20/0.53           (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['99', '100'])).
% 0.20/0.53  thf('102', plain,
% 0.20/0.53      ((((u1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) = (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('clc', [status(thm)], ['93', '101'])).
% 0.20/0.53  thf(fc7_struct_0, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ( v7_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.53       ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.53  thf('103', plain,
% 0.20/0.53      (![X10 : $i]:
% 0.20/0.53         ((v1_zfmisc_1 @ (u1_struct_0 @ X10))
% 0.20/0.53          | ~ (l1_struct_0 @ X10)
% 0.20/0.53          | ~ (v7_struct_0 @ X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc7_struct_0])).
% 0.20/0.53  thf('104', plain,
% 0.20/0.53      ((((v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.53         | ~ (l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['102', '103'])).
% 0.20/0.53  thf('105', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(fc2_tex_2, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 0.20/0.53         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.53       ( ( ~( v2_struct_0 @ ( k1_tex_2 @ A @ B ) ) ) & 
% 0.20/0.53         ( v7_struct_0 @ ( k1_tex_2 @ A @ B ) ) & 
% 0.20/0.53         ( v1_pre_topc @ ( k1_tex_2 @ A @ B ) ) ) ))).
% 0.20/0.53  thf('106', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i]:
% 0.20/0.53         (~ (l1_pre_topc @ X24)
% 0.20/0.53          | (v2_struct_0 @ X24)
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 0.20/0.53          | (v7_struct_0 @ (k1_tex_2 @ X24 @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_tex_2])).
% 0.20/0.53  thf('107', plain,
% 0.20/0.53      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))
% 0.20/0.53        | (v2_struct_0 @ sk_A)
% 0.20/0.53        | ~ (l1_pre_topc @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['105', '106'])).
% 0.20/0.53  thf('108', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('109', plain,
% 0.20/0.53      (((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1)) | (v2_struct_0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['107', '108'])).
% 0.20/0.53  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('111', plain, ((v7_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.20/0.53      inference('clc', [status(thm)], ['109', '110'])).
% 0.20/0.53  thf('112', plain, ((m1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)),
% 0.20/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.53  thf(dt_m1_pre_topc, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( l1_pre_topc @ A ) =>
% 0.20/0.53       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.53  thf('113', plain,
% 0.20/0.53      (![X6 : $i, X7 : $i]:
% 0.20/0.53         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.53  thf('114', plain,
% 0.20/0.53      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['112', '113'])).
% 0.20/0.53  thf('115', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('116', plain, ((l1_pre_topc @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.20/0.53      inference('demod', [status(thm)], ['114', '115'])).
% 0.20/0.53  thf('117', plain, (![X5 : $i]: ((l1_struct_0 @ X5) | ~ (l1_pre_topc @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.20/0.53  thf('118', plain, ((l1_struct_0 @ (k1_tex_2 @ sk_A @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['116', '117'])).
% 0.20/0.53  thf('119', plain,
% 0.20/0.53      (((v1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)))),
% 0.20/0.53      inference('demod', [status(thm)], ['104', '111', '118'])).
% 0.20/0.53  thf('120', plain,
% 0.20/0.53      (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('split', [status(esa)], ['51'])).
% 0.20/0.53  thf(t6_tex_2, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) =>
% 0.20/0.53           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.20/0.53                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.20/0.53  thf('121', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X26 @ X27)
% 0.20/0.53          | ~ (v1_subset_1 @ (k6_domain_1 @ X27 @ X26) @ X27)
% 0.20/0.53          | ~ (v1_zfmisc_1 @ X27)
% 0.20/0.53          | (v1_xboole_0 @ X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [t6_tex_2])).
% 0.20/0.53  thf('122', plain,
% 0.20/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['120', '121'])).
% 0.20/0.53  thf('123', plain, ((m1_subset_1 @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('124', plain,
% 0.20/0.53      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.53         | ~ (v1_zfmisc_1 @ (u1_struct_0 @ sk_A))))
% 0.20/0.53         <= (((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['122', '123'])).
% 0.20/0.53  thf('125', plain,
% 0.20/0.53      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['119', '124'])).
% 0.20/0.53  thf('126', plain,
% 0.20/0.53      (![X8 : $i]:
% 0.20/0.53         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.20/0.53          | ~ (l1_struct_0 @ X8)
% 0.20/0.53          | (v2_struct_0 @ X8))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.20/0.53  thf('127', plain,
% 0.20/0.53      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['125', '126'])).
% 0.20/0.53  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('129', plain,
% 0.20/0.53      (((v2_struct_0 @ sk_A))
% 0.20/0.53         <= (~ ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A)) & 
% 0.20/0.53             ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53               (u1_struct_0 @ sk_A))))),
% 0.20/0.53      inference('demod', [status(thm)], ['127', '128'])).
% 0.20/0.53  thf('130', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('131', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.20/0.53         (u1_struct_0 @ sk_A))) | 
% 0.20/0.53       ((v1_tex_2 @ (k1_tex_2 @ sk_A @ sk_B_1) @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['129', '130'])).
% 0.20/0.53  thf('132', plain, ($false),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['1', '75', '76', '131'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
