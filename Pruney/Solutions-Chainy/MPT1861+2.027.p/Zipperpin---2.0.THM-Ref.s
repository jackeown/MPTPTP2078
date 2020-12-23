%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EayN9fTkaX

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:15 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 161 expanded)
%              Number of leaves         :   21 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  614 (1608 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ~ ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k9_subset_1 @ X41 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 )
      = ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    r1_tarski @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('14',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X36 @ X37 @ X38 ) @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_subset_1 @ sk_C_1 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ sk_C_1 @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k9_subset_1 @ X41 @ X39 @ X40 )
        = ( k3_xboole_0 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
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

thf('28',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v2_tex_2 @ X47 @ X48 )
      | ~ ( r1_tarski @ X49 @ X47 )
      | ( v2_tex_2 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_A )
   <= ( v2_tex_2 @ sk_C_1 @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X44: $i,X45: $i] :
      ( ( r1_tarski @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    ! [X44: $i,X46: $i] :
      ( ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X46 ) )
      | ~ ( r1_tarski @ X44 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( v2_tex_2 @ X47 @ X48 )
      | ~ ( r1_tarski @ X49 @ X47 )
      | ( v2_tex_2 @ X49 @ X48 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X48 ) ) )
      | ~ ( l1_pre_topc @ X48 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( v2_tex_2 @ X0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ! [X0: $i] :
        ( ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B ) )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('52',plain,
    ( ! [X0: $i] :
        ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_A )
   <= ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_tex_2 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('54',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['32'])).

thf('56',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(simpl_trail,[status(thm)],['33','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( r1_tarski @ X0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['31','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ sk_C_1 )
      | ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_subset_1 @ X0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( v2_tex_2 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['4','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EayN9fTkaX
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 194 iterations in 0.122s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.57  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.57  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.40/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.57  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.40/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.57  thf(t29_tex_2, conjecture,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( l1_pre_topc @ A ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57           ( ![C:$i]:
% 0.40/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57               ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.40/0.57                 ( v2_tex_2 @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i]:
% 0.40/0.57        ( ( l1_pre_topc @ A ) =>
% 0.40/0.57          ( ![B:$i]:
% 0.40/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57              ( ![C:$i]:
% 0.40/0.57                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57                  ( ( ( v2_tex_2 @ B @ A ) | ( v2_tex_2 @ C @ A ) ) =>
% 0.40/0.57                    ( v2_tex_2 @
% 0.40/0.57                      ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t29_tex_2])).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      (~ (v2_tex_2 @ (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C_1) @ 
% 0.40/0.57          sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(redefinition_k9_subset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.40/0.57  thf('2', plain,
% 0.40/0.57      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.40/0.57         (((k9_subset_1 @ X41 @ X39 @ X40) = (k3_xboole_0 @ X39 @ X40))
% 0.40/0.57          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1)
% 0.40/0.57           = (k3_xboole_0 @ X0 @ sk_C_1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.57  thf('4', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.40/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.40/0.57  thf('5', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(t3_subset, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      (![X44 : $i, X45 : $i]:
% 0.40/0.57         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('7', plain, ((r1_tarski @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.40/0.57  thf(d3_tarski, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (![X1 : $i, X3 : $i]:
% 0.40/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      (![X1 : $i, X3 : $i]:
% 0.40/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.40/0.57  thf('11', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.57      inference('simplify', [status(thm)], ['10'])).
% 0.40/0.57  thf('12', plain,
% 0.40/0.57      (![X44 : $i, X46 : $i]:
% 0.40/0.57         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('13', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.57  thf(dt_k9_subset_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.57       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.40/0.57         ((m1_subset_1 @ (k9_subset_1 @ X36 @ X37 @ X38) @ (k1_zfmisc_1 @ X36))
% 0.40/0.57          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X36)))),
% 0.40/0.57      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (m1_subset_1 @ (k9_subset_1 @ X0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['13', '14'])).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (![X44 : $i, X45 : $i]:
% 0.40/0.57         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.40/0.57      inference('sup-', [status(thm)], ['15', '16'])).
% 0.40/0.57  thf(t1_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i,C:$i]:
% 0.40/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.40/0.57       ( r1_tarski @ A @ C ) ))).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.57         (~ (r1_tarski @ X6 @ X7)
% 0.40/0.57          | ~ (r1_tarski @ X7 @ X8)
% 0.40/0.57          | (r1_tarski @ X6 @ X8))),
% 0.40/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X2)
% 0.40/0.57          | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (r1_tarski @ (k9_subset_1 @ sk_C_1 @ X0 @ sk_C_1) @ 
% 0.40/0.57          (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['7', '19'])).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      (![X44 : $i, X46 : $i]:
% 0.40/0.57         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (m1_subset_1 @ (k9_subset_1 @ sk_C_1 @ X0 @ sk_C_1) @ 
% 0.40/0.57          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.57  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.40/0.57         (((k9_subset_1 @ X41 @ X39 @ X40) = (k3_xboole_0 @ X39 @ X40))
% 0.40/0.57          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X41)))),
% 0.40/0.57      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.40/0.57  thf('26', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (m1_subset_1 @ (k3_xboole_0 @ X0 @ sk_C_1) @ 
% 0.40/0.57          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('demod', [status(thm)], ['22', '25'])).
% 0.40/0.57  thf('27', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf(t28_tex_2, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( l1_pre_topc @ A ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57           ( ![C:$i]:
% 0.40/0.57             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.57               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.40/0.57                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.40/0.57  thf('28', plain,
% 0.40/0.57      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.40/0.57          | ~ (v2_tex_2 @ X47 @ X48)
% 0.40/0.57          | ~ (r1_tarski @ X49 @ X47)
% 0.40/0.57          | (v2_tex_2 @ X49 @ X48)
% 0.40/0.57          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.40/0.57          | ~ (l1_pre_topc @ X48))),
% 0.40/0.57      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (l1_pre_topc @ sk_A)
% 0.40/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.40/0.57          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.40/0.57          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.40/0.57  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.40/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.40/0.57          | ~ (r1_tarski @ X0 @ sk_C_1)
% 0.40/0.57          | ~ (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.40/0.57      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.57  thf('32', plain, (((v2_tex_2 @ sk_B @ sk_A) | (v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('33', plain,
% 0.40/0.57      (((v2_tex_2 @ sk_C_1 @ sk_A)) <= (((v2_tex_2 @ sk_C_1 @ sk_A)))),
% 0.40/0.57      inference('split', [status(esa)], ['32'])).
% 0.40/0.57  thf('34', plain,
% 0.40/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('35', plain,
% 0.40/0.57      (![X44 : $i, X45 : $i]:
% 0.40/0.57         ((r1_tarski @ X44 @ X45) | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X45)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.57  thf('36', plain, ((r1_tarski @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['34', '35'])).
% 0.40/0.57  thf(t17_xboole_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.40/0.57  thf('37', plain,
% 0.40/0.57      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.40/0.57      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.40/0.57  thf('38', plain,
% 0.40/0.57      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.40/0.57         (~ (r1_tarski @ X6 @ X7)
% 0.40/0.57          | ~ (r1_tarski @ X7 @ X8)
% 0.40/0.57          | (r1_tarski @ X6 @ X8))),
% 0.40/0.57      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.40/0.57  thf('39', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.57  thf('40', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ (u1_struct_0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['36', '39'])).
% 0.40/0.57  thf('41', plain,
% 0.40/0.57      (![X44 : $i, X46 : $i]:
% 0.42/0.57         ((m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X46)) | ~ (r1_tarski @ X44 @ X46))),
% 0.42/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.42/0.57  thf('42', plain,
% 0.42/0.57      (![X0 : $i]:
% 0.42/0.57         (m1_subset_1 @ (k3_xboole_0 @ sk_B @ X0) @ 
% 0.42/0.57          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.42/0.57  thf('43', plain,
% 0.42/0.57      (((v2_tex_2 @ sk_B @ sk_A)) <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.57      inference('split', [status(esa)], ['32'])).
% 0.42/0.57  thf('44', plain,
% 0.42/0.57      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.42/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.57  thf('45', plain,
% 0.42/0.57      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.42/0.57         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.42/0.57          | ~ (v2_tex_2 @ X47 @ X48)
% 0.42/0.57          | ~ (r1_tarski @ X49 @ X47)
% 0.42/0.57          | (v2_tex_2 @ X49 @ X48)
% 0.42/0.57          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (u1_struct_0 @ X48)))
% 0.42/0.57          | ~ (l1_pre_topc @ X48))),
% 0.42/0.57      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.42/0.57  thf('46', plain,
% 0.42/0.57      (![X0 : $i]:
% 0.42/0.57         (~ (l1_pre_topc @ sk_A)
% 0.42/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.57      inference('sup-', [status(thm)], ['44', '45'])).
% 0.42/0.57  thf('47', plain, ((l1_pre_topc @ sk_A)),
% 0.42/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.57  thf('48', plain,
% 0.42/0.57      (![X0 : $i]:
% 0.42/0.57         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.57          | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.57          | ~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.57          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.57      inference('demod', [status(thm)], ['46', '47'])).
% 0.42/0.57  thf('49', plain,
% 0.42/0.57      ((![X0 : $i]:
% 0.42/0.57          (~ (r1_tarski @ X0 @ sk_B)
% 0.42/0.57           | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.57           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))))
% 0.42/0.57         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.57      inference('sup-', [status(thm)], ['43', '48'])).
% 0.42/0.57  thf('50', plain,
% 0.42/0.57      ((![X0 : $i]:
% 0.42/0.57          ((v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A)
% 0.42/0.57           | ~ (r1_tarski @ (k3_xboole_0 @ sk_B @ X0) @ sk_B)))
% 0.42/0.57         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.58      inference('sup-', [status(thm)], ['42', '49'])).
% 0.42/0.58  thf('51', plain,
% 0.42/0.58      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 0.42/0.58      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.42/0.58  thf('52', plain,
% 0.42/0.58      ((![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ sk_B @ X0) @ sk_A))
% 0.42/0.58         <= (((v2_tex_2 @ sk_B @ sk_A)))),
% 0.42/0.58      inference('demod', [status(thm)], ['50', '51'])).
% 0.42/0.58  thf('53', plain, (~ (v2_tex_2 @ (k3_xboole_0 @ sk_B @ sk_C_1) @ sk_A)),
% 0.42/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.42/0.58  thf('54', plain, (~ ((v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.58      inference('sup-', [status(thm)], ['52', '53'])).
% 0.42/0.58  thf('55', plain, (((v2_tex_2 @ sk_C_1 @ sk_A)) | ((v2_tex_2 @ sk_B @ sk_A))),
% 0.42/0.58      inference('split', [status(esa)], ['32'])).
% 0.42/0.58  thf('56', plain, (((v2_tex_2 @ sk_C_1 @ sk_A))),
% 0.42/0.58      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 0.42/0.58  thf('57', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.42/0.58      inference('simpl_trail', [status(thm)], ['33', '56'])).
% 0.42/0.58  thf('58', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.42/0.58          | (v2_tex_2 @ X0 @ sk_A)
% 0.42/0.58          | ~ (r1_tarski @ X0 @ sk_C_1))),
% 0.42/0.58      inference('demod', [status(thm)], ['31', '57'])).
% 0.42/0.58  thf('59', plain,
% 0.42/0.58      (![X0 : $i]:
% 0.42/0.58         (~ (r1_tarski @ (k3_xboole_0 @ X0 @ sk_C_1) @ sk_C_1)
% 0.42/0.58          | (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C_1) @ sk_A))),
% 0.42/0.58      inference('sup-', [status(thm)], ['26', '58'])).
% 0.42/0.58  thf('60', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_subset_1 @ X0 @ X1 @ X0) @ X0)),
% 0.42/0.58      inference('sup-', [status(thm)], ['15', '16'])).
% 0.42/0.58  thf('61', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]:
% 0.42/0.58         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.42/0.58      inference('sup-', [status(thm)], ['23', '24'])).
% 0.42/0.58  thf('62', plain,
% 0.42/0.58      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.42/0.58      inference('demod', [status(thm)], ['60', '61'])).
% 0.42/0.58  thf('63', plain,
% 0.42/0.58      (![X0 : $i]: (v2_tex_2 @ (k3_xboole_0 @ X0 @ sk_C_1) @ sk_A)),
% 0.42/0.58      inference('demod', [status(thm)], ['59', '62'])).
% 0.42/0.58  thf('64', plain, ($false), inference('demod', [status(thm)], ['4', '63'])).
% 0.42/0.58  
% 0.42/0.58  % SZS output end Refutation
% 0.42/0.58  
% 0.42/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
