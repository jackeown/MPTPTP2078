%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1890+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pUOO75EVNx

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:31 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 180 expanded)
%              Number of leaves         :   26 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  725 (3512 expanded)
%              Number of equality atoms :    9 (  76 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t58_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                    = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ C @ B )
                   => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) )
                      = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) )
             => ( v2_tex_2 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t58_tex_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )
           => ( v2_tex_2 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ X11 @ X12 )
      | ( r2_hidden @ ( sk_C @ X11 @ X12 ) @ X11 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('3',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ X2 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_pre_topc @ A @ B ) @ A ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( v4_pre_topc @ ( k2_pre_topc @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_tops_1])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['9','10'])).

thf('29',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ X14 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X14 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('31',plain,(
    ! [X14: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X14 ) ) )
        = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ X14 ) )
      | ~ ( r2_hidden @ X14 @ sk_B ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) )
    = ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_tex_2 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v4_pre_topc @ X13 @ X12 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X12 ) @ X11 @ X13 )
       != ( k6_domain_1 @ ( u1_struct_0 @ X12 ) @ ( sk_C @ X11 @ X12 ) ) )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v3_tdlat_3 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t57_tex_2])).

thf('34',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) )
     != ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,
    ( ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_pre_topc @ ( k2_pre_topc @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) ) ) @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','41'])).

thf('43',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_tex_2 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_tex_2 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['45','46'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('48',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('51',plain,(
    ! [X4: $i] :
      ( ( l1_struct_0 @ X4 )
      | ~ ( l1_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['0','53'])).


%------------------------------------------------------------------------------
