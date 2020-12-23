%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1866+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ajn9l5kfh9

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 187 expanded)
%              Number of leaves         :   17 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  561 (3023 expanded)
%              Number of equality atoms :   15 ( 102 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t34_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( v1_tdlat_3 @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ( B
                   != ( u1_struct_0 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( v2_tex_2 @ B @ A )
                & ! [C: $i] :
                    ( ( ~ ( v2_struct_0 @ C )
                      & ( v1_pre_topc @ C )
                      & ( v1_tdlat_3 @ C )
                      & ( m1_pre_topc @ C @ A ) )
                   => ( B
                     != ( u1_struct_0 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ? [C: $i] :
              ( ( B
                = ( u1_struct_0 @ C ) )
              & ( m1_pre_topc @ C @ A )
              & ( v1_pre_topc @ C )
              & ~ ( v2_struct_0 @ C ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v2_struct_0 @ ( sk_C @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( m1_pre_topc @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X5: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X5 ) )
      | ~ ( m1_pre_topc @ X5 @ sk_A )
      | ~ ( v1_tdlat_3 @ X5 )
      | ~ ( v1_pre_topc @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
     != ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v1_pre_topc @ ( sk_C @ X0 @ X1 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_pre_topc @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X0
        = ( u1_struct_0 @ ( sk_C @ X0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t10_tsep_1])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_B
      = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['19','28','37'])).

thf('39',plain,
    ( ~ ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(t26_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v2_tex_2 @ C @ A )
                <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) )).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( X4
       != ( u1_struct_0 @ X2 ) )
      | ~ ( v2_tex_2 @ X4 @ X3 )
      | ( v1_tdlat_3 @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_pre_topc @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('43',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( l1_pre_topc @ X3 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ( v1_tdlat_3 @ X2 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X2 ) @ X3 )
      | ~ ( m1_pre_topc @ X2 @ X3 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,
    ( sk_B
    = ( u1_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ X0 )
      | ~ ( v2_tex_2 @ sk_B @ X0 )
      | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ~ ( v2_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_pre_topc @ ( sk_C @ sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['15','16'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','50'])).

thf('52',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) )
    | ( v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['6','7'])).

thf('55',plain,(
    v1_tdlat_3 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    v2_struct_0 @ ( sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['39','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['8','56'])).


%------------------------------------------------------------------------------
