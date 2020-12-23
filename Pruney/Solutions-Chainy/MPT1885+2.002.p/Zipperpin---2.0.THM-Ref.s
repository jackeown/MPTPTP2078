%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vclSDeQZkV

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 409 expanded)
%              Number of leaves         :   25 ( 126 expanded)
%              Depth                    :   24
%              Number of atoms          :  788 (6216 expanded)
%              Number of equality atoms :   41 ( 207 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v4_tex_2_type,type,(
    v4_tex_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_pre_topc_type,type,(
    k1_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t53_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ~ ( ( v3_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( ~ ( v2_struct_0 @ C )
                    & ( v1_pre_topc @ C )
                    & ( m1_pre_topc @ C @ A ) )
                 => ~ ( ( v4_tex_2 @ C @ A )
                      & ( B
                        = ( u1_struct_0 @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
           => ~ ( ( v3_tex_2 @ B @ A )
                & ! [C: $i] :
                    ( ( ~ ( v2_struct_0 @ C )
                      & ( v1_pre_topc @ C )
                      & ( m1_pre_topc @ C @ A ) )
                   => ~ ( ( v4_tex_2 @ C @ A )
                        & ( B
                          = ( u1_struct_0 @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t53_tex_2])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) )
        & ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( m1_pre_topc @ ( k1_pre_topc @ X4 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('5',plain,
    ( ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf(d8_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( ( v4_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( v3_tex_2 @ C @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( ( sk_C @ X10 @ X11 )
        = ( u1_struct_0 @ X10 ) )
      | ( v4_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('9',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X13: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X13 ) )
      | ~ ( v4_tex_2 @ X13 @ sk_A )
      | ~ ( m1_pre_topc @ X13 @ sk_A )
      | ~ ( v1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( l1_pre_topc @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v1_pre_topc @ ( k1_pre_topc @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_pre_topc])).

thf('18',plain,
    ( ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('22',plain,
    ( ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
    | ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B
     != ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v1_pre_topc @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( C
                  = ( k1_pre_topc @ A @ B ) )
              <=> ( ( k2_struct_0 @ C )
                  = B ) ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( X2
       != ( k1_pre_topc @ X1 @ X0 ) )
      | ( ( k2_struct_0 @ X2 )
        = X0 )
      | ~ ( m1_pre_topc @ X2 @ X1 )
      | ~ ( v1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_pre_topc])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( v1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) )
      | ~ ( m1_pre_topc @ ( k1_pre_topc @ X1 @ X0 ) @ X1 )
      | ( ( k2_struct_0 @ ( k1_pre_topc @ X1 @ X0 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('30',plain,
    ( ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
      = sk_B )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('32',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf(fc4_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('33',plain,(
    ! [X9: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ~ ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc4_struct_0])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_pre_topc @ X7 @ X8 )
      | ( l1_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('37',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('40',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B
     != ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
    | ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['22','44'])).

thf('46',plain,
    ( ( sk_B
     != ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','45'])).

thf('47',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('48',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('49',plain,
    ( ( sk_B != sk_B )
    | ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
      = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,
    ( ( sk_C @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    = ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ~ ( v3_tex_2 @ ( sk_C @ X10 @ X11 ) @ X11 )
      | ( v4_tex_2 @ X10 @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d8_tex_2])).

thf('52',plain,
    ( ~ ( v3_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('55',plain,
    ( ~ ( v3_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v3_tex_2 @ ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ sk_A ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v3_tex_2 @ ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','57'])).

thf('59',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('60',plain,(
    v3_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('62',plain,(
    v4_tex_2 @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ! [X13: $i] :
      ( ( sk_B
       != ( u1_struct_0 @ X13 ) )
      | ~ ( v4_tex_2 @ X13 @ sk_A )
      | ~ ( m1_pre_topc @ X13 @ sk_A )
      | ~ ( v1_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ~ ( m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A )
    | ( sk_B
     != ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('66',plain,(
    m1_pre_topc @ ( k1_pre_topc @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['5','6'])).

thf('67',plain,
    ( ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    | ( sk_B
     != ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('69',plain,(
    sk_B
 != ( u1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B
     != ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) )
    | ~ ( l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','69'])).

thf('71',plain,
    ( ( k2_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['30','31'])).

thf('72',plain,(
    l1_struct_0 @ ( k1_pre_topc @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('73',plain,(
    sk_B != sk_B ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    $false ),
    inference(simplify,[status(thm)],['73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vclSDeQZkV
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:08:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 63 iterations in 0.038s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.50  thf(v4_tex_2_type, type, v4_tex_2: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.50  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.50  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(k1_pre_topc_type, type, k1_pre_topc: $i > $i > $i).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(d3_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      (![X3 : $i]:
% 0.22/0.50         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X3 : $i]:
% 0.22/0.50         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X3 : $i]:
% 0.22/0.50         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.22/0.50  thf(t53_tex_2, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.50             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50           ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.22/0.50                ( ![C:$i]:
% 0.22/0.50                  ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.22/0.50                      ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50                    ( ~( ( v4_tex_2 @ C @ A ) & ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.50            ( l1_pre_topc @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.50                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50              ( ~( ( v3_tex_2 @ B @ A ) & 
% 0.22/0.50                   ( ![C:$i]:
% 0.22/0.50                     ( ( ( ~( v2_struct_0 @ C ) ) & ( v1_pre_topc @ C ) & 
% 0.22/0.50                         ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50                       ( ~( ( v4_tex_2 @ C @ A ) & 
% 0.22/0.50                            ( ( B ) = ( u1_struct_0 @ C ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t53_tex_2])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(dt_k1_pre_topc, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ( l1_pre_topc @ A ) & 
% 0.22/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.50       ( ( v1_pre_topc @ ( k1_pre_topc @ A @ B ) ) & 
% 0.22/0.50         ( m1_pre_topc @ ( k1_pre_topc @ A @ B ) @ A ) ) ))).
% 0.22/0.50  thf('4', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X4)
% 0.22/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.50          | (m1_pre_topc @ (k1_pre_topc @ X4 @ X5) @ X4))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.50  thf('6', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('7', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(d8_tex_2, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.50           ( ( v4_tex_2 @ B @ A ) <=>
% 0.22/0.50             ( ![C:$i]:
% 0.22/0.50               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50                 ( ( ( C ) = ( u1_struct_0 @ B ) ) => ( v3_tex_2 @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.50          | ((sk_C @ X10 @ X11) = (u1_struct_0 @ X10))
% 0.22/0.50          | (v4_tex_2 @ X10 @ X11)
% 0.22/0.50          | ~ (l1_pre_topc @ X11)
% 0.22/0.50          | (v2_struct_0 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50            = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.50  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50            = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      ((((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50          = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.22/0.50        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      (![X13 : $i]:
% 0.22/0.50         (((sk_B) != (u1_struct_0 @ X13))
% 0.22/0.50          | ~ (v4_tex_2 @ X13 @ sk_A)
% 0.22/0.50          | ~ (m1_pre_topc @ X13 @ sk_A)
% 0.22/0.50          | ~ (v1_pre_topc @ X13)
% 0.22/0.50          | (v2_struct_0 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      ((((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50          = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.22/0.50        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ((sk_B) != (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X4)
% 0.22/0.50          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.22/0.50          | (v1_pre_topc @ (k1_pre_topc @ X4 @ X5)))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_k1_pre_topc])).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)) | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.50  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('20', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('21', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('22', plain,
% 0.22/0.50      ((((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50          = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.22/0.50        | (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ((sk_B) != (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['15', '20', '21'])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(d10_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( ( v1_pre_topc @ C ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.22/0.50               ( ( ( C ) = ( k1_pre_topc @ A @ B ) ) <=>
% 0.22/0.50                 ( ( k2_struct_0 @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.22/0.50          | ((X2) != (k1_pre_topc @ X1 @ X0))
% 0.22/0.50          | ((k2_struct_0 @ X2) = (X0))
% 0.22/0.50          | ~ (m1_pre_topc @ X2 @ X1)
% 0.22/0.50          | ~ (v1_pre_topc @ X2)
% 0.22/0.50          | ~ (l1_pre_topc @ X1))),
% 0.22/0.50      inference('cnf', [status(esa)], [d10_pre_topc])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (~ (l1_pre_topc @ X1)
% 0.22/0.50          | ~ (v1_pre_topc @ (k1_pre_topc @ X1 @ X0))
% 0.22/0.50          | ~ (m1_pre_topc @ (k1_pre_topc @ X1 @ X0) @ X1)
% 0.22/0.50          | ((k2_struct_0 @ (k1_pre_topc @ X1 @ X0)) = (X0))
% 0.22/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.22/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.22/0.50  thf('26', plain,
% 0.22/0.50      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.22/0.50        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '25'])).
% 0.22/0.50  thf('27', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.22/0.50        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      ((((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))
% 0.22/0.50        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.50  thf('31', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('32', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf(fc4_struct_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ))).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X9 : $i]:
% 0.22/0.50         ((v1_xboole_0 @ (k2_struct_0 @ X9))
% 0.22/0.50          | ~ (l1_struct_0 @ X9)
% 0.22/0.50          | ~ (v2_struct_0 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc4_struct_0])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B)
% 0.22/0.50        | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf(dt_m1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( l1_pre_topc @ A ) =>
% 0.22/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.50  thf('36', plain,
% 0.22/0.50      (![X7 : $i, X8 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X7 @ X8) | (l1_pre_topc @ X7) | ~ (l1_pre_topc @ X8))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('39', plain, ((l1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf(dt_l1_pre_topc, axiom,
% 0.22/0.50    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.50  thf('40', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_pre_topc @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.22/0.50  thf('41', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (((v1_xboole_0 @ sk_B) | ~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('demod', [status(thm)], ['34', '41'])).
% 0.22/0.50  thf('43', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('44', plain, (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('clc', [status(thm)], ['42', '43'])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      ((((sk_B) != (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.22/0.50        | ((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50            = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('clc', [status(thm)], ['22', '44'])).
% 0.22/0.50  thf('46', plain,
% 0.22/0.50      ((((sk_B) != (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.22/0.50        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50            = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['2', '45'])).
% 0.22/0.50  thf('47', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('48', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      ((((sk_B) != (sk_B))
% 0.22/0.50        | ((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50            = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (((sk_C @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50         = (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('simplify', [status(thm)], ['49'])).
% 0.22/0.50  thf('51', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i]:
% 0.22/0.50         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.50          | ~ (v3_tex_2 @ (sk_C @ X10 @ X11) @ X11)
% 0.22/0.50          | (v4_tex_2 @ X10 @ X11)
% 0.22/0.50          | ~ (l1_pre_topc @ X11)
% 0.22/0.50          | (v2_struct_0 @ X11))),
% 0.22/0.50      inference('cnf', [status(esa)], [d8_tex_2])).
% 0.22/0.50  thf('52', plain,
% 0.22/0.50      ((~ (v3_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.50        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.50  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('54', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('55', plain,
% 0.22/0.50      ((~ (v3_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ sk_A)
% 0.22/0.50        | (v2_struct_0 @ sk_A)
% 0.22/0.50        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.22/0.50  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('57', plain,
% 0.22/0.50      (((v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ~ (v3_tex_2 @ (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ sk_A))),
% 0.22/0.50      inference('clc', [status(thm)], ['55', '56'])).
% 0.22/0.50  thf('58', plain,
% 0.22/0.50      ((~ (v3_tex_2 @ (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) @ sk_A)
% 0.22/0.50        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | (v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '57'])).
% 0.22/0.50  thf('59', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('60', plain, ((v3_tex_2 @ sk_B @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('61', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('62', plain, ((v4_tex_2 @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.22/0.50  thf('63', plain,
% 0.22/0.50      (![X13 : $i]:
% 0.22/0.50         (((sk_B) != (u1_struct_0 @ X13))
% 0.22/0.50          | ~ (v4_tex_2 @ X13 @ sk_A)
% 0.22/0.50          | ~ (m1_pre_topc @ X13 @ sk_A)
% 0.22/0.50          | ~ (v1_pre_topc @ X13)
% 0.22/0.50          | (v2_struct_0 @ X13))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('64', plain,
% 0.22/0.50      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ~ (v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ~ (m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)
% 0.22/0.50        | ((sk_B) != (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.22/0.50  thf('65', plain, ((v1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.50  thf('66', plain, ((m1_pre_topc @ (k1_pre_topc @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('67', plain,
% 0.22/0.50      (((v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))
% 0.22/0.50        | ((sk_B) != (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))))),
% 0.22/0.50      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.22/0.50  thf('68', plain, (~ (v2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('clc', [status(thm)], ['42', '43'])).
% 0.22/0.50  thf('69', plain, (((sk_B) != (u1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('clc', [status(thm)], ['67', '68'])).
% 0.22/0.50  thf('70', plain,
% 0.22/0.50      ((((sk_B) != (k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))
% 0.22/0.50        | ~ (l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['0', '69'])).
% 0.22/0.50  thf('71', plain, (((k2_struct_0 @ (k1_pre_topc @ sk_A @ sk_B)) = (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.50  thf('72', plain, ((l1_struct_0 @ (k1_pre_topc @ sk_A @ sk_B))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('73', plain, (((sk_B) != (sk_B))),
% 0.22/0.50      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.22/0.50  thf('74', plain, ($false), inference('simplify', [status(thm)], ['73'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
