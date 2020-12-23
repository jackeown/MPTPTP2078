%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CqtdnCb3qH

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:36 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  308 (25007 expanded)
%              Number of leaves         :   37 (6973 expanded)
%              Depth                    :   34
%              Number of atoms          : 2823 (401183 expanded)
%              Number of equality atoms :   98 (4056 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v3_tex_2_type,type,(
    v3_tex_2: $i > $i > $o )).

thf(v3_tdlat_3_type,type,(
    v3_tdlat_3: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t61_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v3_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ~ ( ( ( v3_pre_topc @ B @ A )
                | ( v4_pre_topc @ B @ A ) )
              & ( v3_tex_2 @ B @ A )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( v3_tdlat_3 @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ~ ( ( ( v3_pre_topc @ B @ A )
                  | ( v4_pre_topc @ B @ A ) )
                & ( v3_tex_2 @ B @ A )
                & ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t61_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( v1_tdlat_3 @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ~ ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( v3_tex_2 @ X26 @ X27 )
      | ~ ( v1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l1_pre_topc @ X27 )
      | ~ ( v1_tdlat_3 @ X27 )
      | ~ ( v2_pre_topc @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t49_tex_2])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_subset_1 @ sk_B_3 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v4_pre_topc @ B @ A )
             => ( v3_pre_topc @ B @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v3_tdlat_3 @ X19 )
      | ~ ( v4_pre_topc @ X20 @ X19 )
      | ( v3_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[t24_tdlat_3])).

thf('14',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15','16','17'])).

thf('19',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v3_pre_topc @ B @ A )
              & ( v3_tex_2 @ B @ A ) )
           => ( v1_tops_1 @ B @ A ) ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( v1_tops_1 @ X24 @ X25 )
      | ~ ( v3_tex_2 @ X24 @ X25 )
      | ~ ( v3_pre_topc @ X24 @ X25 )
      | ~ ( l1_pre_topc @ X25 )
      | ~ ( v2_pre_topc @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t47_tex_2])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A )
    | ( v1_tops_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ( v1_tops_1 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_tops_1 @ sk_B_3 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( v1_tops_1 @ sk_B_3 @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_tops_3,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( u1_struct_0 @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( v1_tops_1 @ X7 @ X8 )
      | ( ( k2_pre_topc @ X8 @ X7 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_pre_topc @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_tops_3])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( ( v4_pre_topc @ B @ A )
             => ( ( k2_pre_topc @ A @ B )
                = B ) )
            & ( ( ( v2_pre_topc @ A )
                & ( ( k2_pre_topc @ A @ B )
                  = B ) )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_pre_topc @ X5 @ X6 )
      | ( ( k2_pre_topc @ X6 @ X5 )
        = X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('39',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf(t19_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( B
                    = ( k1_tarski @ C ) )
                 => ( v3_pre_topc @ B @ A ) ) ) )
       => ( v1_tdlat_3 @ A ) ) ) )).

thf('44',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t19_tdlat_3])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('52',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('54',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('56',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

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

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X10 )
      | ( v3_pre_topc @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v3_pre_topc @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ( v3_pre_topc @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ sk_A )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','58'])).

thf('60',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('61',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_tex_2 @ B @ A )
          <=> ( ( v2_tex_2 @ B @ A )
              & ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( ( v2_tex_2 @ C @ A )
                      & ( r1_tarski @ B @ C ) )
                   => ( B = C ) ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( v3_tex_2 @ X13 @ X14 )
      | ( v2_tex_2 @ X13 @ X14 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
    inference(cnf,[status(esa)],[d7_tex_2])).

thf('63',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tex_2 @ sk_B_3 @ sk_A )
    | ~ ( v3_tex_2 @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v3_tex_2 @ sk_B_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('68',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('69',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) @ sk_A )
        | ~ ( r1_tarski @ X0 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','66','67','68','69'])).

thf('71',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','72'])).

thf('74',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('75',plain,
    ( ( v1_tops_1 @ sk_B_3 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('76',plain,
    ( ( v1_tops_1 @ sk_B_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('78',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = ( u1_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( v3_pre_topc @ sk_B_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('80',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_tdlat_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( v3_tdlat_3 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
             => ( v4_pre_topc @ B @ A ) ) ) ) ) )).

thf('81',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('82',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v4_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
    | ~ ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83','84','85'])).

thf('87',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['79','86'])).

thf('88',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
    | ~ ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('89',plain,
    ( ( ( k2_pre_topc @ sk_A @ sk_B_3 )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ X0 )
      | ( r1_tarski @ ( sk_B @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('92',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
      | ( v1_tdlat_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('97',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v3_pre_topc @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ( v3_pre_topc @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ sk_A )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('102',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('103',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('104',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('105',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) @ sk_A )
        | ~ ( r1_tarski @ X0 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','105'])).

thf('107',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('108',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( v3_pre_topc @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('110',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('111',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('112',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('113',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X10 )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','114'])).

thf('116',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('117',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('118',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('119',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('120',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('121',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['115','116','117','118','119','120','121'])).

thf('123',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('124',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','124'])).

thf('126',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('127',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t41_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ C @ B )
                 => ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) )
                    = C ) ) ) ) ) ) )).

thf('128',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( v2_tex_2 @ X21 @ X22 )
      | ~ ( r1_tarski @ X23 @ X21 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X22 ) @ X21 @ ( k2_pre_topc @ X22 @ X23 ) )
        = X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t41_tex_2])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('132',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('133',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('134',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('135',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('136',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['130','131','132','133','134','135','136','137'])).

thf('139',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
        = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','138'])).

thf('140',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','124'])).

thf('141',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('142',plain,
    ( ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
        = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['139','142'])).

thf('144',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','124'])).

thf('145',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('146',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_pre_topc @ X5 @ X6 )
      | ( ( k2_pre_topc @ X6 @ X5 )
        = X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = X0 )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = X0 )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,
    ( ( ~ ( v4_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
        = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['144','149'])).

thf('151',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','124'])).

thf('152',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('153',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('154',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v3_tdlat_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['154','155','156','157'])).

thf('159',plain,
    ( ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['151','158'])).

thf('160',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['97','108'])).

thf('161',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['150','161'])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
        = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['143','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('167',plain,(
    ! [X16: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t19_tdlat_3])).

thf('168',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v2_tex_2 @ X9 @ X10 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X10 ) @ X9 @ ( sk_D @ X11 @ X9 @ X10 ) )
        = X11 )
      | ~ ( r1_tarski @ X11 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_tex_2])).

thf('170',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_3 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B_3 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_B @ sk_A ) )
    | ~ ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['167','173'])).

thf('175',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v1_tdlat_3 @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_B @ sk_A ) )
    | ~ ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('179',plain,
    ( ~ ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_B @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['166','179'])).

thf('181',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['78','89'])).

thf('182',plain,
    ( ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_B @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A )
      = ( sk_B @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['165','182'])).

thf('184',plain,
    ( ( v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['109','183'])).

thf('185',plain,(
    ! [X16: $i] :
      ( ~ ( v3_pre_topc @ ( sk_B @ X16 ) @ X16 )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t19_tdlat_3])).

thf('186',plain,
    ( ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v1_tdlat_3 @ sk_A ) )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( v1_tdlat_3 @ sk_A )
   <= ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['186','187','188'])).

thf('190',plain,(
    ~ ( v1_tdlat_3 @ sk_A ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('191',plain,(
    ~ ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ( v4_pre_topc @ sk_B_3 @ sk_A )
    | ( v3_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('193',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['191','192'])).

thf('194',plain,(
    v3_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['73','193'])).

thf('195',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('196',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('197',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ ( u1_struct_0 @ X0 ) @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('198',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ( m1_subset_1 @ ( sk_D @ X0 @ ( u1_struct_0 @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( l1_pre_topc @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('200',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('201',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('202',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('203',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['198','199','200','201','202','203','204'])).

thf('206',plain,(
    ! [X2: $i,X4: $i] :
      ( ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('207',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','207'])).

thf('209',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ X1 ) )
        = X1 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('211',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_tex_2 @ ( u1_struct_0 @ sk_A ) @ sk_A )
        | ~ ( r1_tarski @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('213',plain,(
    v2_tex_2 @ sk_B_3 @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('214',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('215',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('216',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('217',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( r1_tarski @ X0 @ sk_B_3 )
        | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ X0 ) )
          = X0 )
        | ( v2_struct_0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','214','215','216','217','218'])).

thf('220',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
        = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      | ~ ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['208','219'])).

thf('221',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','207'])).

thf('222',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('223',plain,
    ( ( r1_tarski @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['221','222'])).

thf('224',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( k2_pre_topc @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
        = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['220','223'])).

thf('225',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','207'])).

thf('226',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['191','192'])).

thf('227',plain,(
    m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) ),
    inference(simpl_trail,[status(thm)],['225','226'])).

thf('228',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('229',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( v4_pre_topc @ X5 @ X6 )
      | ( ( k2_pre_topc @ X6 @ X5 )
        = X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('230',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( l1_pre_topc @ sk_A )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = X0 )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( ( k2_pre_topc @ sk_A @ X0 )
          = X0 )
        | ~ ( v4_pre_topc @ X0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['230','231'])).

thf('233',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['191','192'])).

thf('234',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
      | ( ( k2_pre_topc @ sk_A @ X0 )
        = X0 )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['232','233'])).

thf('235',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['227','234'])).

thf('236',plain,
    ( ( m1_subset_1 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ ( k1_zfmisc_1 @ sk_B_3 ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['195','207'])).

thf('237',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('238',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v3_tdlat_3 @ X17 )
      | ~ ( v3_pre_topc @ X18 @ X17 )
      | ( v4_pre_topc @ X18 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t23_tdlat_3])).

thf('239',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ sk_A )
        | ~ ( v3_tdlat_3 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    v3_tdlat_3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B_3 ) )
        | ( v4_pre_topc @ X0 @ sk_A )
        | ~ ( v3_pre_topc @ X0 @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['239','240','241','242'])).

thf('244',plain,
    ( ( ~ ( v3_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
      | ( v4_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['236','243'])).

thf('245',plain,
    ( ( v3_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','72'])).

thf('246',plain,
    ( ( v4_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['244','245'])).

thf('247',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['191','192'])).

thf('248',plain,(
    v4_pre_topc @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['246','247'])).

thf('249',plain,
    ( ( k2_pre_topc @ sk_A @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
    = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['235','248'])).

thf('250',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
        = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['224','249'])).

thf('251',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['191','192'])).

thf('252',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['250','251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
    = ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,
    ( ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('256',plain,
    ( ~ ( r1_tarski @ ( sk_B @ sk_A ) @ sk_B_3 )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('257',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_B @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B_3 )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference('sup+',[status(thm)],['35','42'])).

thf('259',plain,
    ( ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
      = ( sk_B @ sk_A ) )
   <= ( v4_pre_topc @ sk_B_3 @ sk_A ) ),
    inference(demod,[status(thm)],['257','258'])).

thf('260',plain,(
    v4_pre_topc @ sk_B_3 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['191','192'])).

thf('261',plain,
    ( ( k9_subset_1 @ sk_B_3 @ sk_B_3 @ ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A ) )
    = ( sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['259','260'])).

thf('262',plain,
    ( ( sk_D @ ( sk_B @ sk_A ) @ sk_B_3 @ sk_A )
    = ( sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['254','261'])).

thf('263',plain,(
    v3_pre_topc @ ( sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['194','262'])).

thf('264',plain,(
    ! [X16: $i] :
      ( ~ ( v3_pre_topc @ ( sk_B @ X16 ) @ X16 )
      | ( v1_tdlat_3 @ X16 )
      | ~ ( l1_pre_topc @ X16 )
      | ~ ( v2_pre_topc @ X16 ) ) ),
    inference(cnf,[status(esa)],[t19_tdlat_3])).

thf('265',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tdlat_3 @ sk_A ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,(
    v1_tdlat_3 @ sk_A ),
    inference(demod,[status(thm)],['265','266','267'])).

thf('269',plain,(
    $false ),
    inference(demod,[status(thm)],['9','268'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CqtdnCb3qH
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.19/1.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.19/1.41  % Solved by: fo/fo7.sh
% 1.19/1.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.19/1.41  % done 1644 iterations in 0.936s
% 1.19/1.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.19/1.41  % SZS output start Refutation
% 1.19/1.41  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.19/1.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.19/1.41  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 1.19/1.41  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.19/1.41  thf(sk_B_3_type, type, sk_B_3: $i).
% 1.19/1.41  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.19/1.41  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.19/1.41  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.19/1.41  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 1.19/1.41  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.19/1.41  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.19/1.41  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.19/1.41  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 1.19/1.41  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 1.19/1.41  thf(v3_tex_2_type, type, v3_tex_2: $i > $i > $o).
% 1.19/1.41  thf(v3_tdlat_3_type, type, v3_tdlat_3: $i > $o).
% 1.19/1.41  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 1.19/1.41  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.19/1.41  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.19/1.41  thf(sk_A_type, type, sk_A: $i).
% 1.19/1.41  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.19/1.41  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.19/1.41  thf(sk_B_type, type, sk_B: $i > $i).
% 1.19/1.41  thf(t61_tex_2, conjecture,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v3_tdlat_3 @ A ) & 
% 1.19/1.41         ( l1_pre_topc @ A ) ) =>
% 1.19/1.41       ( ![B:$i]:
% 1.19/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41           ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 1.19/1.41                ( v3_tex_2 @ B @ A ) & 
% 1.19/1.41                ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.19/1.41  thf(zf_stmt_0, negated_conjecture,
% 1.19/1.41    (~( ![A:$i]:
% 1.19/1.41        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 1.19/1.41            ( v3_tdlat_3 @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.41          ( ![B:$i]:
% 1.19/1.41            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41              ( ~( ( ( v3_pre_topc @ B @ A ) | ( v4_pre_topc @ B @ A ) ) & 
% 1.19/1.41                   ( v3_tex_2 @ B @ A ) & 
% 1.19/1.41                   ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 1.19/1.41    inference('cnf.neg', [status(esa)], [t61_tex_2])).
% 1.19/1.41  thf('0', plain,
% 1.19/1.41      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(t49_tex_2, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( v1_tdlat_3 @ A ) & 
% 1.19/1.41         ( l1_pre_topc @ A ) ) =>
% 1.19/1.41       ( ![B:$i]:
% 1.19/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41           ( ( v3_tex_2 @ B @ A ) <=>
% 1.19/1.41             ( ~( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 1.19/1.41  thf('1', plain,
% 1.19/1.41      (![X26 : $i, X27 : $i]:
% 1.19/1.41         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 1.19/1.41          | ~ (v3_tex_2 @ X26 @ X27)
% 1.19/1.41          | ~ (v1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 1.19/1.41          | ~ (l1_pre_topc @ X27)
% 1.19/1.41          | ~ (v1_tdlat_3 @ X27)
% 1.19/1.41          | ~ (v2_pre_topc @ X27)
% 1.19/1.41          | (v2_struct_0 @ X27))),
% 1.19/1.41      inference('cnf', [status(esa)], [t49_tex_2])).
% 1.19/1.41  thf('2', plain,
% 1.19/1.41      (((v2_struct_0 @ sk_A)
% 1.19/1.41        | ~ (v2_pre_topc @ sk_A)
% 1.19/1.41        | ~ (v1_tdlat_3 @ sk_A)
% 1.19/1.41        | ~ (l1_pre_topc @ sk_A)
% 1.19/1.41        | ~ (v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))
% 1.19/1.41        | ~ (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['0', '1'])).
% 1.19/1.41  thf('3', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('5', plain, ((v1_subset_1 @ sk_B_3 @ (u1_struct_0 @ sk_A))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('6', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('7', plain, (((v2_struct_0 @ sk_A) | ~ (v1_tdlat_3 @ sk_A))),
% 1.19/1.41      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 1.19/1.41  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('9', plain, (~ (v1_tdlat_3 @ sk_A)),
% 1.19/1.41      inference('clc', [status(thm)], ['7', '8'])).
% 1.19/1.41  thf('10', plain,
% 1.19/1.41      (((v3_pre_topc @ sk_B_3 @ sk_A) | (v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('11', plain,
% 1.19/1.41      (((v4_pre_topc @ sk_B_3 @ sk_A)) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('split', [status(esa)], ['10'])).
% 1.19/1.41  thf('12', plain,
% 1.19/1.41      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(t24_tdlat_3, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.41       ( ( v3_tdlat_3 @ A ) <=>
% 1.19/1.41         ( ![B:$i]:
% 1.19/1.41           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41             ( ( v4_pre_topc @ B @ A ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.19/1.41  thf('13', plain,
% 1.19/1.41      (![X19 : $i, X20 : $i]:
% 1.19/1.41         (~ (v3_tdlat_3 @ X19)
% 1.19/1.41          | ~ (v4_pre_topc @ X20 @ X19)
% 1.19/1.41          | (v3_pre_topc @ X20 @ X19)
% 1.19/1.41          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 1.19/1.41          | ~ (l1_pre_topc @ X19)
% 1.19/1.41          | ~ (v2_pre_topc @ X19))),
% 1.19/1.41      inference('cnf', [status(esa)], [t24_tdlat_3])).
% 1.19/1.41  thf('14', plain,
% 1.19/1.41      ((~ (v2_pre_topc @ sk_A)
% 1.19/1.41        | ~ (l1_pre_topc @ sk_A)
% 1.19/1.41        | (v3_pre_topc @ sk_B_3 @ sk_A)
% 1.19/1.41        | ~ (v4_pre_topc @ sk_B_3 @ sk_A)
% 1.19/1.41        | ~ (v3_tdlat_3 @ sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['12', '13'])).
% 1.19/1.41  thf('15', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('17', plain, ((v3_tdlat_3 @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('18', plain,
% 1.19/1.41      (((v3_pre_topc @ sk_B_3 @ sk_A) | ~ (v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('demod', [status(thm)], ['14', '15', '16', '17'])).
% 1.19/1.41  thf('19', plain,
% 1.19/1.41      (((v3_pre_topc @ sk_B_3 @ sk_A)) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['11', '18'])).
% 1.19/1.41  thf('20', plain,
% 1.19/1.41      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(t47_tex_2, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.41       ( ![B:$i]:
% 1.19/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41           ( ( ( v3_pre_topc @ B @ A ) & ( v3_tex_2 @ B @ A ) ) =>
% 1.19/1.41             ( v1_tops_1 @ B @ A ) ) ) ) ))).
% 1.19/1.41  thf('21', plain,
% 1.19/1.41      (![X24 : $i, X25 : $i]:
% 1.19/1.41         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 1.19/1.41          | (v1_tops_1 @ X24 @ X25)
% 1.19/1.41          | ~ (v3_tex_2 @ X24 @ X25)
% 1.19/1.41          | ~ (v3_pre_topc @ X24 @ X25)
% 1.19/1.41          | ~ (l1_pre_topc @ X25)
% 1.19/1.41          | ~ (v2_pre_topc @ X25)
% 1.19/1.41          | (v2_struct_0 @ X25))),
% 1.19/1.41      inference('cnf', [status(esa)], [t47_tex_2])).
% 1.19/1.41  thf('22', plain,
% 1.19/1.41      (((v2_struct_0 @ sk_A)
% 1.19/1.41        | ~ (v2_pre_topc @ sk_A)
% 1.19/1.41        | ~ (l1_pre_topc @ sk_A)
% 1.19/1.41        | ~ (v3_pre_topc @ sk_B_3 @ sk_A)
% 1.19/1.41        | ~ (v3_tex_2 @ sk_B_3 @ sk_A)
% 1.19/1.41        | (v1_tops_1 @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['20', '21'])).
% 1.19/1.41  thf('23', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('24', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('25', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('26', plain,
% 1.19/1.41      (((v2_struct_0 @ sk_A)
% 1.19/1.41        | ~ (v3_pre_topc @ sk_B_3 @ sk_A)
% 1.19/1.41        | (v1_tops_1 @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 1.19/1.41  thf('27', plain, (~ (v2_struct_0 @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('28', plain,
% 1.19/1.41      (((v1_tops_1 @ sk_B_3 @ sk_A) | ~ (v3_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('clc', [status(thm)], ['26', '27'])).
% 1.19/1.41  thf('29', plain,
% 1.19/1.41      (((v1_tops_1 @ sk_B_3 @ sk_A)) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['19', '28'])).
% 1.19/1.41  thf('30', plain,
% 1.19/1.41      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(d2_tops_3, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( l1_pre_topc @ A ) =>
% 1.19/1.41       ( ![B:$i]:
% 1.19/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41           ( ( v1_tops_1 @ B @ A ) <=>
% 1.19/1.41             ( ( k2_pre_topc @ A @ B ) = ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.19/1.41  thf('31', plain,
% 1.19/1.41      (![X7 : $i, X8 : $i]:
% 1.19/1.41         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 1.19/1.41          | ~ (v1_tops_1 @ X7 @ X8)
% 1.19/1.41          | ((k2_pre_topc @ X8 @ X7) = (u1_struct_0 @ X8))
% 1.19/1.41          | ~ (l1_pre_topc @ X8))),
% 1.19/1.41      inference('cnf', [status(esa)], [d2_tops_3])).
% 1.19/1.41  thf('32', plain,
% 1.19/1.41      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.41        | ((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A))
% 1.19/1.41        | ~ (v1_tops_1 @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['30', '31'])).
% 1.19/1.41  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('34', plain,
% 1.19/1.41      ((((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A))
% 1.19/1.41        | ~ (v1_tops_1 @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('demod', [status(thm)], ['32', '33'])).
% 1.19/1.41  thf('35', plain,
% 1.19/1.41      ((((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.19/1.41         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['29', '34'])).
% 1.19/1.41  thf('36', plain,
% 1.19/1.41      (((v4_pre_topc @ sk_B_3 @ sk_A)) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('split', [status(esa)], ['10'])).
% 1.19/1.41  thf('37', plain,
% 1.19/1.41      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(t52_pre_topc, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( l1_pre_topc @ A ) =>
% 1.19/1.41       ( ![B:$i]:
% 1.19/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.19/1.41             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.19/1.41               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.19/1.41  thf('38', plain,
% 1.19/1.41      (![X5 : $i, X6 : $i]:
% 1.19/1.41         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 1.19/1.41          | ~ (v4_pre_topc @ X5 @ X6)
% 1.19/1.41          | ((k2_pre_topc @ X6 @ X5) = (X5))
% 1.19/1.41          | ~ (l1_pre_topc @ X6))),
% 1.19/1.41      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.19/1.41  thf('39', plain,
% 1.19/1.41      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.41        | ((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3))
% 1.19/1.41        | ~ (v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['37', '38'])).
% 1.19/1.41  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('41', plain,
% 1.19/1.41      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3))
% 1.19/1.41        | ~ (v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('demod', [status(thm)], ['39', '40'])).
% 1.19/1.41  thf('42', plain,
% 1.19/1.41      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3)))
% 1.19/1.41         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['36', '41'])).
% 1.19/1.41  thf('43', plain,
% 1.19/1.41      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.41  thf(t19_tdlat_3, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.41       ( ( ![B:$i]:
% 1.19/1.41           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41             ( ![C:$i]:
% 1.19/1.41               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.19/1.41                 ( ( ( B ) = ( k1_tarski @ C ) ) => ( v3_pre_topc @ B @ A ) ) ) ) ) ) =>
% 1.19/1.41         ( v1_tdlat_3 @ A ) ) ))).
% 1.19/1.41  thf('44', plain,
% 1.19/1.41      (![X16 : $i]:
% 1.19/1.41         ((m1_subset_1 @ (sk_B @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.19/1.41          | (v1_tdlat_3 @ X16)
% 1.19/1.41          | ~ (l1_pre_topc @ X16)
% 1.19/1.41          | ~ (v2_pre_topc @ X16))),
% 1.19/1.41      inference('cnf', [status(esa)], [t19_tdlat_3])).
% 1.19/1.41  thf(t3_subset, axiom,
% 1.19/1.41    (![A:$i,B:$i]:
% 1.19/1.41     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.19/1.41  thf('45', plain,
% 1.19/1.41      (![X2 : $i, X3 : $i]:
% 1.19/1.41         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.19/1.41      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.41  thf('46', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (~ (v2_pre_topc @ X0)
% 1.19/1.41          | ~ (l1_pre_topc @ X0)
% 1.19/1.41          | (v1_tdlat_3 @ X0)
% 1.19/1.41          | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['44', '45'])).
% 1.19/1.41  thf('47', plain,
% 1.19/1.41      ((((r1_tarski @ (sk_B @ sk_A) @ sk_B_3)
% 1.19/1.41         | (v1_tdlat_3 @ sk_A)
% 1.19/1.41         | ~ (l1_pre_topc @ sk_A)
% 1.19/1.41         | ~ (v2_pre_topc @ sk_A))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['43', '46'])).
% 1.19/1.41  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('49', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('50', plain,
% 1.19/1.41      ((((r1_tarski @ (sk_B @ sk_A) @ sk_B_3) | (v1_tdlat_3 @ sk_A)))
% 1.19/1.41         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('demod', [status(thm)], ['47', '48', '49'])).
% 1.19/1.41  thf('51', plain, (~ (v1_tdlat_3 @ sk_A)),
% 1.19/1.41      inference('clc', [status(thm)], ['7', '8'])).
% 1.19/1.41  thf('52', plain,
% 1.19/1.41      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 1.19/1.41         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('clc', [status(thm)], ['50', '51'])).
% 1.19/1.41  thf('53', plain,
% 1.19/1.41      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.41  thf(dt_k2_subset_1, axiom,
% 1.19/1.41    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.19/1.41  thf('54', plain,
% 1.19/1.41      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 1.19/1.41      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 1.19/1.41  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.19/1.41  thf('55', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 1.19/1.41      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.19/1.41  thf('56', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.19/1.41      inference('demod', [status(thm)], ['54', '55'])).
% 1.19/1.41  thf(d5_tex_2, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( l1_pre_topc @ A ) =>
% 1.19/1.41       ( ![B:$i]:
% 1.19/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41           ( ( v2_tex_2 @ B @ A ) <=>
% 1.19/1.41             ( ![C:$i]:
% 1.19/1.41               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41                 ( ~( ( r1_tarski @ C @ B ) & 
% 1.19/1.41                      ( ![D:$i]:
% 1.19/1.41                        ( ( m1_subset_1 @
% 1.19/1.41                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 1.19/1.41                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 1.19/1.41                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.41  thf('57', plain,
% 1.19/1.41      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.19/1.41         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.19/1.41          | ~ (v2_tex_2 @ X9 @ X10)
% 1.19/1.41          | (v3_pre_topc @ (sk_D @ X11 @ X9 @ X10) @ X10)
% 1.19/1.41          | ~ (r1_tarski @ X11 @ X9)
% 1.19/1.41          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.19/1.41          | ~ (l1_pre_topc @ X10))),
% 1.19/1.41      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.19/1.41  thf('58', plain,
% 1.19/1.41      (![X0 : $i, X1 : $i]:
% 1.19/1.41         (~ (l1_pre_topc @ X0)
% 1.19/1.41          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.41          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 1.19/1.41          | (v3_pre_topc @ (sk_D @ X1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.19/1.41          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 1.19/1.41      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.41  thf('59', plain,
% 1.19/1.41      ((![X0 : $i]:
% 1.19/1.41          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.41           | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.19/1.41           | (v3_pre_topc @ (sk_D @ X0 @ (u1_struct_0 @ sk_A) @ sk_A) @ sk_A)
% 1.19/1.41           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 1.19/1.41           | ~ (l1_pre_topc @ sk_A)))
% 1.19/1.41         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['53', '58'])).
% 1.19/1.41  thf('60', plain,
% 1.19/1.41      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.41  thf('61', plain,
% 1.19/1.41      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(d7_tex_2, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( l1_pre_topc @ A ) =>
% 1.19/1.41       ( ![B:$i]:
% 1.19/1.41         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41           ( ( v3_tex_2 @ B @ A ) <=>
% 1.19/1.41             ( ( v2_tex_2 @ B @ A ) & 
% 1.19/1.41               ( ![C:$i]:
% 1.19/1.41                 ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41                   ( ( ( v2_tex_2 @ C @ A ) & ( r1_tarski @ B @ C ) ) =>
% 1.19/1.41                     ( ( B ) = ( C ) ) ) ) ) ) ) ) ) ))).
% 1.19/1.41  thf('62', plain,
% 1.19/1.41      (![X13 : $i, X14 : $i]:
% 1.19/1.41         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 1.19/1.41          | ~ (v3_tex_2 @ X13 @ X14)
% 1.19/1.41          | (v2_tex_2 @ X13 @ X14)
% 1.19/1.41          | ~ (l1_pre_topc @ X14))),
% 1.19/1.41      inference('cnf', [status(esa)], [d7_tex_2])).
% 1.19/1.41  thf('63', plain,
% 1.19/1.41      ((~ (l1_pre_topc @ sk_A)
% 1.19/1.41        | (v2_tex_2 @ sk_B_3 @ sk_A)
% 1.19/1.41        | ~ (v3_tex_2 @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['61', '62'])).
% 1.19/1.41  thf('64', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('65', plain, ((v3_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('66', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.41      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.19/1.41  thf('67', plain,
% 1.19/1.41      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.41  thf('68', plain,
% 1.19/1.41      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.41  thf('69', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('70', plain,
% 1.19/1.41      ((![X0 : $i]:
% 1.19/1.41          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.41           | (v3_pre_topc @ (sk_D @ X0 @ sk_B_3 @ sk_A) @ sk_A)
% 1.19/1.41           | ~ (r1_tarski @ X0 @ sk_B_3)))
% 1.19/1.41         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('demod', [status(thm)], ['59', '60', '66', '67', '68', '69'])).
% 1.19/1.41  thf('71', plain,
% 1.19/1.41      (![X2 : $i, X4 : $i]:
% 1.19/1.41         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 1.19/1.41      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.41  thf('72', plain,
% 1.19/1.41      ((![X0 : $i]:
% 1.19/1.41          (~ (r1_tarski @ X0 @ sk_B_3)
% 1.19/1.41           | (v3_pre_topc @ (sk_D @ X0 @ sk_B_3 @ sk_A) @ sk_A)))
% 1.19/1.41         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('clc', [status(thm)], ['70', '71'])).
% 1.19/1.41  thf('73', plain,
% 1.19/1.41      (((v3_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A))
% 1.19/1.41         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['52', '72'])).
% 1.19/1.41  thf('74', plain,
% 1.19/1.41      (((v3_pre_topc @ sk_B_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('split', [status(esa)], ['10'])).
% 1.19/1.41  thf('75', plain,
% 1.19/1.41      (((v1_tops_1 @ sk_B_3 @ sk_A) | ~ (v3_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('clc', [status(thm)], ['26', '27'])).
% 1.19/1.41  thf('76', plain,
% 1.19/1.41      (((v1_tops_1 @ sk_B_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['74', '75'])).
% 1.19/1.41  thf('77', plain,
% 1.19/1.41      ((((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A))
% 1.19/1.41        | ~ (v1_tops_1 @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('demod', [status(thm)], ['32', '33'])).
% 1.19/1.41  thf('78', plain,
% 1.19/1.41      ((((k2_pre_topc @ sk_A @ sk_B_3) = (u1_struct_0 @ sk_A)))
% 1.19/1.41         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['76', '77'])).
% 1.19/1.41  thf('79', plain,
% 1.19/1.41      (((v3_pre_topc @ sk_B_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('split', [status(esa)], ['10'])).
% 1.19/1.41  thf('80', plain,
% 1.19/1.41      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf(t23_tdlat_3, axiom,
% 1.19/1.41    (![A:$i]:
% 1.19/1.41     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.41       ( ( v3_tdlat_3 @ A ) <=>
% 1.19/1.41         ( ![B:$i]:
% 1.19/1.41           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.41             ( ( v3_pre_topc @ B @ A ) => ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.19/1.41  thf('81', plain,
% 1.19/1.41      (![X17 : $i, X18 : $i]:
% 1.19/1.41         (~ (v3_tdlat_3 @ X17)
% 1.19/1.41          | ~ (v3_pre_topc @ X18 @ X17)
% 1.19/1.41          | (v4_pre_topc @ X18 @ X17)
% 1.19/1.41          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.19/1.41          | ~ (l1_pre_topc @ X17)
% 1.19/1.41          | ~ (v2_pre_topc @ X17))),
% 1.19/1.41      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 1.19/1.41  thf('82', plain,
% 1.19/1.41      ((~ (v2_pre_topc @ sk_A)
% 1.19/1.41        | ~ (l1_pre_topc @ sk_A)
% 1.19/1.41        | (v4_pre_topc @ sk_B_3 @ sk_A)
% 1.19/1.41        | ~ (v3_pre_topc @ sk_B_3 @ sk_A)
% 1.19/1.41        | ~ (v3_tdlat_3 @ sk_A))),
% 1.19/1.41      inference('sup-', [status(thm)], ['80', '81'])).
% 1.19/1.41  thf('83', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('84', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('85', plain, ((v3_tdlat_3 @ sk_A)),
% 1.19/1.41      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.41  thf('86', plain,
% 1.19/1.41      (((v4_pre_topc @ sk_B_3 @ sk_A) | ~ (v3_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('demod', [status(thm)], ['82', '83', '84', '85'])).
% 1.19/1.41  thf('87', plain,
% 1.19/1.41      (((v4_pre_topc @ sk_B_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['79', '86'])).
% 1.19/1.41  thf('88', plain,
% 1.19/1.41      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3))
% 1.19/1.41        | ~ (v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.41      inference('demod', [status(thm)], ['39', '40'])).
% 1.19/1.41  thf('89', plain,
% 1.19/1.41      ((((k2_pre_topc @ sk_A @ sk_B_3) = (sk_B_3)))
% 1.19/1.41         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup-', [status(thm)], ['87', '88'])).
% 1.19/1.41  thf('90', plain,
% 1.19/1.41      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.41      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.41  thf('91', plain,
% 1.19/1.41      (![X0 : $i]:
% 1.19/1.41         (~ (v2_pre_topc @ X0)
% 1.19/1.41          | ~ (l1_pre_topc @ X0)
% 1.19/1.41          | (v1_tdlat_3 @ X0)
% 1.19/1.42          | (r1_tarski @ (sk_B @ X0) @ (u1_struct_0 @ X0)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['44', '45'])).
% 1.19/1.42  thf('92', plain,
% 1.19/1.42      ((((r1_tarski @ (sk_B @ sk_A) @ sk_B_3)
% 1.19/1.42         | (v1_tdlat_3 @ sk_A)
% 1.19/1.42         | ~ (l1_pre_topc @ sk_A)
% 1.19/1.42         | ~ (v2_pre_topc @ sk_A))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['90', '91'])).
% 1.19/1.42  thf('93', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('94', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('95', plain,
% 1.19/1.42      ((((r1_tarski @ (sk_B @ sk_A) @ sk_B_3) | (v1_tdlat_3 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.19/1.42  thf('96', plain, (~ (v1_tdlat_3 @ sk_A)),
% 1.19/1.42      inference('clc', [status(thm)], ['7', '8'])).
% 1.19/1.42  thf('97', plain,
% 1.19/1.42      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['95', '96'])).
% 1.19/1.42  thf('98', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('99', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         (~ (l1_pre_topc @ X0)
% 1.19/1.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.42          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 1.19/1.42          | (v3_pre_topc @ (sk_D @ X1 @ (u1_struct_0 @ X0) @ X0) @ X0)
% 1.19/1.42          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 1.19/1.42      inference('sup-', [status(thm)], ['56', '57'])).
% 1.19/1.42  thf('100', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.19/1.42           | (v3_pre_topc @ (sk_D @ X0 @ (u1_struct_0 @ sk_A) @ sk_A) @ sk_A)
% 1.19/1.42           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['98', '99'])).
% 1.19/1.42  thf('101', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('102', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.42      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.19/1.42  thf('103', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('104', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('105', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('106', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | (v3_pre_topc @ (sk_D @ X0 @ sk_B_3 @ sk_A) @ sk_A)
% 1.19/1.42           | ~ (r1_tarski @ X0 @ sk_B_3)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)],
% 1.19/1.42                ['100', '101', '102', '103', '104', '105'])).
% 1.19/1.42  thf('107', plain,
% 1.19/1.42      (![X2 : $i, X4 : $i]:
% 1.19/1.42         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 1.19/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.42  thf('108', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (r1_tarski @ X0 @ sk_B_3)
% 1.19/1.42           | (v3_pre_topc @ (sk_D @ X0 @ sk_B_3 @ sk_A) @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['106', '107'])).
% 1.19/1.42  thf('109', plain,
% 1.19/1.42      (((v3_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['97', '108'])).
% 1.19/1.42  thf('110', plain,
% 1.19/1.42      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['95', '96'])).
% 1.19/1.42  thf('111', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('112', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.19/1.42      inference('demod', [status(thm)], ['54', '55'])).
% 1.19/1.42  thf('113', plain,
% 1.19/1.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.19/1.42         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.19/1.42          | ~ (v2_tex_2 @ X9 @ X10)
% 1.19/1.42          | (m1_subset_1 @ (sk_D @ X11 @ X9 @ X10) @ 
% 1.19/1.42             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.19/1.42          | ~ (r1_tarski @ X11 @ X9)
% 1.19/1.42          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.19/1.42          | ~ (l1_pre_topc @ X10))),
% 1.19/1.42      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.19/1.42  thf('114', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         (~ (l1_pre_topc @ X0)
% 1.19/1.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.42          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 1.19/1.42          | (m1_subset_1 @ (sk_D @ X1 @ (u1_struct_0 @ X0) @ X0) @ 
% 1.19/1.42             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.42          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 1.19/1.42      inference('sup-', [status(thm)], ['112', '113'])).
% 1.19/1.42  thf('115', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.19/1.42           | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_A) @ sk_A) @ 
% 1.19/1.42              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.19/1.42           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['111', '114'])).
% 1.19/1.42  thf('116', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('117', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.42      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.19/1.42  thf('118', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('119', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('120', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('121', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('122', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | (m1_subset_1 @ (sk_D @ X0 @ sk_B_3 @ sk_A) @ 
% 1.19/1.42              (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (r1_tarski @ X0 @ sk_B_3)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)],
% 1.19/1.42                ['115', '116', '117', '118', '119', '120', '121'])).
% 1.19/1.42  thf('123', plain,
% 1.19/1.42      (![X2 : $i, X4 : $i]:
% 1.19/1.42         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 1.19/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.42  thf('124', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (r1_tarski @ X0 @ sk_B_3)
% 1.19/1.42           | (m1_subset_1 @ (sk_D @ X0 @ sk_B_3 @ sk_A) @ 
% 1.19/1.42              (k1_zfmisc_1 @ sk_B_3))))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['122', '123'])).
% 1.19/1.42  thf('125', plain,
% 1.19/1.42      (((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['110', '124'])).
% 1.19/1.42  thf('126', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('127', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 1.19/1.42      inference('demod', [status(thm)], ['54', '55'])).
% 1.19/1.42  thf(t41_tex_2, axiom,
% 1.19/1.42    (![A:$i]:
% 1.19/1.42     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.19/1.42       ( ![B:$i]:
% 1.19/1.42         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.42           ( ( v2_tex_2 @ B @ A ) <=>
% 1.19/1.42             ( ![C:$i]:
% 1.19/1.42               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.19/1.42                 ( ( r1_tarski @ C @ B ) =>
% 1.19/1.42                   ( ( k9_subset_1 @
% 1.19/1.42                       ( u1_struct_0 @ A ) @ B @ ( k2_pre_topc @ A @ C ) ) =
% 1.19/1.42                     ( C ) ) ) ) ) ) ) ) ))).
% 1.19/1.42  thf('128', plain,
% 1.19/1.42      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.19/1.42         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.19/1.42          | ~ (v2_tex_2 @ X21 @ X22)
% 1.19/1.42          | ~ (r1_tarski @ X23 @ X21)
% 1.19/1.42          | ((k9_subset_1 @ (u1_struct_0 @ X22) @ X21 @ 
% 1.19/1.42              (k2_pre_topc @ X22 @ X23)) = (X23))
% 1.19/1.42          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 1.19/1.42          | ~ (l1_pre_topc @ X22)
% 1.19/1.42          | ~ (v2_pre_topc @ X22)
% 1.19/1.42          | (v2_struct_0 @ X22))),
% 1.19/1.42      inference('cnf', [status(esa)], [t41_tex_2])).
% 1.19/1.42  thf('129', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((v2_struct_0 @ X0)
% 1.19/1.42          | ~ (v2_pre_topc @ X0)
% 1.19/1.42          | ~ (l1_pre_topc @ X0)
% 1.19/1.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.42          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.19/1.42              (k2_pre_topc @ X0 @ X1)) = (X1))
% 1.19/1.42          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 1.19/1.42          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 1.19/1.42      inference('sup-', [status(thm)], ['127', '128'])).
% 1.19/1.42  thf('130', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.19/1.42           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 1.19/1.42           | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.42               (k2_pre_topc @ sk_A @ X0)) = (X0))
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)
% 1.19/1.42           | ~ (v2_pre_topc @ sk_A)
% 1.19/1.42           | (v2_struct_0 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['126', '129'])).
% 1.19/1.42  thf('131', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('132', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.42      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.19/1.42  thf('133', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('134', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('135', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('136', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('137', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('138', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (r1_tarski @ X0 @ sk_B_3)
% 1.19/1.42           | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ X0))
% 1.19/1.42               = (X0))
% 1.19/1.42           | (v2_struct_0 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)],
% 1.19/1.42                ['130', '131', '132', '133', '134', '135', '136', '137'])).
% 1.19/1.42  thf('139', plain,
% 1.19/1.42      ((((v2_struct_0 @ sk_A)
% 1.19/1.42         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42             (k2_pre_topc @ sk_A @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)))
% 1.19/1.42             = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42         | ~ (r1_tarski @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_B_3)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['125', '138'])).
% 1.19/1.42  thf('140', plain,
% 1.19/1.42      (((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['110', '124'])).
% 1.19/1.42  thf('141', plain,
% 1.19/1.42      (![X2 : $i, X3 : $i]:
% 1.19/1.42         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.19/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.42  thf('142', plain,
% 1.19/1.42      (((r1_tarski @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_B_3))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['140', '141'])).
% 1.19/1.42  thf('143', plain,
% 1.19/1.42      ((((v2_struct_0 @ sk_A)
% 1.19/1.42         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42             (k2_pre_topc @ sk_A @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)))
% 1.19/1.42             = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['139', '142'])).
% 1.19/1.42  thf('144', plain,
% 1.19/1.42      (((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['110', '124'])).
% 1.19/1.42  thf('145', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('146', plain,
% 1.19/1.42      (![X5 : $i, X6 : $i]:
% 1.19/1.42         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 1.19/1.42          | ~ (v4_pre_topc @ X5 @ X6)
% 1.19/1.42          | ((k2_pre_topc @ X6 @ X5) = (X5))
% 1.19/1.42          | ~ (l1_pre_topc @ X6))),
% 1.19/1.42      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.19/1.42  thf('147', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)
% 1.19/1.42           | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 1.19/1.42           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['145', '146'])).
% 1.19/1.42  thf('148', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('149', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 1.19/1.42           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['147', '148'])).
% 1.19/1.42  thf('150', plain,
% 1.19/1.42      (((~ (v4_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A)
% 1.19/1.42         | ((k2_pre_topc @ sk_A @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42             = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['144', '149'])).
% 1.19/1.42  thf('151', plain,
% 1.19/1.42      (((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42         (k1_zfmisc_1 @ sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['110', '124'])).
% 1.19/1.42  thf('152', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('153', plain,
% 1.19/1.42      (![X17 : $i, X18 : $i]:
% 1.19/1.42         (~ (v3_tdlat_3 @ X17)
% 1.19/1.42          | ~ (v3_pre_topc @ X18 @ X17)
% 1.19/1.42          | (v4_pre_topc @ X18 @ X17)
% 1.19/1.42          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.19/1.42          | ~ (l1_pre_topc @ X17)
% 1.19/1.42          | ~ (v2_pre_topc @ X17))),
% 1.19/1.42      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 1.19/1.42  thf('154', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (v2_pre_topc @ sk_A)
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)
% 1.19/1.42           | (v4_pre_topc @ X0 @ sk_A)
% 1.19/1.42           | ~ (v3_pre_topc @ X0 @ sk_A)
% 1.19/1.42           | ~ (v3_tdlat_3 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['152', '153'])).
% 1.19/1.42  thf('155', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('157', plain, ((v3_tdlat_3 @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('158', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | (v4_pre_topc @ X0 @ sk_A)
% 1.19/1.42           | ~ (v3_pre_topc @ X0 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['154', '155', '156', '157'])).
% 1.19/1.42  thf('159', plain,
% 1.19/1.42      (((~ (v3_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A)
% 1.19/1.42         | (v4_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['151', '158'])).
% 1.19/1.42  thf('160', plain,
% 1.19/1.42      (((v3_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['97', '108'])).
% 1.19/1.42  thf('161', plain,
% 1.19/1.42      (((v4_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['159', '160'])).
% 1.19/1.42  thf('162', plain,
% 1.19/1.42      ((((k2_pre_topc @ sk_A @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42          = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['150', '161'])).
% 1.19/1.42  thf('163', plain,
% 1.19/1.42      ((((v2_struct_0 @ sk_A)
% 1.19/1.42         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42             (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42             = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['143', '162'])).
% 1.19/1.42  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('165', plain,
% 1.19/1.42      ((((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42          (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42          = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['163', '164'])).
% 1.19/1.42  thf('166', plain,
% 1.19/1.42      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['95', '96'])).
% 1.19/1.42  thf('167', plain,
% 1.19/1.42      (![X16 : $i]:
% 1.19/1.42         ((m1_subset_1 @ (sk_B @ X16) @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 1.19/1.42          | (v1_tdlat_3 @ X16)
% 1.19/1.42          | ~ (l1_pre_topc @ X16)
% 1.19/1.42          | ~ (v2_pre_topc @ X16))),
% 1.19/1.42      inference('cnf', [status(esa)], [t19_tdlat_3])).
% 1.19/1.42  thf('168', plain,
% 1.19/1.42      ((m1_subset_1 @ sk_B_3 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('169', plain,
% 1.19/1.42      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.19/1.42         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.19/1.42          | ~ (v2_tex_2 @ X9 @ X10)
% 1.19/1.42          | ((k9_subset_1 @ (u1_struct_0 @ X10) @ X9 @ (sk_D @ X11 @ X9 @ X10))
% 1.19/1.42              = (X11))
% 1.19/1.42          | ~ (r1_tarski @ X11 @ X9)
% 1.19/1.42          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 1.19/1.42          | ~ (l1_pre_topc @ X10))),
% 1.19/1.42      inference('cnf', [status(esa)], [d5_tex_2])).
% 1.19/1.42  thf('170', plain,
% 1.19/1.42      (![X0 : $i]:
% 1.19/1.42         (~ (l1_pre_topc @ sk_A)
% 1.19/1.42          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.19/1.42          | ~ (r1_tarski @ X0 @ sk_B_3)
% 1.19/1.42          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 1.19/1.42              (sk_D @ X0 @ sk_B_3 @ sk_A)) = (X0))
% 1.19/1.42          | ~ (v2_tex_2 @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('sup-', [status(thm)], ['168', '169'])).
% 1.19/1.42  thf('171', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('172', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.42      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.19/1.42  thf('173', plain,
% 1.19/1.42      (![X0 : $i]:
% 1.19/1.42         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.19/1.42          | ~ (r1_tarski @ X0 @ sk_B_3)
% 1.19/1.42          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 1.19/1.42              (sk_D @ X0 @ sk_B_3 @ sk_A)) = (X0)))),
% 1.19/1.42      inference('demod', [status(thm)], ['170', '171', '172'])).
% 1.19/1.42  thf('174', plain,
% 1.19/1.42      ((~ (v2_pre_topc @ sk_A)
% 1.19/1.42        | ~ (l1_pre_topc @ sk_A)
% 1.19/1.42        | (v1_tdlat_3 @ sk_A)
% 1.19/1.42        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 1.19/1.42            (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)) = (sk_B @ sk_A))
% 1.19/1.42        | ~ (r1_tarski @ (sk_B @ sk_A) @ sk_B_3))),
% 1.19/1.42      inference('sup-', [status(thm)], ['167', '173'])).
% 1.19/1.42  thf('175', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('176', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('177', plain,
% 1.19/1.42      (((v1_tdlat_3 @ sk_A)
% 1.19/1.42        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 1.19/1.42            (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)) = (sk_B @ sk_A))
% 1.19/1.42        | ~ (r1_tarski @ (sk_B @ sk_A) @ sk_B_3))),
% 1.19/1.42      inference('demod', [status(thm)], ['174', '175', '176'])).
% 1.19/1.42  thf('178', plain, (~ (v1_tdlat_3 @ sk_A)),
% 1.19/1.42      inference('clc', [status(thm)], ['7', '8'])).
% 1.19/1.42  thf('179', plain,
% 1.19/1.42      ((~ (r1_tarski @ (sk_B @ sk_A) @ sk_B_3)
% 1.19/1.42        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 1.19/1.42            (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)) = (sk_B @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['177', '178'])).
% 1.19/1.42  thf('180', plain,
% 1.19/1.42      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 1.19/1.42          (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)) = (sk_B @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['166', '179'])).
% 1.19/1.42  thf('181', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['78', '89'])).
% 1.19/1.42  thf('182', plain,
% 1.19/1.42      ((((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42          (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)) = (sk_B @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['180', '181'])).
% 1.19/1.42  thf('183', plain,
% 1.19/1.42      ((((sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) = (sk_B @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['165', '182'])).
% 1.19/1.42  thf('184', plain,
% 1.19/1.42      (((v3_pre_topc @ (sk_B @ sk_A) @ sk_A))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['109', '183'])).
% 1.19/1.42  thf('185', plain,
% 1.19/1.42      (![X16 : $i]:
% 1.19/1.42         (~ (v3_pre_topc @ (sk_B @ X16) @ X16)
% 1.19/1.42          | (v1_tdlat_3 @ X16)
% 1.19/1.42          | ~ (l1_pre_topc @ X16)
% 1.19/1.42          | ~ (v2_pre_topc @ X16))),
% 1.19/1.42      inference('cnf', [status(esa)], [t19_tdlat_3])).
% 1.19/1.42  thf('186', plain,
% 1.19/1.42      (((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v1_tdlat_3 @ sk_A)))
% 1.19/1.42         <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['184', '185'])).
% 1.19/1.42  thf('187', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('188', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('189', plain,
% 1.19/1.42      (((v1_tdlat_3 @ sk_A)) <= (((v3_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['186', '187', '188'])).
% 1.19/1.42  thf('190', plain, (~ (v1_tdlat_3 @ sk_A)),
% 1.19/1.42      inference('clc', [status(thm)], ['7', '8'])).
% 1.19/1.42  thf('191', plain, (~ ((v3_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('sup-', [status(thm)], ['189', '190'])).
% 1.19/1.42  thf('192', plain,
% 1.19/1.42      (((v4_pre_topc @ sk_B_3 @ sk_A)) | ((v3_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('split', [status(esa)], ['10'])).
% 1.19/1.42  thf('193', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('sat_resolution*', [status(thm)], ['191', '192'])).
% 1.19/1.42  thf('194', plain,
% 1.19/1.42      ((v3_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A)),
% 1.19/1.42      inference('simpl_trail', [status(thm)], ['73', '193'])).
% 1.19/1.42  thf('195', plain,
% 1.19/1.42      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['50', '51'])).
% 1.19/1.42  thf('196', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('197', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         (~ (l1_pre_topc @ X0)
% 1.19/1.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.42          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 1.19/1.42          | (m1_subset_1 @ (sk_D @ X1 @ (u1_struct_0 @ X0) @ X0) @ 
% 1.19/1.42             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.42          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 1.19/1.42      inference('sup-', [status(thm)], ['112', '113'])).
% 1.19/1.42  thf('198', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.19/1.42           | (m1_subset_1 @ (sk_D @ X0 @ (u1_struct_0 @ sk_A) @ sk_A) @ 
% 1.19/1.42              (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 1.19/1.42           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['196', '197'])).
% 1.19/1.42  thf('199', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('200', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.42      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.19/1.42  thf('201', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('202', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('203', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('204', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('205', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | (m1_subset_1 @ (sk_D @ X0 @ sk_B_3 @ sk_A) @ 
% 1.19/1.42              (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (r1_tarski @ X0 @ sk_B_3)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)],
% 1.19/1.42                ['198', '199', '200', '201', '202', '203', '204'])).
% 1.19/1.42  thf('206', plain,
% 1.19/1.42      (![X2 : $i, X4 : $i]:
% 1.19/1.42         ((m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X4)) | ~ (r1_tarski @ X2 @ X4))),
% 1.19/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.42  thf('207', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (r1_tarski @ X0 @ sk_B_3)
% 1.19/1.42           | (m1_subset_1 @ (sk_D @ X0 @ sk_B_3 @ sk_A) @ 
% 1.19/1.42              (k1_zfmisc_1 @ sk_B_3))))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['205', '206'])).
% 1.19/1.42  thf('208', plain,
% 1.19/1.42      (((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42         (k1_zfmisc_1 @ sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['195', '207'])).
% 1.19/1.42  thf('209', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('210', plain,
% 1.19/1.42      (![X0 : $i, X1 : $i]:
% 1.19/1.42         ((v2_struct_0 @ X0)
% 1.19/1.42          | ~ (v2_pre_topc @ X0)
% 1.19/1.42          | ~ (l1_pre_topc @ X0)
% 1.19/1.42          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.19/1.42          | ((k9_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0) @ 
% 1.19/1.42              (k2_pre_topc @ X0 @ X1)) = (X1))
% 1.19/1.42          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 1.19/1.42          | ~ (v2_tex_2 @ (u1_struct_0 @ X0) @ X0))),
% 1.19/1.42      inference('sup-', [status(thm)], ['127', '128'])).
% 1.19/1.42  thf('211', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (v2_tex_2 @ (u1_struct_0 @ sk_A) @ sk_A)
% 1.19/1.42           | ~ (r1_tarski @ X0 @ (u1_struct_0 @ sk_A))
% 1.19/1.42           | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A) @ 
% 1.19/1.42               (k2_pre_topc @ sk_A @ X0)) = (X0))
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)
% 1.19/1.42           | ~ (v2_pre_topc @ sk_A)
% 1.19/1.42           | (v2_struct_0 @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['209', '210'])).
% 1.19/1.42  thf('212', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('213', plain, ((v2_tex_2 @ sk_B_3 @ sk_A)),
% 1.19/1.42      inference('demod', [status(thm)], ['63', '64', '65'])).
% 1.19/1.42  thf('214', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('215', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('216', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('217', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('218', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('219', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (r1_tarski @ X0 @ sk_B_3)
% 1.19/1.42           | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (k2_pre_topc @ sk_A @ X0))
% 1.19/1.42               = (X0))
% 1.19/1.42           | (v2_struct_0 @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)],
% 1.19/1.42                ['211', '212', '213', '214', '215', '216', '217', '218'])).
% 1.19/1.42  thf('220', plain,
% 1.19/1.42      ((((v2_struct_0 @ sk_A)
% 1.19/1.42         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42             (k2_pre_topc @ sk_A @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)))
% 1.19/1.42             = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42         | ~ (r1_tarski @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_B_3)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['208', '219'])).
% 1.19/1.42  thf('221', plain,
% 1.19/1.42      (((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42         (k1_zfmisc_1 @ sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['195', '207'])).
% 1.19/1.42  thf('222', plain,
% 1.19/1.42      (![X2 : $i, X3 : $i]:
% 1.19/1.42         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 1.19/1.42      inference('cnf', [status(esa)], [t3_subset])).
% 1.19/1.42  thf('223', plain,
% 1.19/1.42      (((r1_tarski @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_B_3))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['221', '222'])).
% 1.19/1.42  thf('224', plain,
% 1.19/1.42      ((((v2_struct_0 @ sk_A)
% 1.19/1.42         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42             (k2_pre_topc @ sk_A @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)))
% 1.19/1.42             = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['220', '223'])).
% 1.19/1.42  thf('225', plain,
% 1.19/1.42      (((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42         (k1_zfmisc_1 @ sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['195', '207'])).
% 1.19/1.42  thf('226', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('sat_resolution*', [status(thm)], ['191', '192'])).
% 1.19/1.42  thf('227', plain,
% 1.19/1.42      ((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42        (k1_zfmisc_1 @ sk_B_3))),
% 1.19/1.42      inference('simpl_trail', [status(thm)], ['225', '226'])).
% 1.19/1.42  thf('228', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('229', plain,
% 1.19/1.42      (![X5 : $i, X6 : $i]:
% 1.19/1.42         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 1.19/1.42          | ~ (v4_pre_topc @ X5 @ X6)
% 1.19/1.42          | ((k2_pre_topc @ X6 @ X5) = (X5))
% 1.19/1.42          | ~ (l1_pre_topc @ X6))),
% 1.19/1.42      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.19/1.42  thf('230', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)
% 1.19/1.42           | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 1.19/1.42           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['228', '229'])).
% 1.19/1.42  thf('231', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('232', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 1.19/1.42           | ~ (v4_pre_topc @ X0 @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['230', '231'])).
% 1.19/1.42  thf('233', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('sat_resolution*', [status(thm)], ['191', '192'])).
% 1.19/1.42  thf('234', plain,
% 1.19/1.42      (![X0 : $i]:
% 1.19/1.42         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42          | ((k2_pre_topc @ sk_A @ X0) = (X0))
% 1.19/1.42          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 1.19/1.42      inference('simpl_trail', [status(thm)], ['232', '233'])).
% 1.19/1.42  thf('235', plain,
% 1.19/1.42      ((~ (v4_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A)
% 1.19/1.42        | ((k2_pre_topc @ sk_A @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42            = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['227', '234'])).
% 1.19/1.42  thf('236', plain,
% 1.19/1.42      (((m1_subset_1 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ 
% 1.19/1.42         (k1_zfmisc_1 @ sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['195', '207'])).
% 1.19/1.42  thf('237', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('238', plain,
% 1.19/1.42      (![X17 : $i, X18 : $i]:
% 1.19/1.42         (~ (v3_tdlat_3 @ X17)
% 1.19/1.42          | ~ (v3_pre_topc @ X18 @ X17)
% 1.19/1.42          | (v4_pre_topc @ X18 @ X17)
% 1.19/1.42          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.19/1.42          | ~ (l1_pre_topc @ X17)
% 1.19/1.42          | ~ (v2_pre_topc @ X17))),
% 1.19/1.42      inference('cnf', [status(esa)], [t23_tdlat_3])).
% 1.19/1.42  thf('239', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | ~ (v2_pre_topc @ sk_A)
% 1.19/1.42           | ~ (l1_pre_topc @ sk_A)
% 1.19/1.42           | (v4_pre_topc @ X0 @ sk_A)
% 1.19/1.42           | ~ (v3_pre_topc @ X0 @ sk_A)
% 1.19/1.42           | ~ (v3_tdlat_3 @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['237', '238'])).
% 1.19/1.42  thf('240', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('241', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('242', plain, ((v3_tdlat_3 @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('243', plain,
% 1.19/1.42      ((![X0 : $i]:
% 1.19/1.42          (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_B_3))
% 1.19/1.42           | (v4_pre_topc @ X0 @ sk_A)
% 1.19/1.42           | ~ (v3_pre_topc @ X0 @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['239', '240', '241', '242'])).
% 1.19/1.42  thf('244', plain,
% 1.19/1.42      (((~ (v3_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A)
% 1.19/1.42         | (v4_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['236', '243'])).
% 1.19/1.42  thf('245', plain,
% 1.19/1.42      (((v3_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['52', '72'])).
% 1.19/1.42  thf('246', plain,
% 1.19/1.42      (((v4_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['244', '245'])).
% 1.19/1.42  thf('247', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('sat_resolution*', [status(thm)], ['191', '192'])).
% 1.19/1.42  thf('248', plain,
% 1.19/1.42      ((v4_pre_topc @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) @ sk_A)),
% 1.19/1.42      inference('simpl_trail', [status(thm)], ['246', '247'])).
% 1.19/1.42  thf('249', plain,
% 1.19/1.42      (((k2_pre_topc @ sk_A @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42         = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('demod', [status(thm)], ['235', '248'])).
% 1.19/1.42  thf('250', plain,
% 1.19/1.42      ((((v2_struct_0 @ sk_A)
% 1.19/1.42         | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42             (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42             = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['224', '249'])).
% 1.19/1.42  thf('251', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('sat_resolution*', [status(thm)], ['191', '192'])).
% 1.19/1.42  thf('252', plain,
% 1.19/1.42      (((v2_struct_0 @ sk_A)
% 1.19/1.42        | ((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42            (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42            = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('simpl_trail', [status(thm)], ['250', '251'])).
% 1.19/1.42  thf('253', plain, (~ (v2_struct_0 @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('254', plain,
% 1.19/1.42      (((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42         = (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('clc', [status(thm)], ['252', '253'])).
% 1.19/1.42  thf('255', plain,
% 1.19/1.42      (((r1_tarski @ (sk_B @ sk_A) @ sk_B_3))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['50', '51'])).
% 1.19/1.42  thf('256', plain,
% 1.19/1.42      ((~ (r1_tarski @ (sk_B @ sk_A) @ sk_B_3)
% 1.19/1.42        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 1.19/1.42            (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)) = (sk_B @ sk_A)))),
% 1.19/1.42      inference('clc', [status(thm)], ['177', '178'])).
% 1.19/1.42  thf('257', plain,
% 1.19/1.42      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_3 @ 
% 1.19/1.42          (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)) = (sk_B @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup-', [status(thm)], ['255', '256'])).
% 1.19/1.42  thf('258', plain,
% 1.19/1.42      ((((u1_struct_0 @ sk_A) = (sk_B_3))) <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('sup+', [status(thm)], ['35', '42'])).
% 1.19/1.42  thf('259', plain,
% 1.19/1.42      ((((k9_subset_1 @ sk_B_3 @ sk_B_3 @ 
% 1.19/1.42          (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A)) = (sk_B @ sk_A)))
% 1.19/1.42         <= (((v4_pre_topc @ sk_B_3 @ sk_A)))),
% 1.19/1.42      inference('demod', [status(thm)], ['257', '258'])).
% 1.19/1.42  thf('260', plain, (((v4_pre_topc @ sk_B_3 @ sk_A))),
% 1.19/1.42      inference('sat_resolution*', [status(thm)], ['191', '192'])).
% 1.19/1.42  thf('261', plain,
% 1.19/1.42      (((k9_subset_1 @ sk_B_3 @ sk_B_3 @ (sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A))
% 1.19/1.42         = (sk_B @ sk_A))),
% 1.19/1.42      inference('simpl_trail', [status(thm)], ['259', '260'])).
% 1.19/1.42  thf('262', plain, (((sk_D @ (sk_B @ sk_A) @ sk_B_3 @ sk_A) = (sk_B @ sk_A))),
% 1.19/1.42      inference('sup+', [status(thm)], ['254', '261'])).
% 1.19/1.42  thf('263', plain, ((v3_pre_topc @ (sk_B @ sk_A) @ sk_A)),
% 1.19/1.42      inference('demod', [status(thm)], ['194', '262'])).
% 1.19/1.42  thf('264', plain,
% 1.19/1.42      (![X16 : $i]:
% 1.19/1.42         (~ (v3_pre_topc @ (sk_B @ X16) @ X16)
% 1.19/1.42          | (v1_tdlat_3 @ X16)
% 1.19/1.42          | ~ (l1_pre_topc @ X16)
% 1.19/1.42          | ~ (v2_pre_topc @ X16))),
% 1.19/1.42      inference('cnf', [status(esa)], [t19_tdlat_3])).
% 1.19/1.42  thf('265', plain,
% 1.19/1.42      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v1_tdlat_3 @ sk_A))),
% 1.19/1.42      inference('sup-', [status(thm)], ['263', '264'])).
% 1.19/1.42  thf('266', plain, ((v2_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('267', plain, ((l1_pre_topc @ sk_A)),
% 1.19/1.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.19/1.42  thf('268', plain, ((v1_tdlat_3 @ sk_A)),
% 1.19/1.42      inference('demod', [status(thm)], ['265', '266', '267'])).
% 1.19/1.42  thf('269', plain, ($false), inference('demod', [status(thm)], ['9', '268'])).
% 1.19/1.42  
% 1.19/1.42  % SZS output end Refutation
% 1.19/1.42  
% 1.19/1.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
