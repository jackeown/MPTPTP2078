%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1384+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dzbVUZ9mU6

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:36 EST 2020

% Result     : Theorem 9.06s
% Output     : Refutation 9.06s
% Verified   : 
% Statistics : Number of formulae       :  410 (289450 expanded)
%              Number of leaves         :   33 (80343 expanded)
%              Depth                    :   95
%              Number of atoms          : 10313 (6280269 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i )).

thf(m1_connsp_2_type,type,(
    m1_connsp_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(t9_connsp_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( m1_connsp_2 @ D @ A @ C )
                            & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v3_pre_topc @ B @ A )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( m1_connsp_2 @ D @ A @ C )
                              & ( r1_tarski @ D @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_connsp_2])).

thf('0',plain,(
    ! [X36: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_connsp_2 @ X36 @ sk_A @ sk_C_1 )
      | ~ ( r1_tarski @ X36 @ sk_B )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X36 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X36 @ sk_B ) )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X35 @ sk_B )
      | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X35 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X35 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( v2_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ B )
              <=> ? [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                    & ( v3_pre_topc @ D @ A )
                    & ( r1_tarski @ D @ B )
                    & ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ D @ C @ B @ A )
    <=> ( ( r2_hidden @ C @ D )
        & ( r1_tarski @ D @ B )
        & ( v3_pre_topc @ D @ A )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v3_pre_topc @ B @ A )
          <=> ! [C: $i] :
                ( ( r2_hidden @ C @ B )
              <=> ? [D: $i] :
                    ( zip_tseitin_0 @ D @ C @ B @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ( zip_tseitin_0 @ ( sk_D @ X19 @ X20 ) @ ( sk_C @ X19 @ X20 ) @ X19 @ X20 )
      | ( v3_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('10',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('17',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('18',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('29',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D @ sk_B @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X35 @ sk_B )
      | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) ) ),
    inference(split,[status(esa)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('35',plain,
    ( ! [X35: $i] :
        ( ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B )
        | ~ ( r2_hidden @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('39',plain,(
    ! [X35: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X35 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('42',plain,
    ( ! [X35: $i] :
        ( ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 )
        | ~ ( r2_hidden @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,
    ( ( ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('45',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf(dt_m1_connsp_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_connsp_2 @ C @ A @ B )
         => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_connsp_2 @ X2 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_connsp_2])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_connsp_2 @ X0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,
    ( ( ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf(t8_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( m1_connsp_2 @ C @ A @ B )
              <=> ? [D: $i] :
                    ( ( r2_hidden @ B @ D )
                    & ( r1_tarski @ D @ C )
                    & ( v3_pre_topc @ D @ A )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r1_tarski @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['43','58'])).

thf('60',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['37','60'])).

thf('62',plain,
    ( ( ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('63',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['36','64'])).

thf('66',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('68',plain,
    ( ( ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('69',plain,
    ( ( ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('70',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ ( sk_D_2 @ X33 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['68','75'])).

thf('77',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['67','77'])).

thf('79',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('81',plain,
    ( ( ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('82',plain,
    ( ( ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('83',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( v3_pre_topc @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('84',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ sk_A )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ sk_A )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['84','85','86'])).

thf('88',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['81','88'])).

thf('90',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['80','90'])).

thf('92',plain,
    ( ( ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('94',plain,
    ( ( ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('95',plain,
    ( ( ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('96',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( m1_subset_1 @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['94','101'])).

thf('103',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['93','103'])).

thf('105',plain,
    ( ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X18 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('107',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X1 )
        | ~ ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 @ X1 @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['92','107'])).

thf('109',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ X0 @ sk_A )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference('sup-',[status(thm)],['79','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['66','111'])).

thf('113',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v3_pre_topc @ sk_B @ sk_A )
    | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('115',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X19: $i,X20: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( r2_hidden @ ( sk_C @ X19 @ X20 ) @ X19 )
      | ~ ( zip_tseitin_0 @ X24 @ ( sk_C @ X19 @ X20 ) @ X19 @ X20 )
      | ( v3_pre_topc @ X19 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['113','122'])).

thf('124',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D @ sk_B @ sk_A ) @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('127',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('128',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('130',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( m1_subset_1 @ X0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['28','130'])).

thf('132',plain,
    ( ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('133',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('134',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ! [X35: $i] :
        ( ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B )
        | ~ ( r2_hidden @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('137',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('139',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('140',plain,
    ( ! [X35: $i] :
        ( ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 )
        | ~ ( r2_hidden @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('141',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('144',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('146',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('147',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A )
        | ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('150',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r1_tarski @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('152',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['152','153','154'])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['141','155'])).

thf('157',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['138','157'])).

thf('159',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('161',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['137','161'])).

thf('163',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('165',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('166',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('167',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('168',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ ( sk_D_2 @ X33 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('169',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['166','172'])).

thf('174',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['165','174'])).

thf('176',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('178',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('179',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('180',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( v3_pre_topc @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('181',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ sk_A )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['179','180'])).

thf('182',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ sk_A )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['181','182','183'])).

thf('185',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['178','184'])).

thf('186',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['185'])).

thf('187',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['177','186'])).

thf('188',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['187'])).

thf('189',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('190',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('191',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('192',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( m1_subset_1 @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('193',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['190','196'])).

thf('198',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['189','198'])).

thf('200',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( r2_hidden @ X31 @ X34 )
      | ~ ( r1_tarski @ X34 @ X33 )
      | ~ ( v3_pre_topc @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('202',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( m1_connsp_2 @ X0 @ sk_A @ X1 )
        | ~ ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( m1_connsp_2 @ X0 @ sk_A @ X1 )
        | ~ ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['202','203','204'])).

thf('206',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( v3_pre_topc @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
        | ( m1_connsp_2 @ X0 @ sk_A @ X1 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['205'])).

thf('207',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( m1_connsp_2 @ X0 @ sk_A @ X1 )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['188','206'])).

thf('208',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( m1_connsp_2 @ X0 @ sk_A @ X1 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( m1_connsp_2 @ X0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['176','208'])).

thf('210',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( m1_connsp_2 @ X0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( m1_connsp_2 @ X0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['164','210'])).

thf('212',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( m1_connsp_2 @ X0 @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['211'])).

thf('213',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['163','212'])).

thf('214',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,
    ( ( ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r1_tarski @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('219',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_B )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['219','220','221'])).

thf('223',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['216','222'])).

thf('224',plain,
    ( ( ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['27','224'])).

thf('226',plain,
    ( ( ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('228',plain,
    ( ( ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('229',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ ( sk_D_2 @ X33 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('231',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['229','230'])).

thf('232',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['231','232','233'])).

thf('235',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['228','234'])).

thf('236',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['227','236'])).

thf('238',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('240',plain,
    ( ( ( m1_connsp_2 @ sk_B @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['215'])).

thf('241',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( v3_pre_topc @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('243',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v3_pre_topc @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( sk_D_2 @ sk_B @ X0 @ sk_A ) @ sk_A )
      | ~ ( m1_connsp_2 @ sk_B @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v3_pre_topc @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['240','246'])).

thf('248',plain,
    ( ( ( v3_pre_topc @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['239','248'])).

thf('250',plain,
    ( ( ( v3_pre_topc @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('252',plain,
    ( ( ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('253',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('254',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,
    ( ( ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['251','254'])).

thf('256',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('257',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['255','256'])).

thf('258',plain,(
    ! [X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v3_pre_topc @ X15 @ X18 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('259',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X1 )
        | ~ ( v3_pre_topc @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 @ X1 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X1 @ X0 @ sk_A )
        | ~ ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ X1 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['250','259'])).

thf('261',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X1 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
        | ~ ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X1 @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['260'])).

thf('262',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v2_struct_0 @ sk_A )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ X0 @ sk_A )
        | ~ ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['238','261'])).

thf('263',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ X0 @ sk_A )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['262'])).

thf('264',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['226','263'])).

thf('265',plain,
    ( ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_B @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['264'])).

thf('266',plain,
    ( ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('267',plain,(
    ! [X0: $i] :
      ( ( v3_pre_topc @ sk_B @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('268',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['266','267'])).

thf('269',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_0 @ X0 @ ( sk_C @ sk_B @ sk_A ) @ sk_B @ sk_A )
        | ( v1_xboole_0 @ sk_B )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['268'])).

thf('270',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['265','269'])).

thf('271',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['271','272'])).

thf('274',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('275',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('276',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('277',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('278',plain,
    ( ! [X0: $i] :
        ( ( v3_pre_topc @ sk_B @ sk_A )
        | ~ ( v1_xboole_0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ sk_A ) ) )
   <= ( ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ sk_A ) )
        | ( v3_pre_topc @ sk_B @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['275','278'])).

thf('280',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('281',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_D @ sk_B @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,
    ( ( ( v3_pre_topc @ sk_B @ sk_A )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['15','281'])).

thf('283',plain,
    ( ~ ( v3_pre_topc @ sk_B @ sk_A )
   <= ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('284',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('285',plain,
    ( ! [X35: $i] :
        ( ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 )
        | ~ ( r2_hidden @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('286',plain,
    ( ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('287',plain,(
    r1_tarski @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('288',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('289',plain,
    ( ! [X35: $i] :
        ( ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B )
        | ~ ( r2_hidden @ X35 @ sk_B ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('290',plain,
    ( ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('291',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('292',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['290','291'])).

thf('293',plain,
    ( ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['287','292'])).

thf('294',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('295',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['293','294'])).

thf('296',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r2_hidden @ X31 @ ( sk_D_2 @ X33 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('297',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['297','298','299'])).

thf('301',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['286','300'])).

thf('302',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('304',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('305',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(demod,[status(thm)],['301','304'])).

thf('306',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['305','306'])).

thf('308',plain,
    ( ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['288','289'])).

thf('309',plain,
    ( ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ ( sk_C @ sk_B @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['284','285'])).

thf('310',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('311',plain,
    ( ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
   <= ! [X35: $i] :
        ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
        | ~ ( r2_hidden @ X35 @ sk_B )
        | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['6'])).

thf('312',plain,
    ( ( ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference(clc,[status(thm)],['282','283'])).

thf('314',plain,
    ( ( m1_subset_1 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['312','313'])).

thf('315',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X32 ) )
      | ~ ( m1_connsp_2 @ X33 @ X32 @ X31 )
      | ( r1_tarski @ ( sk_D_2 @ X33 @ X31 @ X32 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_pre_topc @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ( v2_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t8_connsp_2])).

thf('316',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['314','315'])).

thf('317',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ sk_A @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['316','317','318'])).

thf('320',plain,
    ( ( ~ ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['309','319'])).

thf('321',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['302','303'])).

thf('322',plain,
    ( ( ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['320','321'])).

thf('323',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('324',plain,
    ( ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(clc,[status(thm)],['322','323'])).

thf('325',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('326',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ X0 )
        | ~ ( r1_tarski @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ X0 ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['324','325'])).

thf('327',plain,
    ( ( r1_tarski @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['308','326'])).

thf('328',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('329',plain,
    ( ( m1_subset_1 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('331',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_B )
        | ~ ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference('sup-',[status(thm)],['329','330'])).

thf('332',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) ) ) ),
    inference('sup-',[status(thm)],['273','274'])).

thf('333',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( sk_D_2 @ ( sk_D_3 @ ( sk_C @ sk_B @ sk_A ) ) @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ~ ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
      & ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ) ),
    inference(demod,[status(thm)],['331','332'])).

thf('334',plain,
    ( ~ ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_connsp_2 @ ( sk_D_3 @ X35 ) @ sk_A @ X35 ) )
    | ~ ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( m1_subset_1 @ ( sk_D_3 @ X35 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ! [X35: $i] :
          ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ sk_A ) )
          | ~ ( r2_hidden @ X35 @ sk_B )
          | ( r1_tarski @ ( sk_D_3 @ X35 ) @ sk_B ) )
    | ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['307','333'])).

thf('335',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('336',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['335'])).

thf('337',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['335'])).

thf('338',plain,
    ( ( v3_pre_topc @ sk_B @ sk_A )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('339',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( v3_pre_topc @ X19 @ X20 )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 )
      | ~ ( r2_hidden @ X23 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('341',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['339','340'])).

thf('342',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('344',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( v3_pre_topc @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['341','342','343'])).

thf('345',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( v3_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['338','344'])).

thf('346',plain,
    ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['337','345'])).

thf('347',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ X15 )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('348',plain,
    ( ( r2_hidden @ sk_C_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['346','347'])).

thf('349',plain,
    ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['337','345'])).

thf('350',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('351',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['349','350'])).

thf(t5_connsp_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( v3_pre_topc @ B @ A )
                  & ( r2_hidden @ C @ B ) )
               => ( m1_connsp_2 @ B @ A @ C ) ) ) ) ) )).

thf('352',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ~ ( v3_pre_topc @ X25 @ X26 )
      | ~ ( r2_hidden @ X27 @ X25 )
      | ( m1_connsp_2 @ X25 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t5_connsp_2])).

thf('353',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( v2_pre_topc @ sk_A )
        | ~ ( l1_pre_topc @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ X0 )
        | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
        | ~ ( v3_pre_topc @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['351','352'])).

thf('354',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,
    ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['337','345'])).

thf('357',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v3_pre_topc @ X15 @ X17 )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('358',plain,
    ( ( v3_pre_topc @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['356','357'])).

thf('359',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( m1_connsp_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ X0 )
        | ~ ( r2_hidden @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['353','354','355','358'])).

thf('360',plain,
    ( ( ( m1_connsp_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['348','359'])).

thf('361',plain,
    ( ( r2_hidden @ sk_C_1 @ sk_B )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['335'])).

thf('362',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('363',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['361','362'])).

thf('364',plain,
    ( ( ( m1_connsp_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_C_1 )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['360','363'])).

thf('365',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('366',plain,
    ( ( m1_connsp_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['364','365'])).

thf('367',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['349','350'])).

thf('368',plain,
    ( ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X36 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X36 @ sk_B ) )
   <= ! [X36: $i] :
        ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
        | ~ ( m1_connsp_2 @ X36 @ sk_A @ sk_C_1 )
        | ~ ( r1_tarski @ X36 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('369',plain,
    ( ( ~ ( r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_connsp_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_C_1 ) )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X36 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X36 @ sk_B ) )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['367','368'])).

thf('370',plain,
    ( ( zip_tseitin_0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_C_1 @ sk_B @ sk_A )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['337','345'])).

thf('371',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( zip_tseitin_0 @ X15 @ X14 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('372',plain,
    ( ( r1_tarski @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_B )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['370','371'])).

thf('373',plain,
    ( ~ ( m1_connsp_2 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ sk_A @ sk_C_1 )
   <= ( ( v3_pre_topc @ sk_B @ sk_A )
      & ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X36 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X36 @ sk_B ) )
      & ( r2_hidden @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['369','372'])).

thf('374',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ sk_B )
    | ~ ( v3_pre_topc @ sk_B @ sk_A )
    | ~ ! [X36: $i] :
          ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
          | ~ ( m1_connsp_2 @ X36 @ sk_A @ sk_C_1 )
          | ~ ( r1_tarski @ X36 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['366','373'])).

thf('375',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','7','334','336','374'])).


%------------------------------------------------------------------------------
