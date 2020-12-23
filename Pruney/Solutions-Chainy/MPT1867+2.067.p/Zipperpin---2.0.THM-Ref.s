%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3j3PXBydDX

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 115 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  796 (1175 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

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
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc10_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ? [B: $i] :
          ( ( v2_pre_topc @ B )
          & ( v1_pre_topc @ B )
          & ( v7_struct_0 @ B )
          & ~ ( v2_struct_0 @ B )
          & ( m1_pre_topc @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( v2_pre_topc @ ( sk_B @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf('3',plain,(
    ! [X13: $i] :
      ( ( v7_struct_0 @ ( sk_B @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf('4',plain,(
    ! [X13: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_pre_topc @ X8 @ X9 )
      | ( l1_pre_topc @ X8 )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( l1_pre_topc @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( l1_pre_topc @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(cc3_tex_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ~ ( v1_tdlat_3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ~ ( v7_struct_0 @ A )
          & ( v2_pre_topc @ A ) ) ) ) )).

thf('8',plain,(
    ! [X12: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v1_tdlat_3 @ X12 )
      | ~ ( v7_struct_0 @ X12 )
      | ~ ( l1_pre_topc @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_tex_1])).

thf('9',plain,(
    ! [X13: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ ( sk_B @ X0 ) )
      | ~ ( v7_struct_0 @ ( sk_B @ X0 ) )
      | ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ ( sk_B @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ ( sk_B @ X0 ) )
      | ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ~ ( v7_struct_0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v7_struct_0 @ ( sk_B @ X0 ) )
      | ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ ( sk_B @ X0 ) )
      | ( v1_tdlat_3 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ~ ( v2_pre_topc @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v1_tdlat_3 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X13: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X13 ) @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X10 @ X11 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_pre_topc @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

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

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( X16
       != ( u1_struct_0 @ X14 ) )
      | ~ ( v1_tdlat_3 @ X14 )
      | ( v2_tex_2 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( l1_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X14 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X14 ) @ X15 )
      | ~ ( v1_tdlat_3 @ X14 )
      | ~ ( m1_pre_topc @ X14 @ X15 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( v1_tdlat_3 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( m1_pre_topc @ ( sk_B @ X0 ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

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

thf('33',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( v2_tex_2 @ X17 @ X18 )
      | ~ ( r1_tarski @ X19 @ X17 )
      | ( v2_tex_2 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ ( sk_B @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X13: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X13 ) )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('45',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('48',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_tex_2 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['46','47'])).

thf('56',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['51','52','53','56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['0','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3j3PXBydDX
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 09:54:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 114 iterations in 0.060s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.22/0.52  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.22/0.52  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 0.22/0.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.22/0.52  thf(t35_tex_2, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_xboole_0 @ B ) & 
% 0.22/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52           ( v2_tex_2 @ B @ A ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52            ( l1_pre_topc @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( ( v1_xboole_0 @ B ) & 
% 0.22/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.22/0.52              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 0.22/0.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(rc10_tex_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ?[B:$i]:
% 0.22/0.52         ( ( v2_pre_topc @ B ) & ( v1_pre_topc @ B ) & ( v7_struct_0 @ B ) & 
% 0.22/0.52           ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X13 : $i]:
% 0.22/0.52         ((m1_pre_topc @ (sk_B @ X13) @ X13)
% 0.22/0.52          | ~ (l1_pre_topc @ X13)
% 0.22/0.52          | ~ (v2_pre_topc @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc10_tex_2])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X13 : $i]:
% 0.22/0.52         ((v2_pre_topc @ (sk_B @ X13))
% 0.22/0.52          | ~ (l1_pre_topc @ X13)
% 0.22/0.52          | ~ (v2_pre_topc @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc10_tex_2])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X13 : $i]:
% 0.22/0.52         ((v7_struct_0 @ (sk_B @ X13))
% 0.22/0.52          | ~ (l1_pre_topc @ X13)
% 0.22/0.52          | ~ (v2_pre_topc @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc10_tex_2])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X13 : $i]:
% 0.22/0.52         ((m1_pre_topc @ (sk_B @ X13) @ X13)
% 0.22/0.52          | ~ (l1_pre_topc @ X13)
% 0.22/0.52          | ~ (v2_pre_topc @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc10_tex_2])).
% 0.22/0.52  thf(dt_m1_pre_topc, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X8 @ X9) | (l1_pre_topc @ X8) | ~ (l1_pre_topc @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (l1_pre_topc @ (sk_B @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((l1_pre_topc @ (sk_B @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.52  thf(cc3_tex_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.22/0.52           ( ~( v1_tdlat_3 @ A ) ) ) =>
% 0.22/0.52         ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.22/0.52           ( v2_pre_topc @ A ) ) ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X12 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X12)
% 0.22/0.52          | ~ (v2_pre_topc @ X12)
% 0.22/0.52          | (v1_tdlat_3 @ X12)
% 0.22/0.52          | ~ (v7_struct_0 @ X12)
% 0.22/0.52          | ~ (l1_pre_topc @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc3_tex_1])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      (![X13 : $i]:
% 0.22/0.52         (~ (v2_struct_0 @ (sk_B @ X13))
% 0.22/0.52          | ~ (l1_pre_topc @ X13)
% 0.22/0.52          | ~ (v2_pre_topc @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc10_tex_2])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (l1_pre_topc @ (sk_B @ X0))
% 0.22/0.52          | ~ (v7_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | (v1_tdlat_3 @ (sk_B @ X0))
% 0.22/0.52          | ~ (v2_pre_topc @ (sk_B @ X0))
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ (sk_B @ X0))
% 0.22/0.52          | (v1_tdlat_3 @ (sk_B @ X0))
% 0.22/0.52          | ~ (v7_struct_0 @ (sk_B @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['7', '10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (v7_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | (v1_tdlat_3 @ (sk_B @ X0))
% 0.22/0.52          | ~ (v2_pre_topc @ (sk_B @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ (sk_B @ X0))
% 0.22/0.52          | (v1_tdlat_3 @ (sk_B @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '12'])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_tdlat_3 @ (sk_B @ X0))
% 0.22/0.52          | ~ (v2_pre_topc @ (sk_B @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v1_tdlat_3 @ (sk_B @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_tdlat_3 @ (sk_B @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X13 : $i]:
% 0.22/0.52         ((m1_pre_topc @ (sk_B @ X13) @ X13)
% 0.22/0.52          | ~ (l1_pre_topc @ X13)
% 0.22/0.52          | ~ (v2_pre_topc @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc10_tex_2])).
% 0.22/0.52  thf(t1_tsep_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_pre_topc @ B @ A ) =>
% 0.22/0.52           ( m1_subset_1 @
% 0.22/0.52             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         (~ (m1_pre_topc @ X10 @ X11)
% 0.22/0.52          | (m1_subset_1 @ (u1_struct_0 @ X10) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.52          | ~ (l1_pre_topc @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.22/0.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.52  thf(t26_tex_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 0.22/0.52                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X14)
% 0.22/0.52          | ~ (m1_pre_topc @ X14 @ X15)
% 0.22/0.52          | ((X16) != (u1_struct_0 @ X14))
% 0.22/0.52          | ~ (v1_tdlat_3 @ X14)
% 0.22/0.52          | (v2_tex_2 @ X16 @ X15)
% 0.22/0.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.52          | ~ (l1_pre_topc @ X15)
% 0.22/0.52          | (v2_struct_0 @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [t26_tex_2])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X14 : $i, X15 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X15)
% 0.22/0.52          | ~ (l1_pre_topc @ X15)
% 0.22/0.52          | ~ (m1_subset_1 @ (u1_struct_0 @ X14) @ 
% 0.22/0.52               (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.22/0.52          | (v2_tex_2 @ (u1_struct_0 @ X14) @ X15)
% 0.22/0.52          | ~ (v1_tdlat_3 @ X14)
% 0.22/0.52          | ~ (m1_pre_topc @ X14 @ X15)
% 0.22/0.52          | (v2_struct_0 @ X14))),
% 0.22/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.52          | ~ (v1_tdlat_3 @ (sk_B @ X0))
% 0.22/0.52          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.22/0.52          | ~ (v1_tdlat_3 @ (sk_B @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.52          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['16', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.22/0.52          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 0.22/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.22/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.52  thf(t4_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf(t3_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.52  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.52  thf(t28_tex_2, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( l1_pre_topc @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.52               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 0.22/0.52                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.52          | ~ (v2_tex_2 @ X17 @ X18)
% 0.22/0.52          | ~ (r1_tarski @ X19 @ X17)
% 0.22/0.52          | (v2_tex_2 @ X19 @ X18)
% 0.22/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.22/0.52          | ~ (l1_pre_topc @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t28_tex_2])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | (v2_tex_2 @ X1 @ X0)
% 0.22/0.52          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ (sk_B @ X0)))
% 0.22/0.52          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 0.22/0.52          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ (sk_B @ X0)))
% 0.22/0.52          | (v2_tex_2 @ X1 @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['31', '35'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 0.22/0.52      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ (sk_B @ X0))
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X13 : $i]:
% 0.22/0.52         (~ (v2_struct_0 @ (sk_B @ X13))
% 0.22/0.52          | ~ (l1_pre_topc @ X13)
% 0.22/0.52          | ~ (v2_pre_topc @ X13)
% 0.22/0.52          | (v2_struct_0 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [rc10_tex_2])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['40', '41'])).
% 0.22/0.52  thf('43', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 0.22/0.52          | ~ (l1_pre_topc @ X0)
% 0.22/0.52          | ~ (v2_pre_topc @ X0)
% 0.22/0.52          | (v2_struct_0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.52  thf(l13_xboole_0, axiom,
% 0.22/0.52    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.52  thf('45', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.52  thf('48', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('49', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['45', '48'])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['44', '49'])).
% 0.22/0.52  thf('51', plain,
% 0.22/0.52      (((v2_struct_0 @ sk_A)
% 0.22/0.52        | ~ (v2_pre_topc @ sk_A)
% 0.22/0.52        | ~ (l1_pre_topc @ sk_A)
% 0.22/0.52        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['43', '50'])).
% 0.22/0.52  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('54', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('55', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.52  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.52      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.52  thf('57', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['51', '52', '53', '56'])).
% 0.22/0.52  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
