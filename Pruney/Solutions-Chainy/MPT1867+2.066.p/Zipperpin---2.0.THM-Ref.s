%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ivXEZyWPH7

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:35 EST 2020

% Result     : Theorem 10.89s
% Output     : Refutation 10.89s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 115 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  794 (1172 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_tdlat_3_type,type,(
    v1_tdlat_3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X18: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf('2',plain,(
    ! [X18: $i] :
      ( ( v2_pre_topc @ ( sk_B @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf('3',plain,(
    ! [X18: $i] :
      ( ( v7_struct_0 @ ( sk_B @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf('4',plain,(
    ! [X18: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_pre_topc @ X13 @ X14 )
      | ( l1_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X14 ) ) ),
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
    ! [X15: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v1_tdlat_3 @ X15 )
      | ~ ( v7_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc3_tex_1])).

thf('9',plain,(
    ! [X18: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X18: $i] :
      ( ( m1_pre_topc @ ( sk_B @ X18 ) @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[rc10_tex_2])).

thf(l17_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[l17_tex_2])).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( X21
       != ( u1_struct_0 @ X19 ) )
      | ~ ( v1_tdlat_3 @ X19 )
      | ( v2_tex_2 @ X21 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t26_tex_2])).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v2_tex_2 @ ( u1_struct_0 @ X19 ) @ X20 )
      | ~ ( v1_tdlat_3 @ X19 )
      | ~ ( m1_pre_topc @ X19 @ X20 )
      | ( v2_struct_0 @ X19 ) ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( v2_tex_2 @ X22 @ X23 )
      | ~ ( r1_tarski @ X24 @ X22 )
      | ( v2_tex_2 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X23 ) ) )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_tex_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) )
      | ( v2_tex_2 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_tex_2 @ k1_xboole_0 @ X0 )
      | ~ ( v2_tex_2 @ ( u1_struct_0 @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['34','37'])).

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
    ! [X18: $i] :
      ( ~ ( v2_struct_0 @ ( sk_B @ X18 ) )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('45',plain,(
    ~ ( v2_tex_2 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

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
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ivXEZyWPH7
% 0.15/0.36  % Computer   : n025.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 16:37:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.21/0.37  % Python version: Python 3.6.8
% 0.21/0.37  % Running in FO mode
% 10.89/11.10  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.89/11.10  % Solved by: fo/fo7.sh
% 10.89/11.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.89/11.10  % done 24605 iterations in 10.621s
% 10.89/11.10  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.89/11.10  % SZS output start Refutation
% 10.89/11.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.89/11.10  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 10.89/11.10  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 10.89/11.10  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 10.89/11.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.89/11.10  thf(sk_A_type, type, sk_A: $i).
% 10.89/11.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.89/11.10  thf(sk_B_type, type, sk_B: $i > $i).
% 10.89/11.10  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 10.89/11.10  thf(v1_tdlat_3_type, type, v1_tdlat_3: $i > $o).
% 10.89/11.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.89/11.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.89/11.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 10.89/11.10  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 10.89/11.10  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 10.89/11.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 10.89/11.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.89/11.10  thf(t35_tex_2, conjecture,
% 10.89/11.10    (![A:$i]:
% 10.89/11.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.89/11.10       ( ![B:$i]:
% 10.89/11.10         ( ( ( v1_xboole_0 @ B ) & 
% 10.89/11.10             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.89/11.10           ( v2_tex_2 @ B @ A ) ) ) ))).
% 10.89/11.10  thf(zf_stmt_0, negated_conjecture,
% 10.89/11.10    (~( ![A:$i]:
% 10.89/11.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 10.89/11.10            ( l1_pre_topc @ A ) ) =>
% 10.89/11.10          ( ![B:$i]:
% 10.89/11.10            ( ( ( v1_xboole_0 @ B ) & 
% 10.89/11.10                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 10.89/11.10              ( v2_tex_2 @ B @ A ) ) ) ) )),
% 10.89/11.10    inference('cnf.neg', [status(esa)], [t35_tex_2])).
% 10.89/11.10  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 10.89/11.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.89/11.10  thf(rc10_tex_2, axiom,
% 10.89/11.10    (![A:$i]:
% 10.89/11.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 10.89/11.10       ( ?[B:$i]:
% 10.89/11.10         ( ( v2_pre_topc @ B ) & ( v1_pre_topc @ B ) & ( v7_struct_0 @ B ) & 
% 10.89/11.10           ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) ) ))).
% 10.89/11.10  thf('1', plain,
% 10.89/11.10      (![X18 : $i]:
% 10.89/11.10         ((m1_pre_topc @ (sk_B @ X18) @ X18)
% 10.89/11.10          | ~ (l1_pre_topc @ X18)
% 10.89/11.10          | ~ (v2_pre_topc @ X18)
% 10.89/11.10          | (v2_struct_0 @ X18))),
% 10.89/11.10      inference('cnf', [status(esa)], [rc10_tex_2])).
% 10.89/11.10  thf('2', plain,
% 10.89/11.10      (![X18 : $i]:
% 10.89/11.10         ((v2_pre_topc @ (sk_B @ X18))
% 10.89/11.10          | ~ (l1_pre_topc @ X18)
% 10.89/11.10          | ~ (v2_pre_topc @ X18)
% 10.89/11.10          | (v2_struct_0 @ X18))),
% 10.89/11.10      inference('cnf', [status(esa)], [rc10_tex_2])).
% 10.89/11.10  thf('3', plain,
% 10.89/11.10      (![X18 : $i]:
% 10.89/11.10         ((v7_struct_0 @ (sk_B @ X18))
% 10.89/11.10          | ~ (l1_pre_topc @ X18)
% 10.89/11.10          | ~ (v2_pre_topc @ X18)
% 10.89/11.10          | (v2_struct_0 @ X18))),
% 10.89/11.10      inference('cnf', [status(esa)], [rc10_tex_2])).
% 10.89/11.10  thf('4', plain,
% 10.89/11.10      (![X18 : $i]:
% 10.89/11.10         ((m1_pre_topc @ (sk_B @ X18) @ X18)
% 10.89/11.10          | ~ (l1_pre_topc @ X18)
% 10.89/11.10          | ~ (v2_pre_topc @ X18)
% 10.89/11.10          | (v2_struct_0 @ X18))),
% 10.89/11.10      inference('cnf', [status(esa)], [rc10_tex_2])).
% 10.89/11.10  thf(dt_m1_pre_topc, axiom,
% 10.89/11.10    (![A:$i]:
% 10.89/11.10     ( ( l1_pre_topc @ A ) =>
% 10.89/11.10       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 10.89/11.10  thf('5', plain,
% 10.89/11.10      (![X13 : $i, X14 : $i]:
% 10.89/11.10         (~ (m1_pre_topc @ X13 @ X14)
% 10.89/11.10          | (l1_pre_topc @ X13)
% 10.89/11.10          | ~ (l1_pre_topc @ X14))),
% 10.89/11.10      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 10.89/11.10  thf('6', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (l1_pre_topc @ (sk_B @ X0)))),
% 10.89/11.10      inference('sup-', [status(thm)], ['4', '5'])).
% 10.89/11.10  thf('7', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((l1_pre_topc @ (sk_B @ X0))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['6'])).
% 10.89/11.10  thf(cc3_tex_1, axiom,
% 10.89/11.10    (![A:$i]:
% 10.89/11.10     ( ( l1_pre_topc @ A ) =>
% 10.89/11.10       ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 10.89/11.10           ( ~( v1_tdlat_3 @ A ) ) ) =>
% 10.89/11.10         ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 10.89/11.10           ( v2_pre_topc @ A ) ) ) ))).
% 10.89/11.10  thf('8', plain,
% 10.89/11.10      (![X15 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X15)
% 10.89/11.10          | ~ (v2_pre_topc @ X15)
% 10.89/11.10          | (v1_tdlat_3 @ X15)
% 10.89/11.10          | ~ (v7_struct_0 @ X15)
% 10.89/11.10          | ~ (l1_pre_topc @ X15))),
% 10.89/11.10      inference('cnf', [status(esa)], [cc3_tex_1])).
% 10.89/11.10  thf('9', plain,
% 10.89/11.10      (![X18 : $i]:
% 10.89/11.10         (~ (v2_struct_0 @ (sk_B @ X18))
% 10.89/11.10          | ~ (l1_pre_topc @ X18)
% 10.89/11.10          | ~ (v2_pre_topc @ X18)
% 10.89/11.10          | (v2_struct_0 @ X18))),
% 10.89/11.10      inference('cnf', [status(esa)], [rc10_tex_2])).
% 10.89/11.10  thf('10', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         (~ (l1_pre_topc @ (sk_B @ X0))
% 10.89/11.10          | ~ (v7_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | (v1_tdlat_3 @ (sk_B @ X0))
% 10.89/11.10          | ~ (v2_pre_topc @ (sk_B @ X0))
% 10.89/11.10          | (v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['8', '9'])).
% 10.89/11.10  thf('11', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ (sk_B @ X0))
% 10.89/11.10          | (v1_tdlat_3 @ (sk_B @ X0))
% 10.89/11.10          | ~ (v7_struct_0 @ (sk_B @ X0)))),
% 10.89/11.10      inference('sup-', [status(thm)], ['7', '10'])).
% 10.89/11.10  thf('12', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         (~ (v7_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | (v1_tdlat_3 @ (sk_B @ X0))
% 10.89/11.10          | ~ (v2_pre_topc @ (sk_B @ X0))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['11'])).
% 10.89/11.10  thf('13', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ (sk_B @ X0))
% 10.89/11.10          | (v1_tdlat_3 @ (sk_B @ X0)))),
% 10.89/11.10      inference('sup-', [status(thm)], ['3', '12'])).
% 10.89/11.10  thf('14', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v1_tdlat_3 @ (sk_B @ X0))
% 10.89/11.10          | ~ (v2_pre_topc @ (sk_B @ X0))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['13'])).
% 10.89/11.10  thf('15', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v1_tdlat_3 @ (sk_B @ X0)))),
% 10.89/11.10      inference('sup-', [status(thm)], ['2', '14'])).
% 10.89/11.10  thf('16', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v1_tdlat_3 @ (sk_B @ X0))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['15'])).
% 10.89/11.10  thf('17', plain,
% 10.89/11.10      (![X18 : $i]:
% 10.89/11.10         ((m1_pre_topc @ (sk_B @ X18) @ X18)
% 10.89/11.10          | ~ (l1_pre_topc @ X18)
% 10.89/11.10          | ~ (v2_pre_topc @ X18)
% 10.89/11.10          | (v2_struct_0 @ X18))),
% 10.89/11.10      inference('cnf', [status(esa)], [rc10_tex_2])).
% 10.89/11.10  thf(l17_tex_2, axiom,
% 10.89/11.10    (![A:$i]:
% 10.89/11.10     ( ( l1_pre_topc @ A ) =>
% 10.89/11.10       ( ![B:$i]:
% 10.89/11.10         ( ( m1_pre_topc @ B @ A ) =>
% 10.89/11.10           ( m1_subset_1 @
% 10.89/11.10             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 10.89/11.10  thf('18', plain,
% 10.89/11.10      (![X16 : $i, X17 : $i]:
% 10.89/11.10         (~ (m1_pre_topc @ X16 @ X17)
% 10.89/11.10          | (m1_subset_1 @ (u1_struct_0 @ X16) @ 
% 10.89/11.10             (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 10.89/11.10          | ~ (l1_pre_topc @ X17))),
% 10.89/11.10      inference('cnf', [status(esa)], [l17_tex_2])).
% 10.89/11.10  thf('19', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 10.89/11.10             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 10.89/11.10      inference('sup-', [status(thm)], ['17', '18'])).
% 10.89/11.10  thf('20', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 10.89/11.10           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['19'])).
% 10.89/11.10  thf(t26_tex_2, axiom,
% 10.89/11.10    (![A:$i]:
% 10.89/11.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) ) =>
% 10.89/11.10       ( ![B:$i]:
% 10.89/11.10         ( ( ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) ) =>
% 10.89/11.10           ( ![C:$i]:
% 10.89/11.10             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.89/11.10               ( ( ( C ) = ( u1_struct_0 @ B ) ) =>
% 10.89/11.10                 ( ( v2_tex_2 @ C @ A ) <=> ( v1_tdlat_3 @ B ) ) ) ) ) ) ) ))).
% 10.89/11.10  thf('21', plain,
% 10.89/11.10      (![X19 : $i, X20 : $i, X21 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X19)
% 10.89/11.10          | ~ (m1_pre_topc @ X19 @ X20)
% 10.89/11.10          | ((X21) != (u1_struct_0 @ X19))
% 10.89/11.10          | ~ (v1_tdlat_3 @ X19)
% 10.89/11.10          | (v2_tex_2 @ X21 @ X20)
% 10.89/11.10          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 10.89/11.10          | ~ (l1_pre_topc @ X20)
% 10.89/11.10          | (v2_struct_0 @ X20))),
% 10.89/11.10      inference('cnf', [status(esa)], [t26_tex_2])).
% 10.89/11.10  thf('22', plain,
% 10.89/11.10      (![X19 : $i, X20 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X20)
% 10.89/11.10          | ~ (l1_pre_topc @ X20)
% 10.89/11.10          | ~ (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 10.89/11.10               (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 10.89/11.10          | (v2_tex_2 @ (u1_struct_0 @ X19) @ X20)
% 10.89/11.10          | ~ (v1_tdlat_3 @ X19)
% 10.89/11.10          | ~ (m1_pre_topc @ X19 @ X20)
% 10.89/11.10          | (v2_struct_0 @ X19))),
% 10.89/11.10      inference('simplify', [status(thm)], ['21'])).
% 10.89/11.10  thf('23', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 10.89/11.10          | ~ (v1_tdlat_3 @ (sk_B @ X0))
% 10.89/11.10          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['20', '22'])).
% 10.89/11.10  thf('24', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 10.89/11.10          | ~ (v1_tdlat_3 @ (sk_B @ X0))
% 10.89/11.10          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 10.89/11.10          | (v2_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['23'])).
% 10.89/11.10  thf('25', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 10.89/11.10          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['16', '24'])).
% 10.89/11.10  thf('26', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 10.89/11.10          | ~ (m1_pre_topc @ (sk_B @ X0) @ X0)
% 10.89/11.10          | (v2_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['25'])).
% 10.89/11.10  thf('27', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['1', '26'])).
% 10.89/11.10  thf('28', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 10.89/11.10          | (v2_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['27'])).
% 10.89/11.10  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.89/11.10  thf('29', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 10.89/11.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.89/11.10  thf('30', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((m1_subset_1 @ (u1_struct_0 @ (sk_B @ X0)) @ 
% 10.89/11.10           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['19'])).
% 10.89/11.10  thf(t28_tex_2, axiom,
% 10.89/11.10    (![A:$i]:
% 10.89/11.10     ( ( l1_pre_topc @ A ) =>
% 10.89/11.10       ( ![B:$i]:
% 10.89/11.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.89/11.10           ( ![C:$i]:
% 10.89/11.10             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.89/11.10               ( ( ( r1_tarski @ C @ B ) & ( v2_tex_2 @ B @ A ) ) =>
% 10.89/11.10                 ( v2_tex_2 @ C @ A ) ) ) ) ) ) ))).
% 10.89/11.10  thf('31', plain,
% 10.89/11.10      (![X22 : $i, X23 : $i, X24 : $i]:
% 10.89/11.10         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 10.89/11.10          | ~ (v2_tex_2 @ X22 @ X23)
% 10.89/11.10          | ~ (r1_tarski @ X24 @ X22)
% 10.89/11.10          | (v2_tex_2 @ X24 @ X23)
% 10.89/11.10          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X23)))
% 10.89/11.10          | ~ (l1_pre_topc @ X23))),
% 10.89/11.10      inference('cnf', [status(esa)], [t28_tex_2])).
% 10.89/11.10  thf('32', plain,
% 10.89/11.10      (![X0 : $i, X1 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.89/11.10          | (v2_tex_2 @ X1 @ X0)
% 10.89/11.10          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ (sk_B @ X0)))
% 10.89/11.10          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['30', '31'])).
% 10.89/11.10  thf('33', plain,
% 10.89/11.10      (![X0 : $i, X1 : $i]:
% 10.89/11.10         (~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0)
% 10.89/11.10          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ (sk_B @ X0)))
% 10.89/11.10          | (v2_tex_2 @ X1 @ X0)
% 10.89/11.10          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['32'])).
% 10.89/11.10  thf('34', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 10.89/11.10          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.89/11.10          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['29', '33'])).
% 10.89/11.10  thf('35', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 10.89/11.10      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.89/11.10  thf(t3_subset, axiom,
% 10.89/11.10    (![A:$i,B:$i]:
% 10.89/11.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 10.89/11.10  thf('36', plain,
% 10.89/11.10      (![X10 : $i, X12 : $i]:
% 10.89/11.10         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 10.89/11.10      inference('cnf', [status(esa)], [t3_subset])).
% 10.89/11.10  thf('37', plain,
% 10.89/11.10      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['35', '36'])).
% 10.89/11.10  thf('38', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.89/11.10          | ~ (v2_tex_2 @ (u1_struct_0 @ (sk_B @ X0)) @ X0))),
% 10.89/11.10      inference('demod', [status(thm)], ['34', '37'])).
% 10.89/11.10  thf('39', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['28', '38'])).
% 10.89/11.10  thf('40', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 10.89/11.10          | (v2_struct_0 @ (sk_B @ X0))
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['39'])).
% 10.89/11.10  thf('41', plain,
% 10.89/11.10      (![X18 : $i]:
% 10.89/11.10         (~ (v2_struct_0 @ (sk_B @ X18))
% 10.89/11.10          | ~ (l1_pre_topc @ X18)
% 10.89/11.10          | ~ (v2_pre_topc @ X18)
% 10.89/11.10          | (v2_struct_0 @ X18))),
% 10.89/11.10      inference('cnf', [status(esa)], [rc10_tex_2])).
% 10.89/11.10  thf('42', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | (v2_tex_2 @ k1_xboole_0 @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['40', '41'])).
% 10.89/11.10  thf('43', plain,
% 10.89/11.10      (![X0 : $i]:
% 10.89/11.10         ((v2_tex_2 @ k1_xboole_0 @ X0)
% 10.89/11.10          | ~ (l1_pre_topc @ X0)
% 10.89/11.10          | ~ (v2_pre_topc @ X0)
% 10.89/11.10          | (v2_struct_0 @ X0))),
% 10.89/11.10      inference('simplify', [status(thm)], ['42'])).
% 10.89/11.10  thf(t6_boole, axiom,
% 10.89/11.10    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 10.89/11.10  thf('44', plain,
% 10.89/11.10      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 10.89/11.10      inference('cnf', [status(esa)], [t6_boole])).
% 10.89/11.10  thf('45', plain, (~ (v2_tex_2 @ sk_B_1 @ sk_A)),
% 10.89/11.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.89/11.10  thf('46', plain, ((v1_xboole_0 @ sk_B_1)),
% 10.89/11.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.89/11.10  thf('47', plain,
% 10.89/11.10      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X9))),
% 10.89/11.10      inference('cnf', [status(esa)], [t6_boole])).
% 10.89/11.10  thf('48', plain, (((sk_B_1) = (k1_xboole_0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['46', '47'])).
% 10.89/11.10  thf('49', plain, (~ (v2_tex_2 @ k1_xboole_0 @ sk_A)),
% 10.89/11.10      inference('demod', [status(thm)], ['45', '48'])).
% 10.89/11.10  thf('50', plain,
% 10.89/11.10      (![X0 : $i]: (~ (v2_tex_2 @ X0 @ sk_A) | ~ (v1_xboole_0 @ X0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['44', '49'])).
% 10.89/11.10  thf('51', plain,
% 10.89/11.10      (((v2_struct_0 @ sk_A)
% 10.89/11.10        | ~ (v2_pre_topc @ sk_A)
% 10.89/11.10        | ~ (l1_pre_topc @ sk_A)
% 10.89/11.10        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['43', '50'])).
% 10.89/11.10  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 10.89/11.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.89/11.10  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 10.89/11.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.89/11.10  thf('54', plain, ((v1_xboole_0 @ sk_B_1)),
% 10.89/11.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.89/11.10  thf('55', plain, (((sk_B_1) = (k1_xboole_0))),
% 10.89/11.10      inference('sup-', [status(thm)], ['46', '47'])).
% 10.89/11.10  thf('56', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 10.89/11.10      inference('demod', [status(thm)], ['54', '55'])).
% 10.89/11.10  thf('57', plain, ((v2_struct_0 @ sk_A)),
% 10.89/11.10      inference('demod', [status(thm)], ['51', '52', '53', '56'])).
% 10.89/11.10  thf('58', plain, ($false), inference('demod', [status(thm)], ['0', '57'])).
% 10.89/11.10  
% 10.89/11.10  % SZS output end Refutation
% 10.89/11.10  
% 10.89/11.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
