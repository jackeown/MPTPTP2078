%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7wr4l6gwW9

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 618 expanded)
%              Number of leaves         :   21 ( 188 expanded)
%              Depth                    :   17
%              Number of atoms          : 1376 (13734 expanded)
%              Number of equality atoms :   12 (  92 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t39_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A )
                  & ( v2_tex_2 @ B @ A )
                  & ( v2_tex_2 @ C @ A ) )
               => ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A )
                    & ( v2_tex_2 @ B @ A )
                    & ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_tex_2])).

thf('0',plain,(
    ~ ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ~ ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A ) )
                 => ( ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A )
                    & ( v4_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ( v4_pre_topc @ B @ A )
                    & ( v4_pre_topc @ C @ A )
                    & ( v2_tex_2 @ B @ A )
                    & ( v2_tex_2 @ C @ A ) )
                 => ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ~ ( v2_tex_2 @ X10 @ X9 )
      | ~ ( v4_pre_topc @ X11 @ X9 )
      | ~ ( v2_tex_2 @ X11 @ X9 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X9 ) @ X10 @ X11 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_tex_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    v4_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('21',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    ~ ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('23',plain,(
    m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ~ ( v2_tex_2 @ X10 @ X9 )
      | ~ ( v4_pre_topc @ X11 @ X9 )
      | ~ ( v2_tex_2 @ X11 @ X9 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X9 ) @ X10 @ X11 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_tex_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( v4_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    v4_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('38',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( ( k4_subset_1 @ X1 @ X0 @ X2 )
        = ( k2_xboole_0 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ X0 )
        = ( k2_xboole_0 @ ( sk_B @ sk_A ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) )
    = ( k2_xboole_0 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','40'])).

thf('42',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v4_pre_topc @ ( k4_subset_1 @ ( u1_struct_0 @ X9 ) @ ( sk_B @ X9 ) @ ( sk_C @ X9 ) ) @ X9 )
      | ~ ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X9 ) @ ( sk_B @ X9 ) @ ( sk_C @ X9 ) ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ~ ( v2_tex_2 @ X10 @ X9 )
      | ~ ( v4_pre_topc @ X11 @ X9 )
      | ~ ( v2_tex_2 @ X11 @ X9 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X9 ) @ X10 @ X11 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_tex_2])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_pre_topc @ ( k2_xboole_0 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X1 @ sk_A )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('45',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(fc5_tops_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A )
        & ( v4_pre_topc @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( v4_pre_topc @ C @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( v4_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ) )).

thf('46',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v4_pre_topc @ X3 @ X4 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 )
      | ~ ( v4_pre_topc @ X5 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ( v4_pre_topc @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc5_tops_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k2_xboole_0 @ ( sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_pre_topc @ ( sk_B @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ~ ( v2_tex_2 @ X10 @ X9 )
      | ~ ( v4_pre_topc @ X11 @ X9 )
      | ~ ( v2_tex_2 @ X11 @ X9 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X9 ) @ X10 @ X11 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_tex_2])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
      | ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55','56'])).

thf('58',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','57'])).

thf('59',plain,(
    v4_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('62',plain,
    ( ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','61'])).

thf('63',plain,(
    ~ ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('64',plain,(
    v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( k2_xboole_0 @ ( sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49','64'])).

thf('66',plain,
    ( ~ ( v4_pre_topc @ ( sk_C @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k2_xboole_0 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['44','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v4_pre_topc @ ( sk_C @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v4_pre_topc @ X10 @ X9 )
      | ~ ( v2_tex_2 @ X10 @ X9 )
      | ~ ( v4_pre_topc @ X11 @ X9 )
      | ~ ( v2_tex_2 @ X11 @ X9 )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ X9 ) @ X10 @ X11 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[t31_tex_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
      | ~ ( v4_pre_topc @ sk_B_1 @ sk_A )
      | ( v4_pre_topc @ ( sk_C @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ( v4_pre_topc @ ( sk_C @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,
    ( ( v4_pre_topc @ ( sk_C @ sk_A ) @ sk_A )
    | ~ ( v4_pre_topc @ sk_C_1 @ sk_A )
    | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
    | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['67','74'])).

thf('76',plain,(
    v4_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('79',plain,
    ( ( v4_pre_topc @ ( sk_C @ sk_A ) @ sk_A )
    | ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,(
    ~ ( v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('81',plain,(
    v4_pre_topc @ ( sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    v4_pre_topc @ ( k2_xboole_0 @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['66','81'])).

thf('83',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ ( sk_C @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('85',plain,(
    m1_subset_1 @ ( sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf(t35_tops_1,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ( v4_pre_topc @ B @ A )
                  & ( v4_pre_topc @ C @ A ) )
               => ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) )).

thf('86',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( v4_pre_topc @ X6 @ X7 )
      | ~ ( v4_pre_topc @ X8 @ X7 )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ X7 ) @ X6 @ X8 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( v2_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[t35_tops_1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v4_pre_topc @ ( sk_B @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['62','63'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,
    ( ~ ( v4_pre_topc @ ( sk_C @ sk_A ) @ sk_A )
    | ( v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    v4_pre_topc @ ( sk_C @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['79','80'])).

thf('94',plain,(
    v4_pre_topc @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( sk_B @ sk_A ) @ ( sk_C @ sk_A ) ) @ sk_A ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X1 @ sk_A )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['43','82','83','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ~ ( v4_pre_topc @ sk_C_1 @ sk_A )
      | ~ ( v2_tex_2 @ sk_C_1 @ sk_A )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','95'])).

thf('97',plain,(
    v4_pre_topc @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_tex_2 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v4_pre_topc @ X0 @ sk_A )
      | ~ ( v2_tex_2 @ X0 @ sk_A )
      | ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 ) @ sk_A )
    | ~ ( v2_tex_2 @ sk_B_1 @ sk_A )
    | ~ ( v4_pre_topc @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','99'])).

thf('101',plain,
    ( ( k4_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('102',plain,(
    v2_tex_2 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v4_pre_topc @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v2_tex_2 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    $false ),
    inference(demod,[status(thm)],['6','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7wr4l6gwW9
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 124 iterations in 0.042s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.48  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.48  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.20/0.48  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.48  thf(t39_tex_2, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) & 
% 0.20/0.48                   ( v2_tex_2 @ B @ A ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.20/0.48                 ( v2_tex_2 @ ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.48            ( l1_pre_topc @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48              ( ![C:$i]:
% 0.20/0.48                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                  ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) & 
% 0.20/0.48                      ( v2_tex_2 @ B @ A ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.20/0.48                    ( v2_tex_2 @
% 0.20/0.48                      ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t39_tex_2])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (~ (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.20/0.48          sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(redefinition_k4_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.48       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 0.20/0.48          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k2_xboole_0 @ X0 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0)
% 0.20/0.48            = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.20/0.48         = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('6', plain, (~ (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t31_tex_2, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_pre_topc @ A ) =>
% 0.20/0.48       ( ( ![B:$i]:
% 0.20/0.48           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.48                   ( ( v4_pre_topc @
% 0.20/0.48                       ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) & 
% 0.20/0.48                     ( v4_pre_topc @
% 0.20/0.48                       ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) =>
% 0.20/0.48         ( ![B:$i]:
% 0.20/0.48           ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48             ( ![C:$i]:
% 0.20/0.48               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48                 ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) & 
% 0.20/0.48                     ( v2_tex_2 @ B @ A ) & ( v2_tex_2 @ C @ A ) ) =>
% 0.20/0.48                   ( v2_tex_2 @
% 0.20/0.48                     ( k4_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (sk_C @ X9) @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (v4_pre_topc @ X10 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X10 @ X9)
% 0.20/0.48          | ~ (v4_pre_topc @ X11 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X11 @ X9)
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X9) @ X10 @ X11) @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_tex_2])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('14', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('15', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | (m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['12', '13', '14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_C_1 @ sk_A)
% 0.20/0.48        | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.20/0.48        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['9', '16'])).
% 0.20/0.48  thf('18', plain, ((v4_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.20/0.48         = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.20/0.48  thf('22', plain, (~ (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((m1_subset_1 @ (sk_B @ X9) @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (v4_pre_topc @ X10 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X10 @ X9)
% 0.20/0.48          | ~ (v4_pre_topc @ X11 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X11 @ X9)
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X9) @ X10 @ X11) @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_tex_2])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.48          | (m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('29', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | (m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | ~ (v4_pre_topc @ sk_C_1 @ sk_A)
% 0.20/0.48        | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.20/0.48        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['24', '31'])).
% 0.20/0.48  thf('33', plain, ((v4_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.20/0.48         = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      (((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.20/0.48  thf('37', plain, (~ (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X1))
% 0.20/0.48          | ((k4_subset_1 @ X1 @ X0 @ X2) = (k2_xboole_0 @ X0 @ X2)))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ X0)
% 0.20/0.48            = (k2_xboole_0 @ (sk_B @ sk_A) @ X0))
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.48  thf('41', plain,
% 0.20/0.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ (sk_C @ sk_A))
% 0.20/0.48         = (k2_xboole_0 @ (sk_B @ sk_A) @ (sk_C @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '40'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (v4_pre_topc @ 
% 0.20/0.48             (k4_subset_1 @ (u1_struct_0 @ X9) @ (sk_B @ X9) @ (sk_C @ X9)) @ 
% 0.20/0.48             X9)
% 0.20/0.48          | ~ (v4_pre_topc @ 
% 0.20/0.48               (k9_subset_1 @ (u1_struct_0 @ X9) @ (sk_B @ X9) @ (sk_C @ X9)) @ 
% 0.20/0.48               X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (v4_pre_topc @ X10 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X10 @ X9)
% 0.20/0.48          | ~ (v4_pre_topc @ X11 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X11 @ X9)
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X9) @ X10 @ X11) @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_tex_2])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v4_pre_topc @ (k2_xboole_0 @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0) @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X1 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (v4_pre_topc @ 
% 0.20/0.48               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ 
% 0.20/0.48                (sk_C @ sk_A)) @ 
% 0.20/0.48               sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf(fc5_tops_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) & ( v4_pre_topc @ B @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.48         ( v4_pre_topc @ C @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.48       ( v4_pre_topc @ ( k2_xboole_0 @ B @ C ) @ A ) ))).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | ~ (v4_pre_topc @ X3 @ X4)
% 0.20/0.48          | ~ (l1_pre_topc @ X4)
% 0.20/0.48          | ~ (v2_pre_topc @ X4)
% 0.20/0.48          | ~ (v4_pre_topc @ X5 @ X4)
% 0.20/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.20/0.48          | (v4_pre_topc @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc5_tops_1])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v4_pre_topc @ (k2_xboole_0 @ (sk_B @ sk_A) @ X0) @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('52', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((v4_pre_topc @ (sk_B @ X9) @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (v4_pre_topc @ X10 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X10 @ X9)
% 0.20/0.48          | ~ (v4_pre_topc @ X11 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X11 @ X9)
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X9) @ X10 @ X11) @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_tex_2])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.48          | (v4_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.48  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | (v4_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['53', '54', '55', '56'])).
% 0.20/0.48  thf('58', plain,
% 0.20/0.48      (((v4_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | ~ (v4_pre_topc @ sk_C_1 @ sk_A)
% 0.20/0.48        | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.20/0.48        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['50', '57'])).
% 0.20/0.48  thf('59', plain, ((v4_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('60', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('61', plain,
% 0.20/0.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.20/0.48         = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (((v4_pre_topc @ (sk_B @ sk_A) @ sk_A)
% 0.20/0.48        | (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['58', '59', '60', '61'])).
% 0.20/0.48  thf('63', plain, (~ (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.48  thf('64', plain, ((v4_pre_topc @ (sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('65', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v4_pre_topc @ (k2_xboole_0 @ (sk_B @ sk_A) @ X0) @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['47', '48', '49', '64'])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      ((~ (v4_pre_topc @ (sk_C @ sk_A) @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ (k2_xboole_0 @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '65'])).
% 0.20/0.48  thf('67', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('68', plain,
% 0.20/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('69', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         ((v4_pre_topc @ (sk_C @ X9) @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (v4_pre_topc @ X10 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X10 @ X9)
% 0.20/0.48          | ~ (v4_pre_topc @ X11 @ X9)
% 0.20/0.48          | ~ (v2_tex_2 @ X11 @ X9)
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ X9) @ X10 @ X11) @ X9)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.20/0.48          | ~ (l1_pre_topc @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t31_tex_2])).
% 0.20/0.48  thf('70', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ sk_B_1 @ sk_A)
% 0.20/0.48          | (v4_pre_topc @ (sk_C @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['68', '69'])).
% 0.20/0.48  thf('71', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('72', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('73', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('74', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ X0) @ 
% 0.20/0.48             sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | (v4_pre_topc @ (sk_C @ sk_A) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.20/0.48  thf('75', plain,
% 0.20/0.48      (((v4_pre_topc @ (sk_C @ sk_A) @ sk_A)
% 0.20/0.48        | ~ (v4_pre_topc @ sk_C_1 @ sk_A)
% 0.20/0.48        | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.20/0.48        | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['67', '74'])).
% 0.20/0.48  thf('76', plain, ((v4_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('77', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('78', plain,
% 0.20/0.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.20/0.48         = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('79', plain,
% 0.20/0.48      (((v4_pre_topc @ (sk_C @ sk_A) @ sk_A)
% 0.20/0.48        | (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.20/0.48  thf('80', plain, (~ (v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '5'])).
% 0.20/0.48  thf('81', plain, ((v4_pre_topc @ (sk_C @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['79', '80'])).
% 0.20/0.48  thf('82', plain,
% 0.20/0.48      ((v4_pre_topc @ (k2_xboole_0 @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['66', '81'])).
% 0.20/0.48  thf('83', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('84', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_C @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['21', '22'])).
% 0.20/0.48  thf('85', plain,
% 0.20/0.48      ((m1_subset_1 @ (sk_B @ sk_A) @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf(t35_tops_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48           ( ![C:$i]:
% 0.20/0.48             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48               ( ( ( v4_pre_topc @ B @ A ) & ( v4_pre_topc @ C @ A ) ) =>
% 0.20/0.48                 ( v4_pre_topc @
% 0.20/0.48                   ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) @ A ) ) ) ) ) ) ))).
% 0.20/0.48  thf('86', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (v4_pre_topc @ X6 @ X7)
% 0.20/0.48          | ~ (v4_pre_topc @ X8 @ X7)
% 0.20/0.48          | (v4_pre_topc @ (k9_subset_1 @ (u1_struct_0 @ X7) @ X6 @ X8) @ X7)
% 0.20/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.20/0.48          | ~ (l1_pre_topc @ X7)
% 0.20/0.48          | ~ (v2_pre_topc @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t35_tops_1])).
% 0.20/0.48  thf('87', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v2_pre_topc @ sk_A)
% 0.20/0.48          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ X0) @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ (sk_B @ sk_A) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['85', '86'])).
% 0.20/0.48  thf('88', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('89', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('90', plain, ((v4_pre_topc @ (sk_B @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['62', '63'])).
% 0.20/0.48  thf('91', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v4_pre_topc @ 
% 0.20/0.48             (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ X0) @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 0.20/0.48  thf('92', plain,
% 0.20/0.48      ((~ (v4_pre_topc @ (sk_C @ sk_A) @ sk_A)
% 0.20/0.48        | (v4_pre_topc @ 
% 0.20/0.48           (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ 
% 0.20/0.48           sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['84', '91'])).
% 0.20/0.48  thf('93', plain, ((v4_pre_topc @ (sk_C @ sk_A) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['79', '80'])).
% 0.20/0.48  thf('94', plain,
% 0.20/0.48      ((v4_pre_topc @ 
% 0.20/0.48        (k9_subset_1 @ (u1_struct_0 @ sk_A) @ (sk_B @ sk_A) @ (sk_C @ sk_A)) @ 
% 0.20/0.48        sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['92', '93'])).
% 0.20/0.48  thf('95', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X1 @ X0) @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X1 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ X1 @ sk_A)
% 0.20/0.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.20/0.48      inference('demod', [status(thm)], ['43', '82', '83', '94'])).
% 0.20/0.48  thf('96', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | ~ (v4_pre_topc @ sk_C_1 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ sk_C_1 @ sk_A)
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1) @ 
% 0.20/0.48             sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '95'])).
% 0.20/0.48  thf('97', plain, ((v4_pre_topc @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('98', plain, ((v2_tex_2 @ sk_C_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('99', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48          | ~ (v4_pre_topc @ X0 @ sk_A)
% 0.20/0.48          | ~ (v2_tex_2 @ X0 @ sk_A)
% 0.20/0.48          | (v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ sk_C_1) @ 
% 0.20/0.48             sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.20/0.48  thf('100', plain,
% 0.20/0.48      (((v2_tex_2 @ (k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1) @ 
% 0.20/0.48         sk_A)
% 0.20/0.48        | ~ (v2_tex_2 @ sk_B_1 @ sk_A)
% 0.20/0.48        | ~ (v4_pre_topc @ sk_B_1 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['7', '99'])).
% 0.20/0.48  thf('101', plain,
% 0.20/0.48      (((k4_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1 @ sk_C_1)
% 0.20/0.48         = (k2_xboole_0 @ sk_B_1 @ sk_C_1))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.48  thf('102', plain, ((v2_tex_2 @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('103', plain, ((v4_pre_topc @ sk_B_1 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('104', plain, ((v2_tex_2 @ (k2_xboole_0 @ sk_B_1 @ sk_C_1) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.20/0.48  thf('105', plain, ($false), inference('demod', [status(thm)], ['6', '104'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
