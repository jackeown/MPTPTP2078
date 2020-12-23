%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1846+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AcPIFYLGIH

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:24 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 166 expanded)
%              Number of leaves         :   13 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :  358 (2157 expanded)
%              Number of equality atoms :   12 (  86 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_tex_2_type,type,(
    v1_tex_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t13_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( C
                  = ( u1_struct_0 @ B ) )
               => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_pre_topc @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( C
                    = ( u1_struct_0 @ B ) )
                 => ( ( v1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                  <=> ( v1_tex_2 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_tex_2])).

thf('0',plain,
    ( ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_tex_2 @ sk_B @ sk_A )
   <= ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( v1_tex_2 @ sk_B @ sk_A )
    | ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( v1_tex_2 @ sk_B @ sk_A )
   <= ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_tex_2 @ X0 @ X1 )
      | ( X2
       != ( u1_struct_0 @ X0 ) )
      | ( v1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X1 )
      | ~ ( m1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( v1_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_tex_2 @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_tex_2 @ sk_B @ X0 )
      | ( v1_subset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ sk_B @ X0 )
      | ~ ( v1_tex_2 @ sk_B @ X0 )
      | ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf('17',plain,
    ( ~ ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','18'])).

thf('20',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf('21',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( ( sk_C @ X0 @ X1 )
        = ( u1_struct_0 @ X0 ) )
      | ( v1_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('23',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( sk_C_1
    = ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_tex_2 @ sk_B @ sk_A )
    | ( ( sk_C @ sk_B @ sk_A )
      = sk_C_1 ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( v1_tex_2 @ sk_B @ sk_A )
   <= ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = sk_C_1 )
   <= ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','18'])).

thf('30',plain,
    ( ( sk_C @ sk_B @ sk_A )
    = sk_C_1 ),
    inference(simpl_trail,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( v1_subset_1 @ ( sk_C @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v1_tex_2 @ X0 @ X1 )
      | ~ ( l1_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tex_2])).

thf('32',plain,
    ( ~ ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v1_tex_2 @ sk_B @ sk_A )
    | ~ ( m1_pre_topc @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('34',plain,
    ( ( v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_tex_2 @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('35',plain,(
    v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','18','34'])).

thf('36',plain,(
    v1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_pre_topc @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_tex_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['32','36','37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['20','39'])).


%------------------------------------------------------------------------------
