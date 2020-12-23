%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mrYkbVC55v

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:18 EST 2020

% Result     : Theorem 5.73s
% Output     : Refutation 5.73s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 184 expanded)
%              Number of leaves         :   18 (  61 expanded)
%              Depth                    :   22
%              Number of atoms          : 1272 (2758 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(t49_pre_topc,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( r1_tarski @ B @ C )
                 => ( r1_tarski @ ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_pre_topc])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X7 @ X8 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('4',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t45_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                   => ( ( ( v4_pre_topc @ D @ A )
                        & ( r1_tarski @ B @ D ) )
                     => ( r2_hidden @ C @ D ) ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ X9 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_C_1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v4_pre_topc @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v4_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( v4_pre_topc @ X12 @ X10 )
      | ~ ( r1_tarski @ X9 @ X12 )
      | ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['0','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mrYkbVC55v
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:42:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 5.73/5.91  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.73/5.91  % Solved by: fo/fo7.sh
% 5.73/5.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.73/5.91  % done 2888 iterations in 5.447s
% 5.73/5.91  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.73/5.91  % SZS output start Refutation
% 5.73/5.91  thf(sk_A_type, type, sk_A: $i).
% 5.73/5.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.73/5.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.73/5.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.73/5.91  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 5.73/5.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.73/5.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.73/5.91  thf(sk_B_type, type, sk_B: $i).
% 5.73/5.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.73/5.91  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 5.73/5.91  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.73/5.91  thf(sk_C_1_type, type, sk_C_1: $i).
% 5.73/5.91  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 5.73/5.91  thf(t49_pre_topc, conjecture,
% 5.73/5.91    (![A:$i]:
% 5.73/5.91     ( ( l1_pre_topc @ A ) =>
% 5.73/5.91       ( ![B:$i]:
% 5.73/5.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.73/5.91           ( ![C:$i]:
% 5.73/5.91             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.73/5.91               ( ( r1_tarski @ B @ C ) =>
% 5.73/5.91                 ( r1_tarski @
% 5.73/5.91                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 5.73/5.91  thf(zf_stmt_0, negated_conjecture,
% 5.73/5.91    (~( ![A:$i]:
% 5.73/5.91        ( ( l1_pre_topc @ A ) =>
% 5.73/5.91          ( ![B:$i]:
% 5.73/5.91            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.73/5.91              ( ![C:$i]:
% 5.73/5.91                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.73/5.91                  ( ( r1_tarski @ B @ C ) =>
% 5.73/5.91                    ( r1_tarski @
% 5.73/5.91                      ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 5.73/5.91    inference('cnf.neg', [status(esa)], [t49_pre_topc])).
% 5.73/5.91  thf('0', plain,
% 5.73/5.91      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.73/5.91          (k2_pre_topc @ sk_A @ sk_C_1))),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf(d3_tarski, axiom,
% 5.73/5.91    (![A:$i,B:$i]:
% 5.73/5.91     ( ( r1_tarski @ A @ B ) <=>
% 5.73/5.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.73/5.91  thf('1', plain,
% 5.73/5.91      (![X1 : $i, X3 : $i]:
% 5.73/5.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.73/5.91      inference('cnf', [status(esa)], [d3_tarski])).
% 5.73/5.91  thf('2', plain,
% 5.73/5.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf(dt_k2_pre_topc, axiom,
% 5.73/5.91    (![A:$i,B:$i]:
% 5.73/5.91     ( ( ( l1_pre_topc @ A ) & 
% 5.73/5.91         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 5.73/5.91       ( m1_subset_1 @
% 5.73/5.91         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.73/5.91  thf('3', plain,
% 5.73/5.91      (![X7 : $i, X8 : $i]:
% 5.73/5.91         (~ (l1_pre_topc @ X7)
% 5.73/5.91          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 5.73/5.91          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 5.73/5.91             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 5.73/5.91      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 5.73/5.91  thf('4', plain,
% 5.73/5.91      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.73/5.91         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.73/5.91        | ~ (l1_pre_topc @ sk_A))),
% 5.73/5.91      inference('sup-', [status(thm)], ['2', '3'])).
% 5.73/5.91  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('6', plain,
% 5.73/5.91      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.73/5.91        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('demod', [status(thm)], ['4', '5'])).
% 5.73/5.91  thf(l3_subset_1, axiom,
% 5.73/5.91    (![A:$i,B:$i]:
% 5.73/5.91     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 5.73/5.91       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 5.73/5.91  thf('7', plain,
% 5.73/5.91      (![X4 : $i, X5 : $i, X6 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X4 @ X5)
% 5.73/5.91          | (r2_hidden @ X4 @ X6)
% 5.73/5.91          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 5.73/5.91      inference('cnf', [status(esa)], [l3_subset_1])).
% 5.73/5.91  thf('8', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['6', '7'])).
% 5.73/5.91  thf('9', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['1', '8'])).
% 5.73/5.91  thf('10', plain,
% 5.73/5.91      (![X1 : $i, X3 : $i]:
% 5.73/5.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.73/5.91      inference('cnf', [status(esa)], [d3_tarski])).
% 5.73/5.91  thf('11', plain,
% 5.73/5.91      (![X1 : $i, X3 : $i]:
% 5.73/5.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.73/5.91      inference('cnf', [status(esa)], [d3_tarski])).
% 5.73/5.91  thf('12', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('13', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X0 @ X1)
% 5.73/5.91          | (r2_hidden @ X0 @ X2)
% 5.73/5.91          | ~ (r1_tarski @ X1 @ X2))),
% 5.73/5.91      inference('cnf', [status(esa)], [d3_tarski])).
% 5.73/5.91  thf('14', plain,
% 5.73/5.91      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 5.73/5.91      inference('sup-', [status(thm)], ['12', '13'])).
% 5.73/5.91  thf('15', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1))),
% 5.73/5.91      inference('sup-', [status(thm)], ['11', '14'])).
% 5.73/5.91  thf('16', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['1', '8'])).
% 5.73/5.91  thf('17', plain,
% 5.73/5.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf(t45_pre_topc, axiom,
% 5.73/5.91    (![A:$i]:
% 5.73/5.91     ( ( l1_pre_topc @ A ) =>
% 5.73/5.91       ( ![B:$i]:
% 5.73/5.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.73/5.91           ( ![C:$i]:
% 5.73/5.91             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 5.73/5.91               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 5.73/5.91                 ( ![D:$i]:
% 5.73/5.91                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.73/5.91                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 5.73/5.91                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 5.73/5.91  thf('18', plain,
% 5.73/5.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.73/5.91         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.73/5.91          | (r1_tarski @ X9 @ (sk_D @ X11 @ X9 @ X10))
% 5.73/5.91          | (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 5.73/5.91          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 5.73/5.91          | ~ (l1_pre_topc @ X10))),
% 5.73/5.91      inference('cnf', [status(esa)], [t45_pre_topc])).
% 5.73/5.91  thf('19', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (l1_pre_topc @ sk_A)
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ sk_C_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['17', '18'])).
% 5.73/5.91  thf('20', plain, ((l1_pre_topc @ sk_A)),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('21', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ sk_C_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A)))),
% 5.73/5.91      inference('demod', [status(thm)], ['19', '20'])).
% 5.73/5.91  thf('22', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r1_tarski @ sk_C_1 @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['16', '21'])).
% 5.73/5.91  thf('23', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X0 @ X1)
% 5.73/5.91          | (r2_hidden @ X0 @ X2)
% 5.73/5.91          | ~ (r1_tarski @ X1 @ X2))),
% 5.73/5.91      inference('cnf', [status(esa)], [d3_tarski])).
% 5.73/5.91  thf('24', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91           (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ X1 @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | ~ (r2_hidden @ X1 @ sk_C_1))),
% 5.73/5.91      inference('sup-', [status(thm)], ['22', '23'])).
% 5.73/5.91  thf('25', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         ((r1_tarski @ sk_B @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 5.73/5.91             (sk_D @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X1)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['15', '24'])).
% 5.73/5.91  thf('26', plain,
% 5.73/5.91      (![X1 : $i, X3 : $i]:
% 5.73/5.91         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.73/5.91      inference('cnf', [status(esa)], [d3_tarski])).
% 5.73/5.91  thf('27', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91           (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r1_tarski @ sk_B @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | (r1_tarski @ sk_B @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['25', '26'])).
% 5.73/5.91  thf('28', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ sk_B @ 
% 5.73/5.91           (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('simplify', [status(thm)], ['27'])).
% 5.73/5.91  thf('29', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['1', '8'])).
% 5.73/5.91  thf('30', plain,
% 5.73/5.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('31', plain,
% 5.73/5.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.73/5.91         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.73/5.91          | (v4_pre_topc @ (sk_D @ X11 @ X9 @ X10) @ X10)
% 5.73/5.91          | (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 5.73/5.91          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 5.73/5.91          | ~ (l1_pre_topc @ X10))),
% 5.73/5.91      inference('cnf', [status(esa)], [t45_pre_topc])).
% 5.73/5.91  thf('32', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (l1_pre_topc @ sk_A)
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (v4_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 5.73/5.91      inference('sup-', [status(thm)], ['30', '31'])).
% 5.73/5.91  thf('33', plain, ((l1_pre_topc @ sk_A)),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('34', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (v4_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 5.73/5.91      inference('demod', [status(thm)], ['32', '33'])).
% 5.73/5.91  thf('35', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (v4_pre_topc @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A) @ 
% 5.73/5.91             sk_A)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['29', '34'])).
% 5.73/5.91  thf('36', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['1', '8'])).
% 5.73/5.91  thf('37', plain,
% 5.73/5.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('38', plain,
% 5.73/5.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.73/5.91         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.73/5.91          | (m1_subset_1 @ (sk_D @ X11 @ X9 @ X10) @ 
% 5.73/5.91             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.73/5.91          | (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 5.73/5.91          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 5.73/5.91          | ~ (l1_pre_topc @ X10))),
% 5.73/5.91      inference('cnf', [status(esa)], [t45_pre_topc])).
% 5.73/5.91  thf('39', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (l1_pre_topc @ sk_A)
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 5.73/5.91             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.73/5.91      inference('sup-', [status(thm)], ['37', '38'])).
% 5.73/5.91  thf('40', plain, ((l1_pre_topc @ sk_A)),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('41', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 5.73/5.91             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 5.73/5.91      inference('demod', [status(thm)], ['39', '40'])).
% 5.73/5.91  thf('42', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (m1_subset_1 @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A) @ 
% 5.73/5.91             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['36', '41'])).
% 5.73/5.91  thf('43', plain,
% 5.73/5.91      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('44', plain,
% 5.73/5.91      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 5.73/5.91         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.73/5.91          | ~ (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 5.73/5.91          | ~ (v4_pre_topc @ X12 @ X10)
% 5.73/5.91          | ~ (r1_tarski @ X9 @ X12)
% 5.73/5.91          | (r2_hidden @ X11 @ X12)
% 5.73/5.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.73/5.91          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 5.73/5.91          | ~ (l1_pre_topc @ X10))),
% 5.73/5.91      inference('cnf', [status(esa)], [t45_pre_topc])).
% 5.73/5.91  thf('45', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         (~ (l1_pre_topc @ sk_A)
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.73/5.91          | (r2_hidden @ X0 @ X1)
% 5.73/5.91          | ~ (r1_tarski @ sk_B @ X1)
% 5.73/5.91          | ~ (v4_pre_topc @ X1 @ sk_A)
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['43', '44'])).
% 5.73/5.91  thf('46', plain, ((l1_pre_topc @ sk_A)),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('47', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 5.73/5.91          | (r2_hidden @ X0 @ X1)
% 5.73/5.91          | ~ (r1_tarski @ sk_B @ X1)
% 5.73/5.91          | ~ (v4_pre_topc @ X1 @ sk_A)
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 5.73/5.91      inference('demod', [status(thm)], ['45', '46'])).
% 5.73/5.91  thf('48', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91           (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 5.73/5.91          | ~ (v4_pre_topc @ 
% 5.73/5.91               (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ 
% 5.73/5.91                sk_A) @ 
% 5.73/5.91               sk_A)
% 5.73/5.91          | ~ (r1_tarski @ sk_B @ 
% 5.73/5.91               (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ 
% 5.73/5.91                sk_A))
% 5.73/5.91          | (r2_hidden @ X1 @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['42', '47'])).
% 5.73/5.91  thf('49', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91           (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X1 @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | ~ (r1_tarski @ sk_B @ 
% 5.73/5.91               (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ 
% 5.73/5.91                sk_A))
% 5.73/5.91          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['35', '48'])).
% 5.73/5.91  thf('50', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 5.73/5.91          | ~ (r1_tarski @ sk_B @ 
% 5.73/5.91               (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ 
% 5.73/5.91                sk_A))
% 5.73/5.91          | (r2_hidden @ X1 @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('simplify', [status(thm)], ['49'])).
% 5.73/5.91  thf('51', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91           (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X1 @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['28', '50'])).
% 5.73/5.91  thf('52', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 5.73/5.91          | (r2_hidden @ X1 @ 
% 5.73/5.91             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('simplify', [status(thm)], ['51'])).
% 5.73/5.91  thf('53', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X1)
% 5.73/5.91          | ~ (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91               (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (sk_D @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['10', '52'])).
% 5.73/5.91  thf('54', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (sk_D @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X1)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 5.73/5.91      inference('sup-', [status(thm)], ['9', '53'])).
% 5.73/5.91  thf('55', plain,
% 5.73/5.91      (![X0 : $i, X1 : $i]:
% 5.73/5.91         ((r2_hidden @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91           (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X1)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (sk_D @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 5.73/5.91      inference('simplify', [status(thm)], ['54'])).
% 5.73/5.91  thf('56', plain,
% 5.73/5.91      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('57', plain,
% 5.73/5.91      (![X9 : $i, X10 : $i, X11 : $i]:
% 5.73/5.91         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 5.73/5.91          | ~ (r2_hidden @ X11 @ (sk_D @ X11 @ X9 @ X10))
% 5.73/5.91          | (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 5.73/5.91          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 5.73/5.91          | ~ (l1_pre_topc @ X10))),
% 5.73/5.91      inference('cnf', [status(esa)], [t45_pre_topc])).
% 5.73/5.91  thf('58', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (l1_pre_topc @ sk_A)
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (sk_D @ X0 @ sk_C_1 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['56', '57'])).
% 5.73/5.91  thf('59', plain, ((l1_pre_topc @ sk_A)),
% 5.73/5.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.73/5.91  thf('60', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | ~ (r2_hidden @ X0 @ (sk_D @ X0 @ sk_C_1 @ sk_A)))),
% 5.73/5.91      inference('demod', [status(thm)], ['58', '59'])).
% 5.73/5.91  thf('61', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | ~ (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91               (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['55', '60'])).
% 5.73/5.91  thf('62', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         (~ (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (u1_struct_0 @ sk_A))
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 5.73/5.91      inference('simplify', [status(thm)], ['61'])).
% 5.73/5.91  thf('63', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (u1_struct_0 @ sk_A)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['1', '8'])).
% 5.73/5.91  thf('64', plain,
% 5.73/5.91      (![X0 : $i]:
% 5.73/5.91         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 5.73/5.91          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 5.73/5.91             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('clc', [status(thm)], ['62', '63'])).
% 5.73/5.91  thf('65', plain,
% 5.73/5.91      (![X1 : $i, X3 : $i]:
% 5.73/5.91         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.73/5.91      inference('cnf', [status(esa)], [d3_tarski])).
% 5.73/5.91  thf('66', plain,
% 5.73/5.91      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.73/5.91         (k2_pre_topc @ sk_A @ sk_C_1))
% 5.73/5.91        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 5.73/5.91           (k2_pre_topc @ sk_A @ sk_C_1)))),
% 5.73/5.91      inference('sup-', [status(thm)], ['64', '65'])).
% 5.73/5.91  thf('67', plain,
% 5.73/5.91      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_C_1))),
% 5.73/5.91      inference('simplify', [status(thm)], ['66'])).
% 5.73/5.91  thf('68', plain, ($false), inference('demod', [status(thm)], ['0', '67'])).
% 5.73/5.91  
% 5.73/5.91  % SZS output end Refutation
% 5.73/5.91  
% 5.73/5.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
