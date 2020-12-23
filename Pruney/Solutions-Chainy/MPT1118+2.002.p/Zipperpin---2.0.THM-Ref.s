%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pHvgNLu4HC

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:18 EST 2020

% Result     : Theorem 20.61s
% Output     : Refutation 20.61s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 199 expanded)
%              Number of leaves         :   18 (  66 expanded)
%              Depth                    :   23
%              Number of atoms          : 1281 (2848 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r1_tarski @ X9 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ sk_C_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_C_1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( sk_D @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( v4_pre_topc @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( v4_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ X1 )
      | ~ ( r1_tarski @ sk_B @ X1 )
      | ~ ( v4_pre_topc @ X1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( v4_pre_topc @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ~ ( r1_tarski @ sk_B @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) )
      | ( r2_hidden @ X1 @ ( sk_D @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( sk_D @ ( sk_C @ X1 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ sk_C_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r2_hidden @ X11 @ ( sk_D @ X11 @ X9 @ X10 ) )
      | ( r2_hidden @ X11 @ ( k2_pre_topc @ X10 @ X9 ) )
      | ~ ( r2_hidden @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_pre_topc @ X10 ) ) ),
    inference(cnf,[status(esa)],[t45_pre_topc])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ ( sk_D @ X0 @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','10'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k2_pre_topc @ sk_A @ sk_B ) ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('68',plain,
    ( ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    r1_tarski @ ( k2_pre_topc @ sk_A @ sk_B ) @ ( k2_pre_topc @ sk_A @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pHvgNLu4HC
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:33:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 20.61/20.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 20.61/20.79  % Solved by: fo/fo7.sh
% 20.61/20.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.61/20.79  % done 11823 iterations in 20.339s
% 20.61/20.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 20.61/20.79  % SZS output start Refutation
% 20.61/20.79  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 20.61/20.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 20.61/20.79  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 20.61/20.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 20.61/20.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.61/20.79  thf(sk_A_type, type, sk_A: $i).
% 20.61/20.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 20.61/20.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.61/20.79  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 20.61/20.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 20.61/20.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.61/20.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.61/20.79  thf(sk_B_type, type, sk_B: $i).
% 20.61/20.79  thf(t49_pre_topc, conjecture,
% 20.61/20.79    (![A:$i]:
% 20.61/20.79     ( ( l1_pre_topc @ A ) =>
% 20.61/20.79       ( ![B:$i]:
% 20.61/20.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.61/20.79           ( ![C:$i]:
% 20.61/20.79             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.61/20.79               ( ( r1_tarski @ B @ C ) =>
% 20.61/20.79                 ( r1_tarski @
% 20.61/20.79                   ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ))).
% 20.61/20.79  thf(zf_stmt_0, negated_conjecture,
% 20.61/20.79    (~( ![A:$i]:
% 20.61/20.79        ( ( l1_pre_topc @ A ) =>
% 20.61/20.79          ( ![B:$i]:
% 20.61/20.79            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.61/20.79              ( ![C:$i]:
% 20.61/20.79                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.61/20.79                  ( ( r1_tarski @ B @ C ) =>
% 20.61/20.79                    ( r1_tarski @
% 20.61/20.79                      ( k2_pre_topc @ A @ B ) @ ( k2_pre_topc @ A @ C ) ) ) ) ) ) ) ) )),
% 20.61/20.79    inference('cnf.neg', [status(esa)], [t49_pre_topc])).
% 20.61/20.79  thf('0', plain,
% 20.61/20.79      (~ (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 20.61/20.79          (k2_pre_topc @ sk_A @ sk_C_1))),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf(d3_tarski, axiom,
% 20.61/20.79    (![A:$i,B:$i]:
% 20.61/20.79     ( ( r1_tarski @ A @ B ) <=>
% 20.61/20.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 20.61/20.79  thf('1', plain,
% 20.61/20.79      (![X1 : $i, X3 : $i]:
% 20.61/20.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 20.61/20.79      inference('cnf', [status(esa)], [d3_tarski])).
% 20.61/20.79  thf('2', plain,
% 20.61/20.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf(dt_k2_pre_topc, axiom,
% 20.61/20.79    (![A:$i,B:$i]:
% 20.61/20.79     ( ( ( l1_pre_topc @ A ) & 
% 20.61/20.79         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 20.61/20.79       ( m1_subset_1 @
% 20.61/20.79         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 20.61/20.79  thf('3', plain,
% 20.61/20.79      (![X7 : $i, X8 : $i]:
% 20.61/20.79         (~ (l1_pre_topc @ X7)
% 20.61/20.79          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 20.61/20.79          | (m1_subset_1 @ (k2_pre_topc @ X7 @ X8) @ 
% 20.61/20.79             (k1_zfmisc_1 @ (u1_struct_0 @ X7))))),
% 20.61/20.79      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 20.61/20.79  thf('4', plain,
% 20.61/20.79      (((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 20.61/20.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.61/20.79        | ~ (l1_pre_topc @ sk_A))),
% 20.61/20.79      inference('sup-', [status(thm)], ['2', '3'])).
% 20.61/20.79  thf('5', plain, ((l1_pre_topc @ sk_A)),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('6', plain,
% 20.61/20.79      ((m1_subset_1 @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 20.61/20.79        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('demod', [status(thm)], ['4', '5'])).
% 20.61/20.79  thf(t3_subset, axiom,
% 20.61/20.79    (![A:$i,B:$i]:
% 20.61/20.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 20.61/20.79  thf('7', plain,
% 20.61/20.79      (![X4 : $i, X5 : $i]:
% 20.61/20.79         ((r1_tarski @ X4 @ X5) | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5)))),
% 20.61/20.79      inference('cnf', [status(esa)], [t3_subset])).
% 20.61/20.79  thf('8', plain,
% 20.61/20.79      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (u1_struct_0 @ sk_A))),
% 20.61/20.79      inference('sup-', [status(thm)], ['6', '7'])).
% 20.61/20.79  thf('9', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X0 @ X1)
% 20.61/20.79          | (r2_hidden @ X0 @ X2)
% 20.61/20.79          | ~ (r1_tarski @ X1 @ X2))),
% 20.61/20.79      inference('cnf', [status(esa)], [d3_tarski])).
% 20.61/20.79  thf('10', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['8', '9'])).
% 20.61/20.79  thf('11', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['1', '10'])).
% 20.61/20.79  thf('12', plain,
% 20.61/20.79      (![X1 : $i, X3 : $i]:
% 20.61/20.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 20.61/20.79      inference('cnf', [status(esa)], [d3_tarski])).
% 20.61/20.79  thf('13', plain,
% 20.61/20.79      (![X1 : $i, X3 : $i]:
% 20.61/20.79         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 20.61/20.79      inference('cnf', [status(esa)], [d3_tarski])).
% 20.61/20.79  thf('14', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('15', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X0 @ X1)
% 20.61/20.79          | (r2_hidden @ X0 @ X2)
% 20.61/20.79          | ~ (r1_tarski @ X1 @ X2))),
% 20.61/20.79      inference('cnf', [status(esa)], [d3_tarski])).
% 20.61/20.79  thf('16', plain,
% 20.61/20.79      (![X0 : $i]: ((r2_hidden @ X0 @ sk_C_1) | ~ (r2_hidden @ X0 @ sk_B))),
% 20.61/20.79      inference('sup-', [status(thm)], ['14', '15'])).
% 20.61/20.79  thf('17', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_C_1))),
% 20.61/20.79      inference('sup-', [status(thm)], ['13', '16'])).
% 20.61/20.79  thf('18', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['1', '10'])).
% 20.61/20.79  thf('19', plain,
% 20.61/20.79      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf(t45_pre_topc, axiom,
% 20.61/20.79    (![A:$i]:
% 20.61/20.79     ( ( l1_pre_topc @ A ) =>
% 20.61/20.79       ( ![B:$i]:
% 20.61/20.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.61/20.79           ( ![C:$i]:
% 20.61/20.79             ( ( r2_hidden @ C @ ( u1_struct_0 @ A ) ) =>
% 20.61/20.79               ( ( r2_hidden @ C @ ( k2_pre_topc @ A @ B ) ) <=>
% 20.61/20.79                 ( ![D:$i]:
% 20.61/20.79                   ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 20.61/20.79                     ( ( ( v4_pre_topc @ D @ A ) & ( r1_tarski @ B @ D ) ) =>
% 20.61/20.79                       ( r2_hidden @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 20.61/20.79  thf('20', plain,
% 20.61/20.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.61/20.79         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 20.61/20.79          | (r1_tarski @ X9 @ (sk_D @ X11 @ X9 @ X10))
% 20.61/20.79          | (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 20.61/20.79          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 20.61/20.79          | ~ (l1_pre_topc @ X10))),
% 20.61/20.79      inference('cnf', [status(esa)], [t45_pre_topc])).
% 20.61/20.79  thf('21', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         (~ (l1_pre_topc @ sk_A)
% 20.61/20.79          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ sk_C_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['19', '20'])).
% 20.61/20.79  thf('22', plain, ((l1_pre_topc @ sk_A)),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('23', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ sk_C_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A)))),
% 20.61/20.79      inference('demod', [status(thm)], ['21', '22'])).
% 20.61/20.79  thf('24', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r1_tarski @ sk_C_1 @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['18', '23'])).
% 20.61/20.79  thf('25', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X0 @ X1)
% 20.61/20.79          | (r2_hidden @ X0 @ X2)
% 20.61/20.79          | ~ (r1_tarski @ X1 @ X2))),
% 20.61/20.79      inference('cnf', [status(esa)], [d3_tarski])).
% 20.61/20.79  thf('26', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79           (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ X1 @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | ~ (r2_hidden @ X1 @ sk_C_1))),
% 20.61/20.79      inference('sup-', [status(thm)], ['24', '25'])).
% 20.61/20.79  thf('27', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         ((r1_tarski @ sk_B @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ sk_B) @ 
% 20.61/20.79             (sk_D @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X1)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['17', '26'])).
% 20.61/20.79  thf('28', plain,
% 20.61/20.79      (![X1 : $i, X3 : $i]:
% 20.61/20.79         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 20.61/20.79      inference('cnf', [status(esa)], [d3_tarski])).
% 20.61/20.79  thf('29', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79           (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r1_tarski @ sk_B @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | (r1_tarski @ sk_B @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['27', '28'])).
% 20.61/20.79  thf('30', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ sk_B @ 
% 20.61/20.79           (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.79      inference('simplify', [status(thm)], ['29'])).
% 20.61/20.79  thf('31', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['1', '10'])).
% 20.61/20.79  thf('32', plain,
% 20.61/20.79      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('33', plain,
% 20.61/20.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.61/20.79         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 20.61/20.79          | (v4_pre_topc @ (sk_D @ X11 @ X9 @ X10) @ X10)
% 20.61/20.79          | (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 20.61/20.79          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 20.61/20.79          | ~ (l1_pre_topc @ X10))),
% 20.61/20.79      inference('cnf', [status(esa)], [t45_pre_topc])).
% 20.61/20.79  thf('34', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         (~ (l1_pre_topc @ sk_A)
% 20.61/20.79          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (v4_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 20.61/20.79      inference('sup-', [status(thm)], ['32', '33'])).
% 20.61/20.79  thf('35', plain, ((l1_pre_topc @ sk_A)),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('36', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (v4_pre_topc @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ sk_A))),
% 20.61/20.79      inference('demod', [status(thm)], ['34', '35'])).
% 20.61/20.79  thf('37', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (v4_pre_topc @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A) @ 
% 20.61/20.79             sk_A)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['31', '36'])).
% 20.61/20.79  thf('38', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['1', '10'])).
% 20.61/20.79  thf('39', plain,
% 20.61/20.79      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('40', plain,
% 20.61/20.79      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.61/20.79         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 20.61/20.79          | (m1_subset_1 @ (sk_D @ X11 @ X9 @ X10) @ 
% 20.61/20.79             (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 20.61/20.79          | (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 20.61/20.79          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 20.61/20.79          | ~ (l1_pre_topc @ X10))),
% 20.61/20.79      inference('cnf', [status(esa)], [t45_pre_topc])).
% 20.61/20.79  thf('41', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         (~ (l1_pre_topc @ sk_A)
% 20.61/20.79          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 20.61/20.79             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 20.61/20.79      inference('sup-', [status(thm)], ['39', '40'])).
% 20.61/20.79  thf('42', plain, ((l1_pre_topc @ sk_A)),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('43', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (m1_subset_1 @ (sk_D @ X0 @ sk_C_1 @ sk_A) @ 
% 20.61/20.79             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 20.61/20.79      inference('demod', [status(thm)], ['41', '42'])).
% 20.61/20.79  thf('44', plain,
% 20.61/20.79      (![X0 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (m1_subset_1 @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A) @ 
% 20.61/20.79             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['38', '43'])).
% 20.61/20.79  thf('45', plain,
% 20.61/20.79      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('46', plain,
% 20.61/20.79      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 20.61/20.79         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 20.61/20.79          | ~ (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 20.61/20.79          | ~ (v4_pre_topc @ X12 @ X10)
% 20.61/20.79          | ~ (r1_tarski @ X9 @ X12)
% 20.61/20.79          | (r2_hidden @ X11 @ X12)
% 20.61/20.79          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 20.61/20.79          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 20.61/20.79          | ~ (l1_pre_topc @ X10))),
% 20.61/20.79      inference('cnf', [status(esa)], [t45_pre_topc])).
% 20.61/20.79  thf('47', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         (~ (l1_pre_topc @ sk_A)
% 20.61/20.79          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.61/20.79          | (r2_hidden @ X0 @ X1)
% 20.61/20.79          | ~ (r1_tarski @ sk_B @ X1)
% 20.61/20.79          | ~ (v4_pre_topc @ X1 @ sk_A)
% 20.61/20.79          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['45', '46'])).
% 20.61/20.79  thf('48', plain, ((l1_pre_topc @ sk_A)),
% 20.61/20.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.79  thf('49', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 20.61/20.79          | (r2_hidden @ X0 @ X1)
% 20.61/20.79          | ~ (r1_tarski @ sk_B @ X1)
% 20.61/20.79          | ~ (v4_pre_topc @ X1 @ sk_A)
% 20.61/20.79          | ~ (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 20.61/20.79      inference('demod', [status(thm)], ['47', '48'])).
% 20.61/20.79  thf('50', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79           (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 20.61/20.79          | ~ (v4_pre_topc @ 
% 20.61/20.79               (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ 
% 20.61/20.79                sk_A) @ 
% 20.61/20.79               sk_A)
% 20.61/20.79          | ~ (r1_tarski @ sk_B @ 
% 20.61/20.79               (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ 
% 20.61/20.79                sk_A))
% 20.61/20.79          | (r2_hidden @ X1 @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['44', '49'])).
% 20.61/20.79  thf('51', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79           (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ X1 @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | ~ (r1_tarski @ sk_B @ 
% 20.61/20.79               (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ 
% 20.61/20.79                sk_A))
% 20.61/20.79          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['37', '50'])).
% 20.61/20.79  thf('52', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 20.61/20.79          | ~ (r1_tarski @ sk_B @ 
% 20.61/20.79               (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ 
% 20.61/20.79                sk_A))
% 20.61/20.79          | (r2_hidden @ X1 @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.79      inference('simplify', [status(thm)], ['51'])).
% 20.61/20.79  thf('53', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         ((r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79           (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ X1 @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['30', '52'])).
% 20.61/20.79  thf('54', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         (~ (r2_hidden @ X1 @ (k2_pre_topc @ sk_A @ sk_B))
% 20.61/20.79          | (r2_hidden @ X1 @ 
% 20.61/20.79             (sk_D @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.79      inference('simplify', [status(thm)], ['53'])).
% 20.61/20.79  thf('55', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X1)
% 20.61/20.79          | ~ (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79               (u1_struct_0 @ sk_A))
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (sk_D @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A)))),
% 20.61/20.79      inference('sup-', [status(thm)], ['12', '54'])).
% 20.61/20.79  thf('56', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (sk_D @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X1)
% 20.61/20.79          | (r2_hidden @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.79             (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.79          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 20.61/20.79      inference('sup-', [status(thm)], ['11', '55'])).
% 20.61/20.79  thf('57', plain,
% 20.61/20.79      (![X0 : $i, X1 : $i]:
% 20.61/20.79         ((r2_hidden @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80           (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.80          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X1)
% 20.61/20.80          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80             (sk_D @ (sk_C @ X1 @ (k2_pre_topc @ sk_A @ sk_B)) @ sk_C_1 @ sk_A))
% 20.61/20.80          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 20.61/20.80      inference('simplify', [status(thm)], ['56'])).
% 20.61/20.80  thf('58', plain,
% 20.61/20.80      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 20.61/20.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.80  thf('59', plain,
% 20.61/20.80      (![X9 : $i, X10 : $i, X11 : $i]:
% 20.61/20.80         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 20.61/20.80          | ~ (r2_hidden @ X11 @ (sk_D @ X11 @ X9 @ X10))
% 20.61/20.80          | (r2_hidden @ X11 @ (k2_pre_topc @ X10 @ X9))
% 20.61/20.80          | ~ (r2_hidden @ X11 @ (u1_struct_0 @ X10))
% 20.61/20.80          | ~ (l1_pre_topc @ X10))),
% 20.61/20.80      inference('cnf', [status(esa)], [t45_pre_topc])).
% 20.61/20.80  thf('60', plain,
% 20.61/20.80      (![X0 : $i]:
% 20.61/20.80         (~ (l1_pre_topc @ sk_A)
% 20.61/20.80          | ~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.80          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.80          | ~ (r2_hidden @ X0 @ (sk_D @ X0 @ sk_C_1 @ sk_A)))),
% 20.61/20.80      inference('sup-', [status(thm)], ['58', '59'])).
% 20.61/20.80  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 20.61/20.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.61/20.80  thf('62', plain,
% 20.61/20.80      (![X0 : $i]:
% 20.61/20.80         (~ (r2_hidden @ X0 @ (u1_struct_0 @ sk_A))
% 20.61/20.80          | (r2_hidden @ X0 @ (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.80          | ~ (r2_hidden @ X0 @ (sk_D @ X0 @ sk_C_1 @ sk_A)))),
% 20.61/20.80      inference('demod', [status(thm)], ['60', '61'])).
% 20.61/20.80  thf('63', plain,
% 20.61/20.80      (![X0 : $i]:
% 20.61/20.80         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.80          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.80          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80             (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.80          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80             (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.80          | ~ (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80               (u1_struct_0 @ sk_A)))),
% 20.61/20.80      inference('sup-', [status(thm)], ['57', '62'])).
% 20.61/20.80  thf('64', plain,
% 20.61/20.80      (![X0 : $i]:
% 20.61/20.80         (~ (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80             (u1_struct_0 @ sk_A))
% 20.61/20.80          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80             (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.80          | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0))),
% 20.61/20.80      inference('simplify', [status(thm)], ['63'])).
% 20.61/20.80  thf('65', plain,
% 20.61/20.80      (![X0 : $i]:
% 20.61/20.80         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.80          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80             (u1_struct_0 @ sk_A)))),
% 20.61/20.80      inference('sup-', [status(thm)], ['1', '10'])).
% 20.61/20.80  thf('66', plain,
% 20.61/20.80      (![X0 : $i]:
% 20.61/20.80         ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ X0)
% 20.61/20.80          | (r2_hidden @ (sk_C @ X0 @ (k2_pre_topc @ sk_A @ sk_B)) @ 
% 20.61/20.80             (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.80      inference('clc', [status(thm)], ['64', '65'])).
% 20.61/20.80  thf('67', plain,
% 20.61/20.80      (![X1 : $i, X3 : $i]:
% 20.61/20.80         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 20.61/20.80      inference('cnf', [status(esa)], [d3_tarski])).
% 20.61/20.80  thf('68', plain,
% 20.61/20.80      (((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 20.61/20.80         (k2_pre_topc @ sk_A @ sk_C_1))
% 20.61/20.80        | (r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ 
% 20.61/20.80           (k2_pre_topc @ sk_A @ sk_C_1)))),
% 20.61/20.80      inference('sup-', [status(thm)], ['66', '67'])).
% 20.61/20.80  thf('69', plain,
% 20.61/20.80      ((r1_tarski @ (k2_pre_topc @ sk_A @ sk_B) @ (k2_pre_topc @ sk_A @ sk_C_1))),
% 20.61/20.80      inference('simplify', [status(thm)], ['68'])).
% 20.61/20.80  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 20.61/20.80  
% 20.61/20.80  % SZS output end Refutation
% 20.61/20.80  
% 20.61/20.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
