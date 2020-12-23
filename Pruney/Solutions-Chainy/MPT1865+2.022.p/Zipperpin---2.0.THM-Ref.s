%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KXgkqEk3iI

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:12:23 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 287 expanded)
%              Number of leaves         :   23 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :  907 (5576 expanded)
%              Number of equality atoms :   23 ( 162 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_pre_topc_type,type,(
    v3_pre_topc: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_tex_2_type,type,(
    v2_tex_2: $i > $i > $o )).

thf(t33_tex_2,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( v2_tex_2 @ B @ A )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                         => ~ ( ( v4_pre_topc @ D @ A )
                              & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                                = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_tex_2,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tex_2 @ B @ A )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                       => ~ ( ( v3_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = ( k1_tarski @ C ) ) ) ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X13 ) @ X12 @ ( sk_D_1 @ X14 @ X12 @ X13 ) )
        = ( k1_tarski @ X14 ) )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t32_tex_2])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X14 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( v2_tex_2 @ X12 @ X13 )
      | ~ ( l1_pre_topc @ X13 ) ) ),
    inference(cnf,[status(esa)],[t32_tex_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf('18',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(dt_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k9_subset_1 @ X5 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_subset_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_tex_2,axiom,(
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
                       => ~ ( ( v4_pre_topc @ D @ A )
                            & ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D )
                              = C ) ) ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ X9 ) @ X8 @ ( sk_D @ X10 @ X8 @ X9 ) )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
      = ( k1_tarski @ sk_C_1 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    r2_hidden @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_tarski @ sk_C_1 @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['29','36'])).

thf('38',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('40',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( m1_subset_1 @ ( sk_D @ X10 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('49',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X15: $i] :
      ( ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X15 )
       != ( k1_tarski @ sk_C_1 ) )
      | ~ ( v4_pre_topc @ X15 @ sk_A )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A )
    | ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
     != ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('55',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( v2_tex_2 @ X8 @ X9 )
      | ( v4_pre_topc @ ( sk_D @ X10 @ X8 @ X9 ) @ X9 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_pre_topc @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_tex_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A )
      | ~ ( v2_tex_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v2_tex_2 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( v4_pre_topc @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v4_pre_topc @ ( sk_D @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B @ sk_A ) @ sk_A )
      | ~ ( r1_tarski @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['54','60'])).

thf('62',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B )
    | ( v4_pre_topc @ ( sk_D @ ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['53','61'])).

thf('63',plain,(
    r1_tarski @ ( k1_tarski @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['34','35'])).

thf('64',plain,
    ( ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D_1 @ sk_C_1 @ sk_B @ sk_A ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('65',plain,(
    v4_pre_topc @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ( k9_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_B @ sk_A ) )
 != ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['52','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KXgkqEk3iI
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:35:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.61  % Solved by: fo/fo7.sh
% 0.39/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.61  % done 121 iterations in 0.153s
% 0.39/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.61  % SZS output start Refutation
% 0.39/0.61  thf(v3_pre_topc_type, type, v3_pre_topc: $i > $i > $o).
% 0.39/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.61  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.39/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.39/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.61  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.39/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.61  thf(v2_tex_2_type, type, v2_tex_2: $i > $i > $o).
% 0.39/0.61  thf(t33_tex_2, conjecture,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( l1_pre_topc @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61           ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.61             ( ![C:$i]:
% 0.39/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.39/0.61                      ( ![D:$i]:
% 0.39/0.61                        ( ( m1_subset_1 @
% 0.39/0.61                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.39/0.61                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.61                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.61    (~( ![A:$i]:
% 0.39/0.61        ( ( l1_pre_topc @ A ) =>
% 0.39/0.61          ( ![B:$i]:
% 0.39/0.61            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61              ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.61                ( ![C:$i]:
% 0.39/0.61                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61                    ( ~( ( r2_hidden @ C @ B ) & 
% 0.39/0.61                         ( ![D:$i]:
% 0.39/0.61                           ( ( m1_subset_1 @
% 0.39/0.61                               D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61                             ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.39/0.61                                  ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.61                                    ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.61    inference('cnf.neg', [status(esa)], [t33_tex_2])).
% 0.39/0.61  thf('0', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('1', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t32_tex_2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( l1_pre_topc @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61           ( ( v2_tex_2 @ B @ A ) =>
% 0.39/0.61             ( ![C:$i]:
% 0.39/0.61               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.39/0.61                 ( ~( ( r2_hidden @ C @ B ) & 
% 0.39/0.61                      ( ![D:$i]:
% 0.39/0.61                        ( ( m1_subset_1 @
% 0.39/0.61                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61                          ( ~( ( v3_pre_topc @ D @ A ) & 
% 0.39/0.61                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.61                                 ( k1_tarski @ C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf('2', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.61          | ((k9_subset_1 @ (u1_struct_0 @ X13) @ X12 @ 
% 0.39/0.61              (sk_D_1 @ X14 @ X12 @ X13)) = (k1_tarski @ X14))
% 0.39/0.61          | ~ (r2_hidden @ X14 @ X12)
% 0.39/0.61          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.39/0.61          | ~ (v2_tex_2 @ X12 @ X13)
% 0.39/0.61          | ~ (l1_pre_topc @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t32_tex_2])).
% 0.39/0.61  thf('3', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (l1_pre_topc @ sk_A)
% 0.39/0.61          | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.39/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.61          | ~ (r2_hidden @ X0 @ sk_B)
% 0.39/0.61          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (k1_tarski @ X0)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.61  thf('4', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('5', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('6', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.61          | ~ (r2_hidden @ X0 @ sk_B)
% 0.39/0.61          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61              (sk_D_1 @ X0 @ sk_B @ sk_A)) = (k1_tarski @ X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.39/0.61  thf('7', plain,
% 0.39/0.61      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61          (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.39/0.61        | ~ (r2_hidden @ sk_C_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['0', '6'])).
% 0.39/0.61  thf('8', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('9', plain,
% 0.39/0.61      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61         (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.39/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.61  thf('10', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('11', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('12', plain,
% 0.39/0.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.61          | (m1_subset_1 @ (sk_D_1 @ X14 @ X12 @ X13) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.39/0.61          | ~ (r2_hidden @ X14 @ X12)
% 0.39/0.61          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.39/0.61          | ~ (v2_tex_2 @ X12 @ X13)
% 0.39/0.61          | ~ (l1_pre_topc @ X13))),
% 0.39/0.61      inference('cnf', [status(esa)], [t32_tex_2])).
% 0.39/0.61  thf('13', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (l1_pre_topc @ sk_A)
% 0.39/0.61          | ~ (v2_tex_2 @ sk_B @ sk_A)
% 0.39/0.61          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.61          | ~ (r2_hidden @ X0 @ sk_B)
% 0.39/0.61          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.61  thf('14', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('15', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('16', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.39/0.61          | ~ (r2_hidden @ X0 @ sk_B)
% 0.39/0.61          | (m1_subset_1 @ (sk_D_1 @ X0 @ sk_B @ sk_A) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.61      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.39/0.61  thf('17', plain,
% 0.39/0.61      (((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.39/0.61         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.61        | ~ (r2_hidden @ sk_C_1 @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['10', '16'])).
% 0.39/0.61  thf('18', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('19', plain,
% 0.39/0.61      ((m1_subset_1 @ (sk_D_1 @ sk_C_1 @ sk_B @ sk_A) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.39/0.61  thf(dt_k9_subset_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.61       ( m1_subset_1 @ ( k9_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.39/0.61  thf('20', plain,
% 0.39/0.61      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.39/0.61         ((m1_subset_1 @ (k9_subset_1 @ X5 @ X6 @ X7) @ (k1_zfmisc_1 @ X5))
% 0.39/0.61          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X5)))),
% 0.39/0.61      inference('cnf', [status(esa)], [dt_k9_subset_1])).
% 0.39/0.61  thf('21', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (m1_subset_1 @ 
% 0.39/0.61          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.39/0.61           (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.61  thf('22', plain,
% 0.39/0.61      ((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.39/0.61        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('sup+', [status(thm)], ['9', '21'])).
% 0.39/0.61  thf('23', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(d6_tex_2, axiom,
% 0.39/0.61    (![A:$i]:
% 0.39/0.61     ( ( l1_pre_topc @ A ) =>
% 0.39/0.61       ( ![B:$i]:
% 0.39/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61           ( ( v2_tex_2 @ B @ A ) <=>
% 0.39/0.61             ( ![C:$i]:
% 0.39/0.61               ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61                 ( ~( ( r1_tarski @ C @ B ) & 
% 0.39/0.61                      ( ![D:$i]:
% 0.39/0.61                        ( ( m1_subset_1 @
% 0.39/0.61                            D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.39/0.61                          ( ~( ( v4_pre_topc @ D @ A ) & 
% 0.39/0.61                               ( ( k9_subset_1 @ ( u1_struct_0 @ A ) @ B @ D ) =
% 0.39/0.61                                 ( C ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.61  thf('24', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.61          | ~ (v2_tex_2 @ X8 @ X9)
% 0.39/0.61          | ((k9_subset_1 @ (u1_struct_0 @ X9) @ X8 @ (sk_D @ X10 @ X8 @ X9))
% 0.39/0.61              = (X10))
% 0.39/0.61          | ~ (r1_tarski @ X10 @ X8)
% 0.39/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.61          | ~ (l1_pre_topc @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.61  thf('25', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (l1_pre_topc @ sk_A)
% 0.39/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.61          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.61          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61              (sk_D @ X0 @ sk_B @ sk_A)) = (X0))
% 0.39/0.61          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.39/0.61  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('27', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('28', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.61          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.61          | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61              (sk_D @ X0 @ sk_B @ sk_A)) = (X0)))),
% 0.39/0.61      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.39/0.61  thf('29', plain,
% 0.39/0.61      ((((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61          (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))
% 0.39/0.61        | ~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['22', '28'])).
% 0.39/0.61  thf('30', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('31', plain, ((r2_hidden @ sk_C_1 @ sk_B)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf(t38_zfmisc_1, axiom,
% 0.39/0.61    (![A:$i,B:$i,C:$i]:
% 0.39/0.61     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.39/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.39/0.61  thf('32', plain,
% 0.39/0.61      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.39/0.61         ((r1_tarski @ (k2_tarski @ X1 @ X3) @ X4)
% 0.39/0.61          | ~ (r2_hidden @ X3 @ X4)
% 0.39/0.61          | ~ (r2_hidden @ X1 @ X4))),
% 0.39/0.61      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.39/0.61  thf('33', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (r2_hidden @ X0 @ sk_B)
% 0.39/0.61          | (r1_tarski @ (k2_tarski @ X0 @ sk_C_1) @ sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.61  thf('34', plain, ((r1_tarski @ (k2_tarski @ sk_C_1 @ sk_C_1) @ sk_B)),
% 0.39/0.61      inference('sup-', [status(thm)], ['30', '33'])).
% 0.39/0.61  thf(t69_enumset1, axiom,
% 0.39/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.39/0.61  thf('35', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.39/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.39/0.61  thf('36', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.39/0.61      inference('demod', [status(thm)], ['34', '35'])).
% 0.39/0.61  thf('37', plain,
% 0.39/0.61      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.39/0.61      inference('demod', [status(thm)], ['29', '36'])).
% 0.39/0.61  thf('38', plain,
% 0.39/0.61      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.61         (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.39/0.61      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.61  thf('39', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (m1_subset_1 @ 
% 0.39/0.61          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.39/0.61           (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.61          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.61  thf('40', plain,
% 0.39/0.61      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('41', plain,
% 0.39/0.61      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.61          | ~ (v2_tex_2 @ X8 @ X9)
% 0.39/0.61          | (m1_subset_1 @ (sk_D @ X10 @ X8 @ X9) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.61          | ~ (r1_tarski @ X10 @ X8)
% 0.39/0.61          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.61          | ~ (l1_pre_topc @ X9))),
% 0.39/0.61      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.61  thf('42', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (l1_pre_topc @ sk_A)
% 0.39/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.61          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.61          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.61          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.61      inference('sup-', [status(thm)], ['40', '41'])).
% 0.39/0.61  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('44', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.61  thf('45', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.61          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.61          | (m1_subset_1 @ (sk_D @ X0 @ sk_B @ sk_A) @ 
% 0.39/0.61             (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.61      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.39/0.61  thf('46', plain,
% 0.39/0.61      (![X0 : $i]:
% 0.39/0.61         ((m1_subset_1 @ 
% 0.39/0.61           (sk_D @ 
% 0.39/0.61            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.39/0.61             (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.61            sk_B @ sk_A) @ 
% 0.39/0.61           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.61          | ~ (r1_tarski @ 
% 0.39/0.61               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.39/0.61                (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.61               sk_B))),
% 0.39/0.61      inference('sup-', [status(thm)], ['39', '45'])).
% 0.39/0.61  thf('47', plain,
% 0.39/0.61      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.39/0.61        | (m1_subset_1 @ 
% 0.39/0.62           (sk_D @ 
% 0.39/0.62            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.62             (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.62            sk_B @ sk_A) @ 
% 0.39/0.62           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['38', '46'])).
% 0.39/0.62  thf('48', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.39/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.62         (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      ((m1_subset_1 @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ 
% 0.39/0.62        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.39/0.62  thf('51', plain,
% 0.39/0.62      (![X15 : $i]:
% 0.39/0.62         (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X15)
% 0.39/0.62            != (k1_tarski @ sk_C_1))
% 0.39/0.62          | ~ (v4_pre_topc @ X15 @ sk_A)
% 0.39/0.62          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('52', plain,
% 0.39/0.62      ((~ (v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)
% 0.39/0.62        | ((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.62            (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A))
% 0.39/0.62            != (k1_tarski @ sk_C_1)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.62  thf('53', plain,
% 0.39/0.62      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.62         (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (m1_subset_1 @ 
% 0.39/0.62          (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.39/0.62           (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.62          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.62  thf('55', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.62          | ~ (v2_tex_2 @ X8 @ X9)
% 0.39/0.62          | (v4_pre_topc @ (sk_D @ X10 @ X8 @ X9) @ X9)
% 0.39/0.62          | ~ (r1_tarski @ X10 @ X8)
% 0.39/0.62          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.39/0.62          | ~ (l1_pre_topc @ X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [d6_tex_2])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (l1_pre_topc @ sk_A)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.62          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A)
% 0.39/0.62          | ~ (v2_tex_2 @ sk_B @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.62  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('59', plain, ((v2_tex_2 @ sk_B @ sk_A)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.39/0.62          | ~ (r1_tarski @ X0 @ sk_B)
% 0.39/0.62          | (v4_pre_topc @ (sk_D @ X0 @ sk_B @ sk_A) @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.39/0.62  thf('61', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((v4_pre_topc @ 
% 0.39/0.62           (sk_D @ 
% 0.39/0.62            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.39/0.62             (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.62            sk_B @ sk_A) @ 
% 0.39/0.62           sk_A)
% 0.39/0.62          | ~ (r1_tarski @ 
% 0.39/0.62               (k9_subset_1 @ (u1_struct_0 @ sk_A) @ X0 @ 
% 0.39/0.62                (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.62               sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['54', '60'])).
% 0.39/0.62  thf('62', plain,
% 0.39/0.62      ((~ (r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)
% 0.39/0.62        | (v4_pre_topc @ 
% 0.39/0.62           (sk_D @ 
% 0.39/0.62            (k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.62             (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) @ 
% 0.39/0.62            sk_B @ sk_A) @ 
% 0.39/0.62           sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['53', '61'])).
% 0.39/0.62  thf('63', plain, ((r1_tarski @ (k1_tarski @ sk_C_1) @ sk_B)),
% 0.39/0.62      inference('demod', [status(thm)], ['34', '35'])).
% 0.39/0.62  thf('64', plain,
% 0.39/0.62      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.62         (sk_D_1 @ sk_C_1 @ sk_B @ sk_A)) = (k1_tarski @ sk_C_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '8'])).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      ((v4_pre_topc @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A) @ sk_A)),
% 0.39/0.62      inference('demod', [status(thm)], ['62', '63', '64'])).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (((k9_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ 
% 0.39/0.62         (sk_D @ (k1_tarski @ sk_C_1) @ sk_B @ sk_A)) != (k1_tarski @ sk_C_1))),
% 0.39/0.62      inference('demod', [status(thm)], ['52', '65'])).
% 0.39/0.62  thf('67', plain, ($false),
% 0.39/0.62      inference('simplify_reflect-', [status(thm)], ['37', '66'])).
% 0.39/0.62  
% 0.39/0.62  % SZS output end Refutation
% 0.39/0.62  
% 0.48/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
