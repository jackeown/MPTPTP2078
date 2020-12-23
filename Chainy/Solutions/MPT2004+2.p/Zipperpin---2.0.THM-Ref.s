%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2004+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gA0Xi9A9W9

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:06 EST 2020

% Result     : Theorem 3.57s
% Output     : Refutation 3.57s
% Verified   : 
% Statistics : Number of formulae       :   18 (  24 expanded)
%              Number of leaves         :   10 (  13 expanded)
%              Depth                    :    5
%              Number of atoms          :   89 ( 281 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   16 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_290_type,type,(
    sk_B_290: $i )).

thf(sk_A_98_type,type,(
    sk_A_98: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_349_type,type,(
    sk_C_349: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_441_type,type,(
    sk_D_441: $i )).

thf(t3_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ ( D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) )
                 => ( ( ( ( u1_struct_0 @ A )
                        = ( u1_struct_0 @ B ) )
                      & ( C = D )
                      & ( m1_setfam_1 @ ( C @ ( u1_struct_0 @ A ) ) ) )
                   => ( m1_setfam_1 @ ( D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( l1_struct_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ ( D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) )
                   => ( ( ( ( u1_struct_0 @ A )
                          = ( u1_struct_0 @ B ) )
                        & ( C = D )
                        & ( m1_setfam_1 @ ( C @ ( u1_struct_0 @ A ) ) ) )
                     => ( m1_setfam_1 @ ( D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_waybel_9])).

thf('0',plain,(
    ~ ( m1_setfam_1 @ ( sk_D_441 @ ( u1_struct_0 @ sk_B_290 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_C_349 = sk_D_441 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ~ ( m1_setfam_1 @ ( sk_C_349 @ ( u1_struct_0 @ sk_B_290 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( u1_struct_0 @ sk_A_98 )
    = ( u1_struct_0 @ sk_B_290 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( m1_setfam_1 @ ( sk_C_349 @ ( u1_struct_0 @ sk_A_98 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_setfam_1 @ ( sk_C_349 @ ( u1_struct_0 @ sk_A_98 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    $false ),
    inference(demod,[status(thm)],['4','5'])).

%------------------------------------------------------------------------------
