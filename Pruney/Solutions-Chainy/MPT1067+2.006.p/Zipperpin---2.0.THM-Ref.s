%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RouijY3erv

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:56 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 147 expanded)
%              Number of leaves         :   30 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  993 (2424 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_funct_2_type,type,(
    k7_funct_2: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k6_funct_2_type,type,(
    k6_funct_2: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_setfam_1_type,type,(
    m1_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t184_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                 => ( r1_tarski @ ( k5_setfam_1 @ A @ D ) @ ( k5_setfam_1 @ A @ ( k6_funct_2 @ A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                   => ( r1_tarski @ ( k5_setfam_1 @ A @ D ) @ ( k5_setfam_1 @ A @ ( k6_funct_2 @ A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t184_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k5_setfam_1 @ sk_A @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k5_setfam_1 @ A @ B )
        = ( k3_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k5_setfam_1 @ X15 @ X14 )
        = ( k3_tarski @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('3',plain,
    ( ( k5_setfam_1 @ sk_A @ sk_D )
    = ( k3_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ sk_D ) @ ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ( m1_subset_1 @ ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X26 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X26 @ X27 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) )
     => ( m1_subset_1 @ ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X23 ) ) )
      | ( m1_subset_1 @ ( k6_funct_2 @ X22 @ X23 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_funct_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k5_setfam_1 @ X15 @ X14 )
        = ( k3_tarski @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('29',plain,
    ( ( k5_setfam_1 @ sk_A @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) )
    = ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ( r2_hidden @ ( sk_C_1 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( r2_hidden @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( r1_tarski @ X3 @ X1 )
      | ( X2
       != ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X3 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ X0 )
      | ( r1_tarski @ ( sk_C_1 @ X0 @ sk_D ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X6 ) @ X7 )
      | ~ ( r1_tarski @ ( sk_C_1 @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A )
    | ( r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ sk_A ),
    inference(simplify,[status(thm)],['39'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('42',plain,(
    m1_subset_1 @ ( k3_tarski @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t182_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) )
                     => ( ( m1_setfam_1 @ D @ E )
                       => ( m1_setfam_1 @ ( k6_funct_2 @ A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ E ) ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X31 ) ) )
      | ~ ( m1_setfam_1 @ X30 @ X32 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ X31 @ X29 @ X33 @ ( k7_funct_2 @ X31 @ X29 @ X33 @ X30 ) ) @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X31 @ X29 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t182_funct_2])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ X1 @ X0 @ ( k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D ) ) @ X2 )
      | ~ ( m1_setfam_1 @ sk_D @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_setfam_1 @ sk_D @ X0 )
      | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ~ ( m1_setfam_1 @ sk_D @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('52',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ ( k1_zfmisc_1 @ ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('53',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t60_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( m1_setfam_1 @ B @ A )
      <=> ( ( k5_setfam_1 @ A @ B )
          = A ) ) ) )).

thf('55',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k5_setfam_1 @ X19 @ X20 )
       != X19 )
      | ( m1_setfam_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t60_setfam_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) )
      | ( ( k5_setfam_1 @ ( k3_tarski @ X0 ) @ X0 )
       != ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('58',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k5_setfam_1 @ X15 @ X14 )
        = ( k3_tarski @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_setfam_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k5_setfam_1 @ ( k3_tarski @ X0 ) @ X0 )
      = ( k3_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) )
      | ( ( k3_tarski @ X0 )
       != ( k3_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( m1_setfam_1 @ X0 @ ( k3_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k3_tarski @ sk_D ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k3_tarski @ sk_D ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_setfam_1 @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) @ ( k3_tarski @ sk_D ) ),
    inference(clc,[status(thm)],['64','65'])).

thf(d12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_setfam_1 @ B @ A )
    <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('67',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ ( k3_tarski @ X12 ) )
      | ~ ( m1_setfam_1 @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d12_setfam_1])).

thf('68',plain,(
    r1_tarski @ ( k3_tarski @ sk_D ) @ ( k3_tarski @ ( k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['4','29','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RouijY3erv
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:30:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.40/2.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.40/2.65  % Solved by: fo/fo7.sh
% 2.40/2.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.40/2.65  % done 2892 iterations in 2.197s
% 2.40/2.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.40/2.65  % SZS output start Refutation
% 2.40/2.65  thf(k7_funct_2_type, type, k7_funct_2: $i > $i > $i > $i > $i).
% 2.40/2.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.40/2.65  thf(k6_funct_2_type, type, k6_funct_2: $i > $i > $i > $i > $i).
% 2.40/2.65  thf(sk_A_type, type, sk_A: $i).
% 2.40/2.65  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.40/2.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.40/2.65  thf(sk_B_type, type, sk_B: $i).
% 2.40/2.65  thf(sk_C_2_type, type, sk_C_2: $i).
% 2.40/2.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 2.40/2.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.40/2.65  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 2.40/2.65  thf(sk_D_type, type, sk_D: $i).
% 2.40/2.65  thf(m1_setfam_1_type, type, m1_setfam_1: $i > $i > $o).
% 2.40/2.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.40/2.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.40/2.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.40/2.65  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.40/2.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.40/2.65  thf(t184_funct_2, conjecture,
% 2.40/2.65    (![A:$i]:
% 2.40/2.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.40/2.65       ( ![B:$i]:
% 2.40/2.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.40/2.65           ( ![C:$i]:
% 2.40/2.65             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.40/2.65                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.40/2.65               ( ![D:$i]:
% 2.40/2.65                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.40/2.65                   ( r1_tarski @
% 2.40/2.65                     ( k5_setfam_1 @ A @ D ) @ 
% 2.40/2.65                     ( k5_setfam_1 @
% 2.40/2.65                       A @ 
% 2.40/2.65                       ( k6_funct_2 @
% 2.40/2.65                         A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 2.40/2.65  thf(zf_stmt_0, negated_conjecture,
% 2.40/2.65    (~( ![A:$i]:
% 2.40/2.65        ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.40/2.65          ( ![B:$i]:
% 2.40/2.65            ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.40/2.65              ( ![C:$i]:
% 2.40/2.65                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.40/2.65                    ( m1_subset_1 @
% 2.40/2.65                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.40/2.65                  ( ![D:$i]:
% 2.40/2.65                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.40/2.65                      ( r1_tarski @
% 2.40/2.65                        ( k5_setfam_1 @ A @ D ) @ 
% 2.40/2.65                        ( k5_setfam_1 @
% 2.40/2.65                          A @ 
% 2.40/2.65                          ( k6_funct_2 @
% 2.40/2.65                            A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ) )),
% 2.40/2.65    inference('cnf.neg', [status(esa)], [t184_funct_2])).
% 2.40/2.65  thf('0', plain,
% 2.40/2.65      (~ (r1_tarski @ (k5_setfam_1 @ sk_A @ sk_D) @ 
% 2.40/2.65          (k5_setfam_1 @ sk_A @ 
% 2.40/2.65           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('1', plain,
% 2.40/2.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf(redefinition_k5_setfam_1, axiom,
% 2.40/2.65    (![A:$i,B:$i]:
% 2.40/2.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.40/2.65       ( ( k5_setfam_1 @ A @ B ) = ( k3_tarski @ B ) ) ))).
% 2.40/2.65  thf('2', plain,
% 2.40/2.65      (![X14 : $i, X15 : $i]:
% 2.40/2.65         (((k5_setfam_1 @ X15 @ X14) = (k3_tarski @ X14))
% 2.40/2.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 2.40/2.65      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 2.40/2.65  thf('3', plain, (((k5_setfam_1 @ sk_A @ sk_D) = (k3_tarski @ sk_D))),
% 2.40/2.65      inference('sup-', [status(thm)], ['1', '2'])).
% 2.40/2.65  thf('4', plain,
% 2.40/2.65      (~ (r1_tarski @ (k3_tarski @ sk_D) @ 
% 2.40/2.65          (k5_setfam_1 @ sk_A @ 
% 2.40/2.65           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 2.40/2.65      inference('demod', [status(thm)], ['0', '3'])).
% 2.40/2.65  thf('5', plain,
% 2.40/2.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('6', plain,
% 2.40/2.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf(dt_k7_funct_2, axiom,
% 2.40/2.65    (![A:$i,B:$i,C:$i,D:$i]:
% 2.40/2.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 2.40/2.65         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.40/2.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.40/2.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) =>
% 2.40/2.65       ( m1_subset_1 @
% 2.40/2.65         ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ))).
% 2.40/2.65  thf('7', plain,
% 2.40/2.65      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 2.40/2.65         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 2.40/2.65          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 2.40/2.65          | ~ (v1_funct_1 @ X25)
% 2.40/2.65          | (v1_xboole_0 @ X27)
% 2.40/2.65          | (v1_xboole_0 @ X26)
% 2.40/2.65          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X26)))
% 2.40/2.65          | (m1_subset_1 @ (k7_funct_2 @ X26 @ X27 @ X25 @ X28) @ 
% 2.40/2.65             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X27))))),
% 2.40/2.65      inference('cnf', [status(esa)], [dt_k7_funct_2])).
% 2.40/2.65  thf('8', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 2.40/2.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.40/2.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.40/2.65          | (v1_xboole_0 @ sk_A)
% 2.40/2.65          | (v1_xboole_0 @ sk_B)
% 2.40/2.65          | ~ (v1_funct_1 @ sk_C_2)
% 2.40/2.65          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 2.40/2.65      inference('sup-', [status(thm)], ['6', '7'])).
% 2.40/2.65  thf('9', plain, ((v1_funct_1 @ sk_C_2)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('10', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('11', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 2.40/2.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.40/2.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.40/2.65          | (v1_xboole_0 @ sk_A)
% 2.40/2.65          | (v1_xboole_0 @ sk_B))),
% 2.40/2.65      inference('demod', [status(thm)], ['8', '9', '10'])).
% 2.40/2.65  thf('12', plain,
% 2.40/2.65      (((v1_xboole_0 @ sk_B)
% 2.40/2.65        | (v1_xboole_0 @ sk_A)
% 2.40/2.65        | (m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D) @ 
% 2.40/2.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B))))),
% 2.40/2.65      inference('sup-', [status(thm)], ['5', '11'])).
% 2.40/2.65  thf('13', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('14', plain,
% 2.40/2.65      (((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D) @ 
% 2.40/2.65         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.40/2.65        | (v1_xboole_0 @ sk_A))),
% 2.40/2.65      inference('clc', [status(thm)], ['12', '13'])).
% 2.40/2.65  thf('15', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('16', plain,
% 2.40/2.65      ((m1_subset_1 @ (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D) @ 
% 2.40/2.65        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))),
% 2.40/2.65      inference('clc', [status(thm)], ['14', '15'])).
% 2.40/2.65  thf('17', plain,
% 2.40/2.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf(dt_k6_funct_2, axiom,
% 2.40/2.65    (![A:$i,B:$i,C:$i,D:$i]:
% 2.40/2.65     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 2.40/2.65         ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.40/2.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.40/2.65         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) =>
% 2.40/2.65       ( m1_subset_1 @
% 2.40/2.65         ( k6_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 2.40/2.65  thf('18', plain,
% 2.40/2.65      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 2.40/2.65         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 2.40/2.65          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 2.40/2.65          | ~ (v1_funct_1 @ X21)
% 2.40/2.65          | (v1_xboole_0 @ X23)
% 2.40/2.65          | (v1_xboole_0 @ X22)
% 2.40/2.65          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X23)))
% 2.40/2.65          | (m1_subset_1 @ (k6_funct_2 @ X22 @ X23 @ X21 @ X24) @ 
% 2.40/2.65             (k1_zfmisc_1 @ (k1_zfmisc_1 @ X22))))),
% 2.40/2.65      inference('cnf', [status(esa)], [dt_k6_funct_2])).
% 2.40/2.65  thf('19', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 2.40/2.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.40/2.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.40/2.65          | (v1_xboole_0 @ sk_A)
% 2.40/2.65          | (v1_xboole_0 @ sk_B)
% 2.40/2.65          | ~ (v1_funct_1 @ sk_C_2)
% 2.40/2.65          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B))),
% 2.40/2.65      inference('sup-', [status(thm)], ['17', '18'])).
% 2.40/2.65  thf('20', plain, ((v1_funct_1 @ sk_C_2)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('21', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('22', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((m1_subset_1 @ (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ X0) @ 
% 2.40/2.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.40/2.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_B)))
% 2.40/2.65          | (v1_xboole_0 @ sk_A)
% 2.40/2.65          | (v1_xboole_0 @ sk_B))),
% 2.40/2.65      inference('demod', [status(thm)], ['19', '20', '21'])).
% 2.40/2.65  thf('23', plain,
% 2.40/2.65      (((v1_xboole_0 @ sk_B)
% 2.40/2.65        | (v1_xboole_0 @ sk_A)
% 2.40/2.65        | (m1_subset_1 @ 
% 2.40/2.65           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65           (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 2.40/2.65      inference('sup-', [status(thm)], ['16', '22'])).
% 2.40/2.65  thf('24', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('25', plain,
% 2.40/2.65      (((m1_subset_1 @ 
% 2.40/2.65         (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65          (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65         (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 2.40/2.65        | (v1_xboole_0 @ sk_A))),
% 2.40/2.65      inference('clc', [status(thm)], ['23', '24'])).
% 2.40/2.65  thf('26', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('27', plain,
% 2.40/2.65      ((m1_subset_1 @ 
% 2.40/2.65        (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65         (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.40/2.65      inference('clc', [status(thm)], ['25', '26'])).
% 2.40/2.65  thf('28', plain,
% 2.40/2.65      (![X14 : $i, X15 : $i]:
% 2.40/2.65         (((k5_setfam_1 @ X15 @ X14) = (k3_tarski @ X14))
% 2.40/2.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 2.40/2.65      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 2.40/2.65  thf('29', plain,
% 2.40/2.65      (((k5_setfam_1 @ sk_A @ 
% 2.40/2.65         (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65          (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)))
% 2.40/2.65         = (k3_tarski @ 
% 2.40/2.65            (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65             (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 2.40/2.65      inference('sup-', [status(thm)], ['27', '28'])).
% 2.40/2.65  thf(t94_zfmisc_1, axiom,
% 2.40/2.65    (![A:$i,B:$i]:
% 2.40/2.65     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 2.40/2.65       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 2.40/2.65  thf('30', plain,
% 2.40/2.65      (![X6 : $i, X7 : $i]:
% 2.40/2.65         ((r1_tarski @ (k3_tarski @ X6) @ X7)
% 2.40/2.65          | (r2_hidden @ (sk_C_1 @ X7 @ X6) @ X6))),
% 2.40/2.65      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 2.40/2.65  thf('31', plain,
% 2.40/2.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf(l3_subset_1, axiom,
% 2.40/2.65    (![A:$i,B:$i]:
% 2.40/2.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 2.40/2.65  thf('32', plain,
% 2.40/2.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.40/2.65         (~ (r2_hidden @ X8 @ X9)
% 2.40/2.65          | (r2_hidden @ X8 @ X10)
% 2.40/2.65          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 2.40/2.65      inference('cnf', [status(esa)], [l3_subset_1])).
% 2.40/2.65  thf('33', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((r2_hidden @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_D))),
% 2.40/2.65      inference('sup-', [status(thm)], ['31', '32'])).
% 2.40/2.65  thf('34', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((r1_tarski @ (k3_tarski @ sk_D) @ X0)
% 2.40/2.65          | (r2_hidden @ (sk_C_1 @ X0 @ sk_D) @ (k1_zfmisc_1 @ sk_A)))),
% 2.40/2.65      inference('sup-', [status(thm)], ['30', '33'])).
% 2.40/2.65  thf(d1_zfmisc_1, axiom,
% 2.40/2.65    (![A:$i,B:$i]:
% 2.40/2.65     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 2.40/2.65       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 2.40/2.65  thf('35', plain,
% 2.40/2.65      (![X1 : $i, X2 : $i, X3 : $i]:
% 2.40/2.65         (~ (r2_hidden @ X3 @ X2)
% 2.40/2.65          | (r1_tarski @ X3 @ X1)
% 2.40/2.65          | ((X2) != (k1_zfmisc_1 @ X1)))),
% 2.40/2.65      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 2.40/2.65  thf('36', plain,
% 2.40/2.65      (![X1 : $i, X3 : $i]:
% 2.40/2.65         ((r1_tarski @ X3 @ X1) | ~ (r2_hidden @ X3 @ (k1_zfmisc_1 @ X1)))),
% 2.40/2.65      inference('simplify', [status(thm)], ['35'])).
% 2.40/2.65  thf('37', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((r1_tarski @ (k3_tarski @ sk_D) @ X0)
% 2.40/2.65          | (r1_tarski @ (sk_C_1 @ X0 @ sk_D) @ sk_A))),
% 2.40/2.65      inference('sup-', [status(thm)], ['34', '36'])).
% 2.40/2.65  thf('38', plain,
% 2.40/2.65      (![X6 : $i, X7 : $i]:
% 2.40/2.65         ((r1_tarski @ (k3_tarski @ X6) @ X7)
% 2.40/2.65          | ~ (r1_tarski @ (sk_C_1 @ X7 @ X6) @ X7))),
% 2.40/2.65      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 2.40/2.65  thf('39', plain,
% 2.40/2.65      (((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)
% 2.40/2.65        | (r1_tarski @ (k3_tarski @ sk_D) @ sk_A))),
% 2.40/2.65      inference('sup-', [status(thm)], ['37', '38'])).
% 2.40/2.65  thf('40', plain, ((r1_tarski @ (k3_tarski @ sk_D) @ sk_A)),
% 2.40/2.65      inference('simplify', [status(thm)], ['39'])).
% 2.40/2.65  thf(t3_subset, axiom,
% 2.40/2.65    (![A:$i,B:$i]:
% 2.40/2.65     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.40/2.65  thf('41', plain,
% 2.40/2.65      (![X16 : $i, X18 : $i]:
% 2.40/2.65         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 2.40/2.65      inference('cnf', [status(esa)], [t3_subset])).
% 2.40/2.65  thf('42', plain, ((m1_subset_1 @ (k3_tarski @ sk_D) @ (k1_zfmisc_1 @ sk_A))),
% 2.40/2.65      inference('sup-', [status(thm)], ['40', '41'])).
% 2.40/2.65  thf('43', plain,
% 2.40/2.65      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('44', plain,
% 2.40/2.65      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf(t182_funct_2, axiom,
% 2.40/2.65    (![A:$i]:
% 2.40/2.65     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.40/2.65       ( ![B:$i]:
% 2.40/2.65         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.40/2.65           ( ![C:$i]:
% 2.40/2.65             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.40/2.65                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.40/2.65               ( ![D:$i]:
% 2.40/2.65                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.40/2.65                   ( ![E:$i]:
% 2.40/2.65                     ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ A ) ) =>
% 2.40/2.65                       ( ( m1_setfam_1 @ D @ E ) =>
% 2.40/2.65                         ( m1_setfam_1 @
% 2.40/2.65                           ( k6_funct_2 @
% 2.40/2.65                             A @ B @ C @ ( k7_funct_2 @ A @ B @ C @ D ) ) @ 
% 2.40/2.65                           E ) ) ) ) ) ) ) ) ) ) ))).
% 2.40/2.65  thf('45', plain,
% 2.40/2.65      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 2.40/2.65         ((v1_xboole_0 @ X29)
% 2.40/2.65          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X31)))
% 2.40/2.65          | ~ (m1_setfam_1 @ X30 @ X32)
% 2.40/2.65          | (m1_setfam_1 @ 
% 2.40/2.65             (k6_funct_2 @ X31 @ X29 @ X33 @ 
% 2.40/2.65              (k7_funct_2 @ X31 @ X29 @ X33 @ X30)) @ 
% 2.40/2.65             X32)
% 2.40/2.65          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31))
% 2.40/2.65          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X29)))
% 2.40/2.65          | ~ (v1_funct_2 @ X33 @ X31 @ X29)
% 2.40/2.65          | ~ (v1_funct_1 @ X33)
% 2.40/2.65          | (v1_xboole_0 @ X31))),
% 2.40/2.65      inference('cnf', [status(esa)], [t182_funct_2])).
% 2.40/2.65  thf('46', plain,
% 2.40/2.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.65         ((v1_xboole_0 @ sk_A)
% 2.40/2.65          | ~ (v1_funct_1 @ X0)
% 2.40/2.65          | ~ (v1_funct_2 @ X0 @ sk_A @ X1)
% 2.40/2.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 2.40/2.65          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ sk_A))
% 2.40/2.65          | (m1_setfam_1 @ 
% 2.40/2.65             (k6_funct_2 @ sk_A @ X1 @ X0 @ 
% 2.40/2.65              (k7_funct_2 @ sk_A @ X1 @ X0 @ sk_D)) @ 
% 2.40/2.65             X2)
% 2.40/2.65          | ~ (m1_setfam_1 @ sk_D @ X2)
% 2.40/2.65          | (v1_xboole_0 @ X1))),
% 2.40/2.65      inference('sup-', [status(thm)], ['44', '45'])).
% 2.40/2.65  thf('47', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((v1_xboole_0 @ sk_B)
% 2.40/2.65          | ~ (m1_setfam_1 @ sk_D @ X0)
% 2.40/2.65          | (m1_setfam_1 @ 
% 2.40/2.65             (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65              (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65             X0)
% 2.40/2.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 2.40/2.65          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 2.40/2.65          | ~ (v1_funct_1 @ sk_C_2)
% 2.40/2.65          | (v1_xboole_0 @ sk_A))),
% 2.40/2.65      inference('sup-', [status(thm)], ['43', '46'])).
% 2.40/2.65  thf('48', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('49', plain, ((v1_funct_1 @ sk_C_2)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('50', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((v1_xboole_0 @ sk_B)
% 2.40/2.65          | ~ (m1_setfam_1 @ sk_D @ X0)
% 2.40/2.65          | (m1_setfam_1 @ 
% 2.40/2.65             (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65              (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65             X0)
% 2.40/2.65          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 2.40/2.65          | (v1_xboole_0 @ sk_A))),
% 2.40/2.65      inference('demod', [status(thm)], ['47', '48', '49'])).
% 2.40/2.65  thf('51', plain,
% 2.40/2.65      (((v1_xboole_0 @ sk_A)
% 2.40/2.65        | (m1_setfam_1 @ 
% 2.40/2.65           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65           (k3_tarski @ sk_D))
% 2.40/2.65        | ~ (m1_setfam_1 @ sk_D @ (k3_tarski @ sk_D))
% 2.40/2.65        | (v1_xboole_0 @ sk_B))),
% 2.40/2.65      inference('sup-', [status(thm)], ['42', '50'])).
% 2.40/2.65  thf(t100_zfmisc_1, axiom,
% 2.40/2.65    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 2.40/2.65  thf('52', plain,
% 2.40/2.65      (![X5 : $i]: (r1_tarski @ X5 @ (k1_zfmisc_1 @ (k3_tarski @ X5)))),
% 2.40/2.65      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 2.40/2.65  thf('53', plain,
% 2.40/2.65      (![X16 : $i, X18 : $i]:
% 2.40/2.65         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 2.40/2.65      inference('cnf', [status(esa)], [t3_subset])).
% 2.40/2.65  thf('54', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 2.40/2.65      inference('sup-', [status(thm)], ['52', '53'])).
% 2.40/2.65  thf(t60_setfam_1, axiom,
% 2.40/2.65    (![A:$i,B:$i]:
% 2.40/2.65     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.40/2.65       ( ( m1_setfam_1 @ B @ A ) <=> ( ( k5_setfam_1 @ A @ B ) = ( A ) ) ) ))).
% 2.40/2.65  thf('55', plain,
% 2.40/2.65      (![X19 : $i, X20 : $i]:
% 2.40/2.65         (((k5_setfam_1 @ X19 @ X20) != (X19))
% 2.40/2.65          | (m1_setfam_1 @ X20 @ X19)
% 2.40/2.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X19))))),
% 2.40/2.65      inference('cnf', [status(esa)], [t60_setfam_1])).
% 2.40/2.65  thf('56', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((m1_setfam_1 @ X0 @ (k3_tarski @ X0))
% 2.40/2.65          | ((k5_setfam_1 @ (k3_tarski @ X0) @ X0) != (k3_tarski @ X0)))),
% 2.40/2.65      inference('sup-', [status(thm)], ['54', '55'])).
% 2.40/2.65  thf('57', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 2.40/2.65      inference('sup-', [status(thm)], ['52', '53'])).
% 2.40/2.65  thf('58', plain,
% 2.40/2.65      (![X14 : $i, X15 : $i]:
% 2.40/2.65         (((k5_setfam_1 @ X15 @ X14) = (k3_tarski @ X14))
% 2.40/2.65          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 2.40/2.65      inference('cnf', [status(esa)], [redefinition_k5_setfam_1])).
% 2.40/2.65  thf('59', plain,
% 2.40/2.65      (![X0 : $i]: ((k5_setfam_1 @ (k3_tarski @ X0) @ X0) = (k3_tarski @ X0))),
% 2.40/2.65      inference('sup-', [status(thm)], ['57', '58'])).
% 2.40/2.65  thf('60', plain,
% 2.40/2.65      (![X0 : $i]:
% 2.40/2.65         ((m1_setfam_1 @ X0 @ (k3_tarski @ X0))
% 2.40/2.65          | ((k3_tarski @ X0) != (k3_tarski @ X0)))),
% 2.40/2.65      inference('demod', [status(thm)], ['56', '59'])).
% 2.40/2.65  thf('61', plain, (![X0 : $i]: (m1_setfam_1 @ X0 @ (k3_tarski @ X0))),
% 2.40/2.65      inference('simplify', [status(thm)], ['60'])).
% 2.40/2.65  thf('62', plain,
% 2.40/2.65      (((v1_xboole_0 @ sk_A)
% 2.40/2.65        | (m1_setfam_1 @ 
% 2.40/2.65           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65           (k3_tarski @ sk_D))
% 2.40/2.65        | (v1_xboole_0 @ sk_B))),
% 2.40/2.65      inference('demod', [status(thm)], ['51', '61'])).
% 2.40/2.65  thf('63', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('64', plain,
% 2.40/2.65      (((v1_xboole_0 @ sk_B)
% 2.40/2.65        | (m1_setfam_1 @ 
% 2.40/2.65           (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65            (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65           (k3_tarski @ sk_D)))),
% 2.40/2.65      inference('clc', [status(thm)], ['62', '63'])).
% 2.40/2.65  thf('65', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.40/2.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.65  thf('66', plain,
% 2.40/2.65      ((m1_setfam_1 @ 
% 2.40/2.65        (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65         (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D)) @ 
% 2.40/2.65        (k3_tarski @ sk_D))),
% 2.40/2.65      inference('clc', [status(thm)], ['64', '65'])).
% 2.40/2.65  thf(d12_setfam_1, axiom,
% 2.40/2.65    (![A:$i,B:$i]:
% 2.40/2.65     ( ( m1_setfam_1 @ B @ A ) <=> ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 2.40/2.65  thf('67', plain,
% 2.40/2.65      (![X11 : $i, X12 : $i]:
% 2.40/2.65         ((r1_tarski @ X11 @ (k3_tarski @ X12)) | ~ (m1_setfam_1 @ X12 @ X11))),
% 2.40/2.65      inference('cnf', [status(esa)], [d12_setfam_1])).
% 2.40/2.65  thf('68', plain,
% 2.40/2.65      ((r1_tarski @ (k3_tarski @ sk_D) @ 
% 2.40/2.65        (k3_tarski @ 
% 2.40/2.65         (k6_funct_2 @ sk_A @ sk_B @ sk_C_2 @ 
% 2.40/2.65          (k7_funct_2 @ sk_A @ sk_B @ sk_C_2 @ sk_D))))),
% 2.40/2.65      inference('sup-', [status(thm)], ['66', '67'])).
% 2.40/2.65  thf('69', plain, ($false),
% 2.40/2.65      inference('demod', [status(thm)], ['4', '29', '68'])).
% 2.40/2.65  
% 2.40/2.65  % SZS output end Refutation
% 2.40/2.65  
% 2.50/2.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
