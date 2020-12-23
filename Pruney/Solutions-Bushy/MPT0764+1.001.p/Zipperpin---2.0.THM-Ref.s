%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0764+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yphfd0tHtl

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:27 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 343 expanded)
%              Number of leaves         :   33 ( 113 expanded)
%              Depth                    :   24
%              Number of atoms          : 1042 (4269 expanded)
%              Number of equality atoms :   31 ( 170 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t10_wellord1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ! [D: $i] :
                        ( ( r2_hidden @ D @ B )
                       => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( v2_wellord1 @ A )
         => ! [B: $i] :
              ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
                & ( B != k1_xboole_0 )
                & ! [C: $i] :
                    ~ ( ( r2_hidden @ C @ B )
                      & ! [D: $i] :
                          ( ( r2_hidden @ D @ B )
                         => ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_wellord1])).

thf('0',plain,(
    r1_tarski @ sk_B_3 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_wellord1 @ A )
      <=> ! [B: $i] :
            ~ ( ( r1_tarski @ B @ ( k3_relat_1 @ A ) )
              & ( B != k1_xboole_0 )
              & ! [C: $i] :
                  ~ ( ( r2_hidden @ C @ B )
                    & ( r1_xboole_0 @ ( k1_wellord1 @ A @ C ) @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i] :
      ( ~ ( v1_wellord1 @ X6 )
      | ~ ( r1_tarski @ X8 @ ( k3_relat_1 @ X6 ) )
      | ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_wellord1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 )
    | ( sk_B_3 = k1_xboole_0 )
    | ~ ( v1_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ( v1_wellord1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('6',plain,
    ( ( v1_wellord1 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_wellord1 @ sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 )
    | ( sk_B_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3','8'])).

thf('10',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_B_3 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('15',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('18',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B_3 )
      | ( r2_hidden @ ( sk_D_1 @ X30 ) @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_B_3 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B_3 @ ( k1_zfmisc_1 @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( m1_subset_1 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B_3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('28',plain,(
    m1_subset_1 @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(l4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v6_relat_2 @ A )
      <=> ! [B: $i,C: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k3_relat_1 @ A ) )
              & ( B != C )
              & ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
              & ~ ( r2_hidden @ ( k4_tarski @ C @ B ) @ A ) ) ) ) )).

thf('31',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v6_relat_2 @ X12 )
      | ~ ( r2_hidden @ X13 @ ( k3_relat_1 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X13 ) @ X12 )
      | ( r2_hidden @ ( k4_tarski @ X13 @ X14 ) @ X12 )
      | ( X13 = X14 )
      | ~ ( r2_hidden @ X14 @ ( k3_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l4_wellord1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B_3 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ X0 ) @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_A )
      | ~ ( v6_relat_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X9: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ( v6_relat_2 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('36',plain,
    ( ( v6_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v6_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ sk_A ) )
      | ( ( sk_C @ sk_B_3 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ X0 ) @ sk_A )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','38'])).

thf('40',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) ) @ sk_A )
    | ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,
    ( ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) ) @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('42',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord1 @ X2 @ X1 ) )
      | ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( X5 = X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( X5 = X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X5 @ X1 ) @ X2 )
      | ( r2_hidden @ X5 @ ( k1_wellord1 @ X2 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) ) @ sk_A )
    | ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) )
      = ( sk_C @ sk_B_3 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) ) @ sk_A )
    | ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) )
      = ( sk_C @ sk_B_3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B_3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ ( sk_D_1 @ X30 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('51',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_B_3 ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('53',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B_3 @ X0 )
      | ~ ( r2_hidden @ ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ~ ( r1_xboole_0 @ sk_B_3 @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    r1_tarski @ sk_B_3 @ ( k3_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X6: $i,X8: $i] :
      ( ~ ( v1_wellord1 @ X6 )
      | ~ ( r1_tarski @ X8 @ ( k3_relat_1 @ X6 ) )
      | ( X8 = k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_wellord1 @ X6 @ ( sk_C @ X8 @ X6 ) ) @ X8 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d2_wellord1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_xboole_0 @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_B_3 )
    | ( sk_B_3 = k1_xboole_0 )
    | ~ ( v1_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_wellord1 @ sk_A ),
    inference(demod,[status(thm)],['6','7'])).

thf('61',plain,
    ( ( r1_xboole_0 @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_B_3 )
    | ( sk_B_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    r1_xboole_0 @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_B_3 ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ( r2_hidden @ ( sk_C_2 @ X21 @ X20 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('65',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X20 @ X21 )
      | ( r2_hidden @ ( sk_C_2 @ X21 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('66',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_xboole_0 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    r1_xboole_0 @ sk_B_3 @ ( k1_wellord1 @ sk_A @ ( sk_C @ sk_B_3 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,
    ( ( ( sk_C @ sk_B_3 @ sk_A )
      = ( sk_D_1 @ ( sk_C @ sk_B_3 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','70'])).

thf('72',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_B_3 )
      | ~ ( r2_hidden @ ( k4_tarski @ X30 @ ( sk_D_1 @ X30 ) ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ sk_B_3 ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('75',plain,
    ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_A )
    | ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ sk_B_3 @ sk_A ) @ ( k3_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(l1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v1_relat_2 @ A )
      <=> ! [B: $i] :
            ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
           => ( r2_hidden @ ( k4_tarski @ B @ B ) @ A ) ) ) ) )).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_2 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X11 @ X11 ) @ X10 )
      | ~ ( r2_hidden @ X11 @ ( k3_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l1_wellord1])).

thf('78',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_A )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_A )
    | ~ ( v1_relat_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X9: $i] :
      ( ~ ( v2_wellord1 @ X9 )
      | ( v1_relat_2 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('82',plain,
    ( ( v1_relat_2 @ sk_A )
    | ~ ( v2_wellord1 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v2_wellord1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_relat_2 @ sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( k3_relat_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B_3 @ sk_A ) @ ( sk_C @ sk_B_3 @ sk_A ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['78','79','84'])).

thf('86',plain,(
    v1_xboole_0 @ ( k3_relat_1 @ sk_A ) ),
    inference(clc,[status(thm)],['75','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['16','86'])).

thf('88',plain,(
    $false ),
    inference('sup-',[status(thm)],['11','87'])).


%------------------------------------------------------------------------------
