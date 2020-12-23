%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PJ8gmPfxIH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:08 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 223 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  782 (3247 expanded)
%              Number of equality atoms :   67 ( 227 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( X31 = X28 )
      | ~ ( r1_partfun1 @ X31 @ X28 )
      | ~ ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v1_partfun1 @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_2 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_2 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('25',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('27',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('30',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('38',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C_1 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('41',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('47',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','47','48'])).

thf('50',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','50'])).

thf('52',plain,(
    ! [X21: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X21 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('57',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['46'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('65',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X17 @ X18 @ X19 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['65'])).

thf('67',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C_1 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','67'])).

thf('69',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('70',plain,
    ( ( sk_C_1 = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('71',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['62','71'])).

thf('73',plain,
    ( ( sk_B_2 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['35'])).

thf('74',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['36','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['34','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ sk_B_2 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_B_2 ) ),
    inference('simplify_reflect+',[status(thm)],['77','78'])).

thf('80',plain,(
    sk_C_1 = sk_D ),
    inference(clc,[status(thm)],['24','79'])).

thf('81',plain,(
    r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['64','66'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PJ8gmPfxIH
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/1.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/1.04  % Solved by: fo/fo7.sh
% 0.81/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.04  % done 743 iterations in 0.575s
% 0.81/1.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/1.04  % SZS output start Refutation
% 0.81/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.04  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.81/1.04  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.81/1.04  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.81/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.81/1.04  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.81/1.04  thf(sk_D_type, type, sk_D: $i).
% 0.81/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.81/1.04  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.81/1.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.81/1.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.81/1.04  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.04  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.81/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.81/1.04  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.81/1.04  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.81/1.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.81/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.81/1.04  thf(t142_funct_2, conjecture,
% 0.81/1.04    (![A:$i,B:$i,C:$i]:
% 0.81/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.81/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.04       ( ![D:$i]:
% 0.81/1.04         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.81/1.04             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.04           ( ( r1_partfun1 @ C @ D ) =>
% 0.81/1.04             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.81/1.04               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.81/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.04    (~( ![A:$i,B:$i,C:$i]:
% 0.81/1.04        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.81/1.04            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.04          ( ![D:$i]:
% 0.81/1.04            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.81/1.04                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.04              ( ( r1_partfun1 @ C @ D ) =>
% 0.81/1.04                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.81/1.04                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.81/1.04    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.81/1.04  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('1', plain,
% 0.81/1.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('2', plain,
% 0.81/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf(cc5_funct_2, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.81/1.04       ( ![C:$i]:
% 0.81/1.04         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.81/1.04           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.81/1.04             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.81/1.04  thf('3', plain,
% 0.81/1.04      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.81/1.04         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.81/1.04          | (v1_partfun1 @ X25 @ X26)
% 0.81/1.04          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.81/1.04          | ~ (v1_funct_1 @ X25)
% 0.81/1.04          | (v1_xboole_0 @ X27))),
% 0.81/1.04      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.81/1.04  thf('4', plain,
% 0.81/1.04      (((v1_xboole_0 @ sk_B_2)
% 0.81/1.04        | ~ (v1_funct_1 @ sk_D)
% 0.81/1.04        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_2)
% 0.81/1.04        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.81/1.04      inference('sup-', [status(thm)], ['2', '3'])).
% 0.81/1.04  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_2)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('7', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.81/1.04      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.81/1.04  thf('8', plain,
% 0.81/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf(t148_partfun1, axiom,
% 0.81/1.04    (![A:$i,B:$i,C:$i]:
% 0.81/1.04     ( ( ( v1_funct_1 @ C ) & 
% 0.81/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.04       ( ![D:$i]:
% 0.81/1.04         ( ( ( v1_funct_1 @ D ) & 
% 0.81/1.04             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.04           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.81/1.04               ( r1_partfun1 @ C @ D ) ) =>
% 0.81/1.04             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.81/1.04  thf('9', plain,
% 0.81/1.04      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.81/1.04         (~ (v1_funct_1 @ X28)
% 0.81/1.04          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.81/1.04          | ((X31) = (X28))
% 0.81/1.04          | ~ (r1_partfun1 @ X31 @ X28)
% 0.81/1.04          | ~ (v1_partfun1 @ X28 @ X29)
% 0.81/1.04          | ~ (v1_partfun1 @ X31 @ X29)
% 0.81/1.04          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.81/1.04          | ~ (v1_funct_1 @ X31))),
% 0.81/1.04      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.81/1.04  thf('10', plain,
% 0.81/1.04      (![X0 : $i]:
% 0.81/1.04         (~ (v1_funct_1 @ X0)
% 0.81/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.81/1.04          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.81/1.04          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.81/1.04          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.81/1.04          | ((X0) = (sk_D))
% 0.81/1.04          | ~ (v1_funct_1 @ sk_D))),
% 0.81/1.04      inference('sup-', [status(thm)], ['8', '9'])).
% 0.81/1.04  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('12', plain,
% 0.81/1.04      (![X0 : $i]:
% 0.81/1.04         (~ (v1_funct_1 @ X0)
% 0.81/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.81/1.04          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.81/1.04          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.81/1.04          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.81/1.04          | ((X0) = (sk_D)))),
% 0.81/1.04      inference('demod', [status(thm)], ['10', '11'])).
% 0.81/1.04  thf('13', plain,
% 0.81/1.04      (![X0 : $i]:
% 0.81/1.04         ((v1_xboole_0 @ sk_B_2)
% 0.81/1.04          | ((X0) = (sk_D))
% 0.81/1.04          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.81/1.04          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.81/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))
% 0.81/1.04          | ~ (v1_funct_1 @ X0))),
% 0.81/1.04      inference('sup-', [status(thm)], ['7', '12'])).
% 0.81/1.04  thf('14', plain,
% 0.81/1.04      ((~ (v1_funct_1 @ sk_C_1)
% 0.81/1.04        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.81/1.04        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.81/1.04        | ((sk_C_1) = (sk_D))
% 0.81/1.04        | (v1_xboole_0 @ sk_B_2))),
% 0.81/1.04      inference('sup-', [status(thm)], ['1', '13'])).
% 0.81/1.04  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('16', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('17', plain,
% 0.81/1.04      ((~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.81/1.04        | ((sk_C_1) = (sk_D))
% 0.81/1.04        | (v1_xboole_0 @ sk_B_2))),
% 0.81/1.04      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.81/1.04  thf('18', plain,
% 0.81/1.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('19', plain,
% 0.81/1.04      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.81/1.04         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.81/1.04          | (v1_partfun1 @ X25 @ X26)
% 0.81/1.04          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.81/1.04          | ~ (v1_funct_1 @ X25)
% 0.81/1.04          | (v1_xboole_0 @ X27))),
% 0.81/1.04      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.81/1.04  thf('20', plain,
% 0.81/1.04      (((v1_xboole_0 @ sk_B_2)
% 0.81/1.04        | ~ (v1_funct_1 @ sk_C_1)
% 0.81/1.04        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)
% 0.81/1.04        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.81/1.04      inference('sup-', [status(thm)], ['18', '19'])).
% 0.81/1.04  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('22', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_2)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('23', plain, (((v1_xboole_0 @ sk_B_2) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.81/1.04      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.81/1.04  thf('24', plain, (((v1_xboole_0 @ sk_B_2) | ((sk_C_1) = (sk_D)))),
% 0.81/1.04      inference('clc', [status(thm)], ['17', '23'])).
% 0.81/1.04  thf(t29_mcart_1, axiom,
% 0.81/1.04    (![A:$i]:
% 0.81/1.04     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.81/1.04          ( ![B:$i]:
% 0.81/1.04            ( ~( ( r2_hidden @ B @ A ) & 
% 0.81/1.04                 ( ![C:$i,D:$i,E:$i]:
% 0.81/1.04                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.81/1.04                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.81/1.04  thf('25', plain,
% 0.81/1.04      (![X21 : $i]:
% 0.81/1.04         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X21) @ X21))),
% 0.81/1.04      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.81/1.04  thf(d10_xboole_0, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.81/1.04  thf('26', plain,
% 0.81/1.04      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.81/1.04      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.81/1.04  thf('27', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.81/1.04      inference('simplify', [status(thm)], ['26'])).
% 0.81/1.04  thf(t3_subset, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.81/1.04  thf('28', plain,
% 0.81/1.04      (![X11 : $i, X13 : $i]:
% 0.81/1.04         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.81/1.04      inference('cnf', [status(esa)], [t3_subset])).
% 0.81/1.04  thf('29', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.81/1.04      inference('sup-', [status(thm)], ['27', '28'])).
% 0.81/1.04  thf(t5_subset, axiom,
% 0.81/1.04    (![A:$i,B:$i,C:$i]:
% 0.81/1.04     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.81/1.04          ( v1_xboole_0 @ C ) ) ))).
% 0.81/1.04  thf('30', plain,
% 0.81/1.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.81/1.04         (~ (r2_hidden @ X14 @ X15)
% 0.81/1.04          | ~ (v1_xboole_0 @ X16)
% 0.81/1.04          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.81/1.04      inference('cnf', [status(esa)], [t5_subset])).
% 0.81/1.04  thf('31', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.81/1.04      inference('sup-', [status(thm)], ['29', '30'])).
% 0.81/1.04  thf('32', plain,
% 0.81/1.04      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.81/1.04      inference('sup-', [status(thm)], ['25', '31'])).
% 0.81/1.04  thf('33', plain,
% 0.81/1.04      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.81/1.04      inference('sup-', [status(thm)], ['25', '31'])).
% 0.81/1.04  thf('34', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i]:
% 0.81/1.04         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.81/1.04      inference('sup+', [status(thm)], ['32', '33'])).
% 0.81/1.04  thf('35', plain, ((((sk_B_2) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('36', plain,
% 0.81/1.04      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_xboole_0))))),
% 0.81/1.04      inference('split', [status(esa)], ['35'])).
% 0.81/1.04  thf('37', plain,
% 0.81/1.04      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('split', [status(esa)], ['35'])).
% 0.81/1.04  thf('38', plain, (~ (r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_D)),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('39', plain,
% 0.81/1.04      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C_1 @ sk_D))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup-', [status(thm)], ['37', '38'])).
% 0.81/1.04  thf('40', plain,
% 0.81/1.04      (![X21 : $i]:
% 0.81/1.04         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X21) @ X21))),
% 0.81/1.04      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.81/1.04  thf('41', plain,
% 0.81/1.04      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('split', [status(esa)], ['35'])).
% 0.81/1.04  thf('42', plain,
% 0.81/1.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('43', plain,
% 0.81/1.04      (((m1_subset_1 @ sk_C_1 @ 
% 0.81/1.04         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup+', [status(thm)], ['41', '42'])).
% 0.81/1.04  thf('44', plain,
% 0.81/1.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.81/1.04         (~ (r2_hidden @ X14 @ X15)
% 0.81/1.04          | ~ (v1_xboole_0 @ X16)
% 0.81/1.04          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.81/1.04      inference('cnf', [status(esa)], [t5_subset])).
% 0.81/1.04  thf('45', plain,
% 0.81/1.04      ((![X0 : $i]:
% 0.81/1.04          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))
% 0.81/1.04           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup-', [status(thm)], ['43', '44'])).
% 0.81/1.04  thf(t113_zfmisc_1, axiom,
% 0.81/1.04    (![A:$i,B:$i]:
% 0.81/1.04     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.81/1.04       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.81/1.04  thf('46', plain,
% 0.81/1.04      (![X8 : $i, X9 : $i]:
% 0.81/1.04         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.81/1.04      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.81/1.04  thf('47', plain,
% 0.81/1.04      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.81/1.04      inference('simplify', [status(thm)], ['46'])).
% 0.81/1.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.81/1.04  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.81/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.81/1.04  thf('49', plain,
% 0.81/1.04      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('demod', [status(thm)], ['45', '47', '48'])).
% 0.81/1.04  thf('50', plain,
% 0.81/1.04      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup-', [status(thm)], ['40', '49'])).
% 0.81/1.04  thf('51', plain,
% 0.81/1.04      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ sk_D))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('demod', [status(thm)], ['39', '50'])).
% 0.81/1.04  thf('52', plain,
% 0.81/1.04      (![X21 : $i]:
% 0.81/1.04         (((X21) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X21) @ X21))),
% 0.81/1.04      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.81/1.04  thf('53', plain,
% 0.81/1.04      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('split', [status(esa)], ['35'])).
% 0.81/1.04  thf('54', plain,
% 0.81/1.04      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf('55', plain,
% 0.81/1.04      (((m1_subset_1 @ sk_D @ 
% 0.81/1.04         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup+', [status(thm)], ['53', '54'])).
% 0.81/1.04  thf('56', plain,
% 0.81/1.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.81/1.04         (~ (r2_hidden @ X14 @ X15)
% 0.81/1.04          | ~ (v1_xboole_0 @ X16)
% 0.81/1.04          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.81/1.04      inference('cnf', [status(esa)], [t5_subset])).
% 0.81/1.04  thf('57', plain,
% 0.81/1.04      ((![X0 : $i]:
% 0.81/1.04          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_2))
% 0.81/1.04           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup-', [status(thm)], ['55', '56'])).
% 0.81/1.04  thf('58', plain,
% 0.81/1.04      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.81/1.04      inference('simplify', [status(thm)], ['46'])).
% 0.81/1.04  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.81/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.81/1.04  thf('60', plain,
% 0.81/1.04      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.81/1.04  thf('61', plain,
% 0.81/1.04      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup-', [status(thm)], ['52', '60'])).
% 0.81/1.04  thf('62', plain,
% 0.81/1.04      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('demod', [status(thm)], ['51', '61'])).
% 0.81/1.04  thf('63', plain,
% 0.81/1.04      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('split', [status(esa)], ['35'])).
% 0.81/1.04  thf('64', plain,
% 0.81/1.04      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.81/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.04  thf(reflexivity_r2_relset_1, axiom,
% 0.81/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.81/1.04     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.81/1.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.81/1.04       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.81/1.04  thf('65', plain,
% 0.81/1.04      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.81/1.04         ((r2_relset_1 @ X17 @ X18 @ X19 @ X19)
% 0.81/1.04          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.81/1.04          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.81/1.04      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.81/1.04  thf('66', plain,
% 0.81/1.04      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.04         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.81/1.04          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.81/1.04      inference('condensation', [status(thm)], ['65'])).
% 0.81/1.04  thf('67', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_C_1)),
% 0.81/1.04      inference('sup-', [status(thm)], ['64', '66'])).
% 0.81/1.04  thf('68', plain,
% 0.81/1.04      (((r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ sk_C_1 @ sk_C_1))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup+', [status(thm)], ['63', '67'])).
% 0.81/1.04  thf('69', plain,
% 0.81/1.04      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup-', [status(thm)], ['40', '49'])).
% 0.81/1.04  thf('70', plain,
% 0.81/1.04      ((((sk_C_1) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('sup-', [status(thm)], ['40', '49'])).
% 0.81/1.04  thf('71', plain,
% 0.81/1.04      (((r2_relset_1 @ k1_xboole_0 @ sk_B_2 @ k1_xboole_0 @ k1_xboole_0))
% 0.81/1.04         <= ((((sk_A) = (k1_xboole_0))))),
% 0.81/1.04      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.81/1.04  thf('72', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.81/1.04      inference('demod', [status(thm)], ['62', '71'])).
% 0.81/1.04  thf('73', plain,
% 0.81/1.04      (~ (((sk_B_2) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.81/1.04      inference('split', [status(esa)], ['35'])).
% 0.81/1.04  thf('74', plain, (~ (((sk_B_2) = (k1_xboole_0)))),
% 0.81/1.04      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.81/1.04  thf('75', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.81/1.04      inference('simpl_trail', [status(thm)], ['36', '74'])).
% 0.81/1.04  thf('76', plain,
% 0.81/1.04      (![X0 : $i]:
% 0.81/1.04         (((X0) != (k1_xboole_0))
% 0.81/1.04          | ~ (v1_xboole_0 @ X0)
% 0.81/1.04          | ~ (v1_xboole_0 @ sk_B_2))),
% 0.81/1.04      inference('sup-', [status(thm)], ['34', '75'])).
% 0.81/1.04  thf('77', plain,
% 0.81/1.04      ((~ (v1_xboole_0 @ sk_B_2) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.81/1.04      inference('simplify', [status(thm)], ['76'])).
% 0.81/1.04  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.81/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.81/1.04  thf('79', plain, (~ (v1_xboole_0 @ sk_B_2)),
% 0.81/1.04      inference('simplify_reflect+', [status(thm)], ['77', '78'])).
% 0.81/1.04  thf('80', plain, (((sk_C_1) = (sk_D))),
% 0.81/1.04      inference('clc', [status(thm)], ['24', '79'])).
% 0.81/1.04  thf('81', plain, ((r2_relset_1 @ sk_A @ sk_B_2 @ sk_C_1 @ sk_C_1)),
% 0.81/1.04      inference('sup-', [status(thm)], ['64', '66'])).
% 0.81/1.04  thf('82', plain, ($false),
% 0.81/1.04      inference('demod', [status(thm)], ['0', '80', '81'])).
% 0.81/1.04  
% 0.81/1.04  % SZS output end Refutation
% 0.81/1.04  
% 0.81/1.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
