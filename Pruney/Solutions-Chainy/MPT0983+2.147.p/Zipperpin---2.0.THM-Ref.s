%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0qEr367DhN

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:24 EST 2020

% Result     : Theorem 9.93s
% Output     : Refutation 9.93s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 992 expanded)
%              Number of leaves         :   47 ( 299 expanded)
%              Depth                    :   24
%              Number of atoms          : 1426 (19613 expanded)
%              Number of equality atoms :   58 ( 228 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('1',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['1','2'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('5',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('6',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','7'])).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('9',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('14',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('24',plain,(
    v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('27',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( ( k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41 )
        = ( k5_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['24','33'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) ) @ ( k2_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['38','43','48'])).

thf('50',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('53',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('54',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('55',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('58',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('60',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('61',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('62',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('65',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('67',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('68',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('69',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('76',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('78',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('79',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['55','66','69','76','77','78'])).

thf('80',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('81',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('84',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ X29 )
       != X28 )
      | ( v2_funct_2 @ X29 @ X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('85',plain,(
    ! [X29: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ~ ( v5_relat_1 @ X29 @ ( k2_relat_1 @ X29 ) )
      | ( v2_funct_2 @ X29 @ ( k2_relat_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['79','87'])).

thf('89',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('90',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('92',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('94',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['11','94'])).

thf('96',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('97',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('98',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('102',plain,(
    ! [X44: $i] :
      ( ( k6_partfun1 @ X44 )
      = ( k6_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('103',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('106',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['104','105'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('107',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('110',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('112',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('113',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('114',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('115',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['100','103','110','111','112','113','114'])).

thf('116',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('117',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('118',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45 ) )
      | ( v2_funct_1 @ X49 )
      | ( X47 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X48 @ X46 )
      | ~ ( v1_funct_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['116','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['123','124','125','126'])).

thf('128',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('129',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('130',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('132',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['92','93'])).

thf('134',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['115','134'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('136',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('137',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('138',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('139',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('140',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['137','138','139'])).

thf('141',plain,(
    $false ),
    inference(demod,[status(thm)],['95','140'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0qEr367DhN
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 9.93/10.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.93/10.16  % Solved by: fo/fo7.sh
% 9.93/10.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.93/10.16  % done 8233 iterations in 9.671s
% 9.93/10.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.93/10.16  % SZS output start Refutation
% 9.93/10.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.93/10.16  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 9.93/10.16  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 9.93/10.16  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 9.93/10.16  thf(sk_D_type, type, sk_D: $i).
% 9.93/10.16  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 9.93/10.16  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.93/10.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 9.93/10.16  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 9.93/10.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.93/10.16  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 9.93/10.16  thf(sk_C_type, type, sk_C: $i).
% 9.93/10.16  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 9.93/10.16  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 9.93/10.16  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 9.93/10.16  thf(sk_B_type, type, sk_B: $i).
% 9.93/10.16  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 9.93/10.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.93/10.16  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 9.93/10.16  thf(sk_A_type, type, sk_A: $i).
% 9.93/10.16  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 9.93/10.16  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 9.93/10.16  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 9.93/10.16  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 9.93/10.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 9.93/10.16  thf(l13_xboole_0, axiom,
% 9.93/10.16    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 9.93/10.16  thf('0', plain,
% 9.93/10.16      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 9.93/10.16      inference('cnf', [status(esa)], [l13_xboole_0])).
% 9.93/10.16  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 9.93/10.16  thf('1', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.93/10.16      inference('cnf', [status(esa)], [t81_relat_1])).
% 9.93/10.16  thf(redefinition_k6_partfun1, axiom,
% 9.93/10.16    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 9.93/10.16  thf('2', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 9.93/10.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.93/10.16  thf('3', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 9.93/10.16      inference('demod', [status(thm)], ['1', '2'])).
% 9.93/10.16  thf(fc4_funct_1, axiom,
% 9.93/10.16    (![A:$i]:
% 9.93/10.16     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 9.93/10.16       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 9.93/10.16  thf('4', plain, (![X20 : $i]: (v2_funct_1 @ (k6_relat_1 @ X20))),
% 9.93/10.16      inference('cnf', [status(esa)], [fc4_funct_1])).
% 9.93/10.16  thf('5', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 9.93/10.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.93/10.16  thf('6', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 9.93/10.16      inference('demod', [status(thm)], ['4', '5'])).
% 9.93/10.16  thf('7', plain, ((v2_funct_1 @ k1_xboole_0)),
% 9.93/10.16      inference('sup+', [status(thm)], ['3', '6'])).
% 9.93/10.16  thf('8', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 9.93/10.16      inference('sup+', [status(thm)], ['0', '7'])).
% 9.93/10.16  thf(t29_funct_2, conjecture,
% 9.93/10.16    (![A:$i,B:$i,C:$i]:
% 9.93/10.16     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.93/10.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.93/10.16       ( ![D:$i]:
% 9.93/10.16         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 9.93/10.16             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 9.93/10.16           ( ( r2_relset_1 @
% 9.93/10.16               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 9.93/10.16               ( k6_partfun1 @ A ) ) =>
% 9.93/10.16             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 9.93/10.16  thf(zf_stmt_0, negated_conjecture,
% 9.93/10.16    (~( ![A:$i,B:$i,C:$i]:
% 9.93/10.16        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 9.93/10.16            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.93/10.16          ( ![D:$i]:
% 9.93/10.16            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 9.93/10.16                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 9.93/10.16              ( ( r2_relset_1 @
% 9.93/10.16                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 9.93/10.16                  ( k6_partfun1 @ A ) ) =>
% 9.93/10.16                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 9.93/10.16    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 9.93/10.16  thf('9', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('10', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 9.93/10.16      inference('split', [status(esa)], ['9'])).
% 9.93/10.16  thf('11', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 9.93/10.16      inference('sup-', [status(thm)], ['8', '10'])).
% 9.93/10.16  thf('12', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('13', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf(dt_k1_partfun1, axiom,
% 9.93/10.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.93/10.16     ( ( ( v1_funct_1 @ E ) & 
% 9.93/10.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.93/10.16         ( v1_funct_1 @ F ) & 
% 9.93/10.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.93/10.16       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 9.93/10.16         ( m1_subset_1 @
% 9.93/10.16           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 9.93/10.16           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 9.93/10.16  thf('14', plain,
% 9.93/10.16      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 9.93/10.16         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 9.93/10.16          | ~ (v1_funct_1 @ X30)
% 9.93/10.16          | ~ (v1_funct_1 @ X33)
% 9.93/10.16          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 9.93/10.16          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 9.93/10.16             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 9.93/10.16      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 9.93/10.16  thf('15', plain,
% 9.93/10.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.93/10.16         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 9.93/10.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.93/10.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.93/10.16          | ~ (v1_funct_1 @ X1)
% 9.93/10.16          | ~ (v1_funct_1 @ sk_C))),
% 9.93/10.16      inference('sup-', [status(thm)], ['13', '14'])).
% 9.93/10.16  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('17', plain,
% 9.93/10.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.93/10.16         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 9.93/10.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 9.93/10.16          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 9.93/10.16          | ~ (v1_funct_1 @ X1))),
% 9.93/10.16      inference('demod', [status(thm)], ['15', '16'])).
% 9.93/10.16  thf('18', plain,
% 9.93/10.16      ((~ (v1_funct_1 @ sk_D)
% 9.93/10.16        | (m1_subset_1 @ 
% 9.93/10.16           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 9.93/10.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.93/10.16      inference('sup-', [status(thm)], ['12', '17'])).
% 9.93/10.16  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('20', plain,
% 9.93/10.16      ((m1_subset_1 @ 
% 9.93/10.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 9.93/10.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.93/10.16      inference('demod', [status(thm)], ['18', '19'])).
% 9.93/10.16  thf(cc2_relat_1, axiom,
% 9.93/10.16    (![A:$i]:
% 9.93/10.16     ( ( v1_relat_1 @ A ) =>
% 9.93/10.16       ( ![B:$i]:
% 9.93/10.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 9.93/10.16  thf('21', plain,
% 9.93/10.16      (![X4 : $i, X5 : $i]:
% 9.93/10.16         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 9.93/10.16          | (v1_relat_1 @ X4)
% 9.93/10.16          | ~ (v1_relat_1 @ X5))),
% 9.93/10.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.93/10.16  thf('22', plain,
% 9.93/10.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 9.93/10.16        | (v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 9.93/10.16      inference('sup-', [status(thm)], ['20', '21'])).
% 9.93/10.16  thf(fc6_relat_1, axiom,
% 9.93/10.16    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 9.93/10.16  thf('23', plain,
% 9.93/10.16      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 9.93/10.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.93/10.16  thf('24', plain,
% 9.93/10.16      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['22', '23'])).
% 9.93/10.16  thf('25', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('26', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf(redefinition_k1_partfun1, axiom,
% 9.93/10.16    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 9.93/10.16     ( ( ( v1_funct_1 @ E ) & 
% 9.93/10.16         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.93/10.16         ( v1_funct_1 @ F ) & 
% 9.93/10.16         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 9.93/10.16       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 9.93/10.16  thf('27', plain,
% 9.93/10.16      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 9.93/10.16         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 9.93/10.16          | ~ (v1_funct_1 @ X38)
% 9.93/10.16          | ~ (v1_funct_1 @ X41)
% 9.93/10.16          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 9.93/10.16          | ((k1_partfun1 @ X39 @ X40 @ X42 @ X43 @ X38 @ X41)
% 9.93/10.16              = (k5_relat_1 @ X38 @ X41)))),
% 9.93/10.16      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 9.93/10.16  thf('28', plain,
% 9.93/10.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.93/10.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 9.93/10.16            = (k5_relat_1 @ sk_C @ X0))
% 9.93/10.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.93/10.16          | ~ (v1_funct_1 @ X0)
% 9.93/10.16          | ~ (v1_funct_1 @ sk_C))),
% 9.93/10.16      inference('sup-', [status(thm)], ['26', '27'])).
% 9.93/10.16  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('30', plain,
% 9.93/10.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.93/10.16         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 9.93/10.16            = (k5_relat_1 @ sk_C @ X0))
% 9.93/10.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 9.93/10.16          | ~ (v1_funct_1 @ X0))),
% 9.93/10.16      inference('demod', [status(thm)], ['28', '29'])).
% 9.93/10.16  thf('31', plain,
% 9.93/10.16      ((~ (v1_funct_1 @ sk_D)
% 9.93/10.16        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 9.93/10.16            = (k5_relat_1 @ sk_C @ sk_D)))),
% 9.93/10.16      inference('sup-', [status(thm)], ['25', '30'])).
% 9.93/10.16  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('33', plain,
% 9.93/10.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 9.93/10.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['31', '32'])).
% 9.93/10.16  thf('34', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['24', '33'])).
% 9.93/10.16  thf(t45_relat_1, axiom,
% 9.93/10.16    (![A:$i]:
% 9.93/10.16     ( ( v1_relat_1 @ A ) =>
% 9.93/10.16       ( ![B:$i]:
% 9.93/10.16         ( ( v1_relat_1 @ B ) =>
% 9.93/10.16           ( r1_tarski @
% 9.93/10.16             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 9.93/10.16  thf('35', plain,
% 9.93/10.16      (![X15 : $i, X16 : $i]:
% 9.93/10.16         (~ (v1_relat_1 @ X15)
% 9.93/10.16          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X16 @ X15)) @ 
% 9.93/10.16             (k2_relat_1 @ X15))
% 9.93/10.16          | ~ (v1_relat_1 @ X16))),
% 9.93/10.16      inference('cnf', [status(esa)], [t45_relat_1])).
% 9.93/10.16  thf(d19_relat_1, axiom,
% 9.93/10.16    (![A:$i,B:$i]:
% 9.93/10.16     ( ( v1_relat_1 @ B ) =>
% 9.93/10.16       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 9.93/10.16  thf('36', plain,
% 9.93/10.16      (![X8 : $i, X9 : $i]:
% 9.93/10.16         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 9.93/10.16          | (v5_relat_1 @ X8 @ X9)
% 9.93/10.16          | ~ (v1_relat_1 @ X8))),
% 9.93/10.16      inference('cnf', [status(esa)], [d19_relat_1])).
% 9.93/10.16  thf('37', plain,
% 9.93/10.16      (![X0 : $i, X1 : $i]:
% 9.93/10.16         (~ (v1_relat_1 @ X1)
% 9.93/10.16          | ~ (v1_relat_1 @ X0)
% 9.93/10.16          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 9.93/10.16          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 9.93/10.16      inference('sup-', [status(thm)], ['35', '36'])).
% 9.93/10.16  thf('38', plain,
% 9.93/10.16      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 9.93/10.16        | ~ (v1_relat_1 @ sk_D)
% 9.93/10.16        | ~ (v1_relat_1 @ sk_C))),
% 9.93/10.16      inference('sup-', [status(thm)], ['34', '37'])).
% 9.93/10.16  thf('39', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('40', plain,
% 9.93/10.16      (![X4 : $i, X5 : $i]:
% 9.93/10.16         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 9.93/10.16          | (v1_relat_1 @ X4)
% 9.93/10.16          | ~ (v1_relat_1 @ X5))),
% 9.93/10.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.93/10.16  thf('41', plain,
% 9.93/10.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 9.93/10.16      inference('sup-', [status(thm)], ['39', '40'])).
% 9.93/10.16  thf('42', plain,
% 9.93/10.16      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 9.93/10.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.93/10.16  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 9.93/10.16      inference('demod', [status(thm)], ['41', '42'])).
% 9.93/10.16  thf('44', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('45', plain,
% 9.93/10.16      (![X4 : $i, X5 : $i]:
% 9.93/10.16         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 9.93/10.16          | (v1_relat_1 @ X4)
% 9.93/10.16          | ~ (v1_relat_1 @ X5))),
% 9.93/10.16      inference('cnf', [status(esa)], [cc2_relat_1])).
% 9.93/10.16  thf('46', plain,
% 9.93/10.16      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 9.93/10.16      inference('sup-', [status(thm)], ['44', '45'])).
% 9.93/10.16  thf('47', plain,
% 9.93/10.16      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 9.93/10.16      inference('cnf', [status(esa)], [fc6_relat_1])).
% 9.93/10.16  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 9.93/10.16      inference('demod', [status(thm)], ['46', '47'])).
% 9.93/10.16  thf('49', plain,
% 9.93/10.16      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['38', '43', '48'])).
% 9.93/10.16  thf('50', plain,
% 9.93/10.16      (![X8 : $i, X9 : $i]:
% 9.93/10.16         (~ (v5_relat_1 @ X8 @ X9)
% 9.93/10.16          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 9.93/10.16          | ~ (v1_relat_1 @ X8))),
% 9.93/10.16      inference('cnf', [status(esa)], [d19_relat_1])).
% 9.93/10.16  thf('51', plain,
% 9.93/10.16      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 9.93/10.16        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 9.93/10.16           (k2_relat_1 @ sk_D)))),
% 9.93/10.16      inference('sup-', [status(thm)], ['49', '50'])).
% 9.93/10.16  thf('52', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['24', '33'])).
% 9.93/10.16  thf('53', plain,
% 9.93/10.16      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 9.93/10.16        (k2_relat_1 @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['51', '52'])).
% 9.93/10.16  thf(d10_xboole_0, axiom,
% 9.93/10.16    (![A:$i,B:$i]:
% 9.93/10.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 9.93/10.16  thf('54', plain,
% 9.93/10.16      (![X1 : $i, X3 : $i]:
% 9.93/10.16         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 9.93/10.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.93/10.16  thf('55', plain,
% 9.93/10.16      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 9.93/10.16           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 9.93/10.16        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 9.93/10.16      inference('sup-', [status(thm)], ['53', '54'])).
% 9.93/10.16  thf('56', plain,
% 9.93/10.16      ((r2_relset_1 @ sk_A @ sk_A @ 
% 9.93/10.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 9.93/10.16        (k6_partfun1 @ sk_A))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('57', plain,
% 9.93/10.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 9.93/10.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['31', '32'])).
% 9.93/10.16  thf('58', plain,
% 9.93/10.16      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 9.93/10.16        (k6_partfun1 @ sk_A))),
% 9.93/10.16      inference('demod', [status(thm)], ['56', '57'])).
% 9.93/10.16  thf('59', plain,
% 9.93/10.16      ((m1_subset_1 @ 
% 9.93/10.16        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 9.93/10.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.93/10.16      inference('demod', [status(thm)], ['18', '19'])).
% 9.93/10.16  thf('60', plain,
% 9.93/10.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 9.93/10.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['31', '32'])).
% 9.93/10.16  thf('61', plain,
% 9.93/10.16      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 9.93/10.16        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 9.93/10.16      inference('demod', [status(thm)], ['59', '60'])).
% 9.93/10.16  thf(redefinition_r2_relset_1, axiom,
% 9.93/10.16    (![A:$i,B:$i,C:$i,D:$i]:
% 9.93/10.16     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 9.93/10.16         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.93/10.16       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 9.93/10.16  thf('62', plain,
% 9.93/10.16      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 9.93/10.16         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 9.93/10.16          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 9.93/10.16          | ((X24) = (X27))
% 9.93/10.16          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 9.93/10.16      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 9.93/10.16  thf('63', plain,
% 9.93/10.16      (![X0 : $i]:
% 9.93/10.16         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 9.93/10.16          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 9.93/10.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 9.93/10.16      inference('sup-', [status(thm)], ['61', '62'])).
% 9.93/10.16  thf('64', plain,
% 9.93/10.16      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 9.93/10.16           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 9.93/10.16        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 9.93/10.16      inference('sup-', [status(thm)], ['58', '63'])).
% 9.93/10.16  thf(dt_k6_partfun1, axiom,
% 9.93/10.16    (![A:$i]:
% 9.93/10.16     ( ( m1_subset_1 @
% 9.93/10.16         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 9.93/10.16       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 9.93/10.16  thf('65', plain,
% 9.93/10.16      (![X37 : $i]:
% 9.93/10.16         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 9.93/10.16          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 9.93/10.16      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 9.93/10.16  thf('66', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 9.93/10.16      inference('demod', [status(thm)], ['64', '65'])).
% 9.93/10.16  thf(t71_relat_1, axiom,
% 9.93/10.16    (![A:$i]:
% 9.93/10.16     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 9.93/10.16       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 9.93/10.16  thf('67', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 9.93/10.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.93/10.16  thf('68', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 9.93/10.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.93/10.16  thf('69', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 9.93/10.16      inference('demod', [status(thm)], ['67', '68'])).
% 9.93/10.16  thf('70', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf(cc2_relset_1, axiom,
% 9.93/10.16    (![A:$i,B:$i,C:$i]:
% 9.93/10.16     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 9.93/10.16       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 9.93/10.16  thf('71', plain,
% 9.93/10.16      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.93/10.16         ((v5_relat_1 @ X21 @ X23)
% 9.93/10.16          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 9.93/10.16      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.93/10.16  thf('72', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 9.93/10.16      inference('sup-', [status(thm)], ['70', '71'])).
% 9.93/10.16  thf('73', plain,
% 9.93/10.16      (![X8 : $i, X9 : $i]:
% 9.93/10.16         (~ (v5_relat_1 @ X8 @ X9)
% 9.93/10.16          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 9.93/10.16          | ~ (v1_relat_1 @ X8))),
% 9.93/10.16      inference('cnf', [status(esa)], [d19_relat_1])).
% 9.93/10.16  thf('74', plain,
% 9.93/10.16      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 9.93/10.16      inference('sup-', [status(thm)], ['72', '73'])).
% 9.93/10.16  thf('75', plain, ((v1_relat_1 @ sk_D)),
% 9.93/10.16      inference('demod', [status(thm)], ['41', '42'])).
% 9.93/10.16  thf('76', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 9.93/10.16      inference('demod', [status(thm)], ['74', '75'])).
% 9.93/10.16  thf('77', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 9.93/10.16      inference('demod', [status(thm)], ['64', '65'])).
% 9.93/10.16  thf('78', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 9.93/10.16      inference('demod', [status(thm)], ['67', '68'])).
% 9.93/10.16  thf('79', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 9.93/10.16      inference('demod', [status(thm)], ['55', '66', '69', '76', '77', '78'])).
% 9.93/10.16  thf('80', plain,
% 9.93/10.16      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 9.93/10.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.93/10.16  thf('81', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 9.93/10.16      inference('simplify', [status(thm)], ['80'])).
% 9.93/10.16  thf('82', plain,
% 9.93/10.16      (![X8 : $i, X9 : $i]:
% 9.93/10.16         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 9.93/10.16          | (v5_relat_1 @ X8 @ X9)
% 9.93/10.16          | ~ (v1_relat_1 @ X8))),
% 9.93/10.16      inference('cnf', [status(esa)], [d19_relat_1])).
% 9.93/10.16  thf('83', plain,
% 9.93/10.16      (![X0 : $i]:
% 9.93/10.16         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 9.93/10.16      inference('sup-', [status(thm)], ['81', '82'])).
% 9.93/10.16  thf(d3_funct_2, axiom,
% 9.93/10.16    (![A:$i,B:$i]:
% 9.93/10.16     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 9.93/10.16       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 9.93/10.16  thf('84', plain,
% 9.93/10.16      (![X28 : $i, X29 : $i]:
% 9.93/10.16         (((k2_relat_1 @ X29) != (X28))
% 9.93/10.16          | (v2_funct_2 @ X29 @ X28)
% 9.93/10.16          | ~ (v5_relat_1 @ X29 @ X28)
% 9.93/10.16          | ~ (v1_relat_1 @ X29))),
% 9.93/10.16      inference('cnf', [status(esa)], [d3_funct_2])).
% 9.93/10.16  thf('85', plain,
% 9.93/10.16      (![X29 : $i]:
% 9.93/10.16         (~ (v1_relat_1 @ X29)
% 9.93/10.16          | ~ (v5_relat_1 @ X29 @ (k2_relat_1 @ X29))
% 9.93/10.16          | (v2_funct_2 @ X29 @ (k2_relat_1 @ X29)))),
% 9.93/10.16      inference('simplify', [status(thm)], ['84'])).
% 9.93/10.16  thf('86', plain,
% 9.93/10.16      (![X0 : $i]:
% 9.93/10.16         (~ (v1_relat_1 @ X0)
% 9.93/10.16          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 9.93/10.16          | ~ (v1_relat_1 @ X0))),
% 9.93/10.16      inference('sup-', [status(thm)], ['83', '85'])).
% 9.93/10.16  thf('87', plain,
% 9.93/10.16      (![X0 : $i]:
% 9.93/10.16         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 9.93/10.16      inference('simplify', [status(thm)], ['86'])).
% 9.93/10.16  thf('88', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 9.93/10.16      inference('sup+', [status(thm)], ['79', '87'])).
% 9.93/10.16  thf('89', plain, ((v1_relat_1 @ sk_D)),
% 9.93/10.16      inference('demod', [status(thm)], ['41', '42'])).
% 9.93/10.16  thf('90', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 9.93/10.16      inference('demod', [status(thm)], ['88', '89'])).
% 9.93/10.16  thf('91', plain,
% 9.93/10.16      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 9.93/10.16      inference('split', [status(esa)], ['9'])).
% 9.93/10.16  thf('92', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 9.93/10.16      inference('sup-', [status(thm)], ['90', '91'])).
% 9.93/10.16  thf('93', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 9.93/10.16      inference('split', [status(esa)], ['9'])).
% 9.93/10.16  thf('94', plain, (~ ((v2_funct_1 @ sk_C))),
% 9.93/10.16      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 9.93/10.16  thf('95', plain, (~ (v1_xboole_0 @ sk_C)),
% 9.93/10.16      inference('simpl_trail', [status(thm)], ['11', '94'])).
% 9.93/10.16  thf('96', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 9.93/10.16      inference('demod', [status(thm)], ['64', '65'])).
% 9.93/10.16  thf(t44_relat_1, axiom,
% 9.93/10.16    (![A:$i]:
% 9.93/10.16     ( ( v1_relat_1 @ A ) =>
% 9.93/10.16       ( ![B:$i]:
% 9.93/10.16         ( ( v1_relat_1 @ B ) =>
% 9.93/10.16           ( r1_tarski @
% 9.93/10.16             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 9.93/10.16  thf('97', plain,
% 9.93/10.16      (![X13 : $i, X14 : $i]:
% 9.93/10.16         (~ (v1_relat_1 @ X13)
% 9.93/10.16          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 9.93/10.16             (k1_relat_1 @ X14))
% 9.93/10.16          | ~ (v1_relat_1 @ X14))),
% 9.93/10.16      inference('cnf', [status(esa)], [t44_relat_1])).
% 9.93/10.16  thf('98', plain,
% 9.93/10.16      (![X1 : $i, X3 : $i]:
% 9.93/10.16         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 9.93/10.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 9.93/10.16  thf('99', plain,
% 9.93/10.16      (![X0 : $i, X1 : $i]:
% 9.93/10.16         (~ (v1_relat_1 @ X0)
% 9.93/10.16          | ~ (v1_relat_1 @ X1)
% 9.93/10.16          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 9.93/10.16               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 9.93/10.16          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 9.93/10.16      inference('sup-', [status(thm)], ['97', '98'])).
% 9.93/10.16  thf('100', plain,
% 9.93/10.16      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 9.93/10.16           (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 9.93/10.16        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 9.93/10.16        | ~ (v1_relat_1 @ sk_D)
% 9.93/10.16        | ~ (v1_relat_1 @ sk_C))),
% 9.93/10.16      inference('sup-', [status(thm)], ['96', '99'])).
% 9.93/10.16  thf('101', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 9.93/10.16      inference('cnf', [status(esa)], [t71_relat_1])).
% 9.93/10.16  thf('102', plain, (![X44 : $i]: ((k6_partfun1 @ X44) = (k6_relat_1 @ X44))),
% 9.93/10.16      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 9.93/10.16  thf('103', plain,
% 9.93/10.16      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 9.93/10.16      inference('demod', [status(thm)], ['101', '102'])).
% 9.93/10.16  thf('104', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('105', plain,
% 9.93/10.16      (![X21 : $i, X22 : $i, X23 : $i]:
% 9.93/10.16         ((v4_relat_1 @ X21 @ X22)
% 9.93/10.16          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 9.93/10.16      inference('cnf', [status(esa)], [cc2_relset_1])).
% 9.93/10.16  thf('106', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 9.93/10.16      inference('sup-', [status(thm)], ['104', '105'])).
% 9.93/10.16  thf(d18_relat_1, axiom,
% 9.93/10.16    (![A:$i,B:$i]:
% 9.93/10.16     ( ( v1_relat_1 @ B ) =>
% 9.93/10.16       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 9.93/10.16  thf('107', plain,
% 9.93/10.16      (![X6 : $i, X7 : $i]:
% 9.93/10.16         (~ (v4_relat_1 @ X6 @ X7)
% 9.93/10.16          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 9.93/10.16          | ~ (v1_relat_1 @ X6))),
% 9.93/10.16      inference('cnf', [status(esa)], [d18_relat_1])).
% 9.93/10.16  thf('108', plain,
% 9.93/10.16      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 9.93/10.16      inference('sup-', [status(thm)], ['106', '107'])).
% 9.93/10.16  thf('109', plain, ((v1_relat_1 @ sk_C)),
% 9.93/10.16      inference('demod', [status(thm)], ['46', '47'])).
% 9.93/10.16  thf('110', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 9.93/10.16      inference('demod', [status(thm)], ['108', '109'])).
% 9.93/10.16  thf('111', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 9.93/10.16      inference('demod', [status(thm)], ['64', '65'])).
% 9.93/10.16  thf('112', plain,
% 9.93/10.16      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 9.93/10.16      inference('demod', [status(thm)], ['101', '102'])).
% 9.93/10.16  thf('113', plain, ((v1_relat_1 @ sk_D)),
% 9.93/10.16      inference('demod', [status(thm)], ['41', '42'])).
% 9.93/10.16  thf('114', plain, ((v1_relat_1 @ sk_C)),
% 9.93/10.16      inference('demod', [status(thm)], ['46', '47'])).
% 9.93/10.16  thf('115', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 9.93/10.16      inference('demod', [status(thm)],
% 9.93/10.16                ['100', '103', '110', '111', '112', '113', '114'])).
% 9.93/10.16  thf('116', plain,
% 9.93/10.16      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 9.93/10.16         = (k5_relat_1 @ sk_C @ sk_D))),
% 9.93/10.16      inference('demod', [status(thm)], ['31', '32'])).
% 9.93/10.16  thf('117', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf(t26_funct_2, axiom,
% 9.93/10.16    (![A:$i,B:$i,C:$i,D:$i]:
% 9.93/10.16     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 9.93/10.16         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 9.93/10.16       ( ![E:$i]:
% 9.93/10.16         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 9.93/10.16             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 9.93/10.16           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 9.93/10.16             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 9.93/10.16               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 9.93/10.16  thf('118', plain,
% 9.93/10.16      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 9.93/10.16         (~ (v1_funct_1 @ X45)
% 9.93/10.16          | ~ (v1_funct_2 @ X45 @ X46 @ X47)
% 9.93/10.16          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 9.93/10.16          | ~ (v2_funct_1 @ (k1_partfun1 @ X48 @ X46 @ X46 @ X47 @ X49 @ X45))
% 9.93/10.16          | (v2_funct_1 @ X49)
% 9.93/10.16          | ((X47) = (k1_xboole_0))
% 9.93/10.16          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X46)))
% 9.93/10.16          | ~ (v1_funct_2 @ X49 @ X48 @ X46)
% 9.93/10.16          | ~ (v1_funct_1 @ X49))),
% 9.93/10.16      inference('cnf', [status(esa)], [t26_funct_2])).
% 9.93/10.16  thf('119', plain,
% 9.93/10.16      (![X0 : $i, X1 : $i]:
% 9.93/10.16         (~ (v1_funct_1 @ X0)
% 9.93/10.16          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 9.93/10.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 9.93/10.16          | ((sk_A) = (k1_xboole_0))
% 9.93/10.16          | (v2_funct_1 @ X0)
% 9.93/10.16          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 9.93/10.16          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 9.93/10.16          | ~ (v1_funct_1 @ sk_D))),
% 9.93/10.16      inference('sup-', [status(thm)], ['117', '118'])).
% 9.93/10.16  thf('120', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('121', plain, ((v1_funct_1 @ sk_D)),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('122', plain,
% 9.93/10.16      (![X0 : $i, X1 : $i]:
% 9.93/10.16         (~ (v1_funct_1 @ X0)
% 9.93/10.16          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 9.93/10.16          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 9.93/10.16          | ((sk_A) = (k1_xboole_0))
% 9.93/10.16          | (v2_funct_1 @ X0)
% 9.93/10.16          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 9.93/10.16      inference('demod', [status(thm)], ['119', '120', '121'])).
% 9.93/10.16  thf('123', plain,
% 9.93/10.16      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 9.93/10.16        | (v2_funct_1 @ sk_C)
% 9.93/10.16        | ((sk_A) = (k1_xboole_0))
% 9.93/10.16        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 9.93/10.16        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 9.93/10.16        | ~ (v1_funct_1 @ sk_C))),
% 9.93/10.16      inference('sup-', [status(thm)], ['116', '122'])).
% 9.93/10.16  thf('124', plain,
% 9.93/10.16      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('125', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('126', plain, ((v1_funct_1 @ sk_C)),
% 9.93/10.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.93/10.16  thf('127', plain,
% 9.93/10.16      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 9.93/10.16        | (v2_funct_1 @ sk_C)
% 9.93/10.16        | ((sk_A) = (k1_xboole_0)))),
% 9.93/10.16      inference('demod', [status(thm)], ['123', '124', '125', '126'])).
% 9.93/10.16  thf('128', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 9.93/10.16      inference('demod', [status(thm)], ['64', '65'])).
% 9.93/10.16  thf('129', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 9.93/10.16      inference('demod', [status(thm)], ['4', '5'])).
% 9.93/10.16  thf('130', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 9.93/10.16      inference('demod', [status(thm)], ['127', '128', '129'])).
% 9.93/10.16  thf('131', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 9.93/10.16      inference('split', [status(esa)], ['9'])).
% 9.93/10.16  thf('132', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 9.93/10.16      inference('sup-', [status(thm)], ['130', '131'])).
% 9.93/10.16  thf('133', plain, (~ ((v2_funct_1 @ sk_C))),
% 9.93/10.16      inference('sat_resolution*', [status(thm)], ['92', '93'])).
% 9.93/10.16  thf('134', plain, (((sk_A) = (k1_xboole_0))),
% 9.93/10.16      inference('simpl_trail', [status(thm)], ['132', '133'])).
% 9.93/10.16  thf('135', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 9.93/10.16      inference('demod', [status(thm)], ['115', '134'])).
% 9.93/10.16  thf(fc8_relat_1, axiom,
% 9.93/10.16    (![A:$i]:
% 9.93/10.16     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 9.93/10.16       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 9.93/10.16  thf('136', plain,
% 9.93/10.16      (![X12 : $i]:
% 9.93/10.16         (~ (v1_xboole_0 @ (k1_relat_1 @ X12))
% 9.93/10.16          | ~ (v1_relat_1 @ X12)
% 9.93/10.16          | (v1_xboole_0 @ X12))),
% 9.93/10.16      inference('cnf', [status(esa)], [fc8_relat_1])).
% 9.93/10.16  thf('137', plain,
% 9.93/10.16      ((~ (v1_xboole_0 @ k1_xboole_0)
% 9.93/10.16        | (v1_xboole_0 @ sk_C)
% 9.93/10.16        | ~ (v1_relat_1 @ sk_C))),
% 9.93/10.16      inference('sup-', [status(thm)], ['135', '136'])).
% 9.93/10.16  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 9.93/10.16  thf('138', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 9.93/10.16      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 9.93/10.16  thf('139', plain, ((v1_relat_1 @ sk_C)),
% 9.93/10.16      inference('demod', [status(thm)], ['46', '47'])).
% 9.93/10.16  thf('140', plain, ((v1_xboole_0 @ sk_C)),
% 9.93/10.16      inference('demod', [status(thm)], ['137', '138', '139'])).
% 9.93/10.16  thf('141', plain, ($false), inference('demod', [status(thm)], ['95', '140'])).
% 9.93/10.16  
% 9.93/10.16  % SZS output end Refutation
% 9.93/10.16  
% 9.93/10.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
