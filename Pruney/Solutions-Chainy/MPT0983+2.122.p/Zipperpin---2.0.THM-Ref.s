%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g1CKoZqoTe

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:20 EST 2020

% Result     : Theorem 3.30s
% Output     : Refutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 816 expanded)
%              Number of leaves         :   45 ( 248 expanded)
%              Depth                    :   23
%              Number of atoms          : 1303 (15816 expanded)
%              Number of equality atoms :   53 ( 191 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
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
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X36 ) ) ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 )
        = ( k5_relat_1 @ X37 @ X40 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( v5_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['38','43','48'])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('65',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('66',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('67',plain,(
    ! [X28: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X28 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('69',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X18 ) )
      = X18 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('70',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('71',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('73',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('78',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('80',plain,(
    ! [X18: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X18 ) )
      = X18 ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('81',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['55','68','71','78','79','80'])).

thf('82',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('83',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( v5_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('86',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k2_relat_1 @ X30 )
       != X29 )
      | ( v2_funct_2 @ X30 @ X29 )
      | ~ ( v5_relat_1 @ X30 @ X29 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('87',plain,(
    ! [X30: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v5_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
      | ( v2_funct_2 @ X30 @ ( k2_relat_1 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_funct_2 @ X0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['81','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('92',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('94',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['9'])).

thf('96',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('97',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['11','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('99',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('100',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('102',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('103',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
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

thf('105',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44 ) )
      | ( v2_funct_1 @ X48 )
      | ( X46 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['106','107','108'])).

thf('110',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','109'])).

thf('111',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('112',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['110','111','112','113','114'])).

thf('116',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('117',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('118',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['116','117'])).

thf('119',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['115','118'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('120',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('121',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['120'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['100','119','121','122'])).

thf('124',plain,(
    $false ),
    inference(demod,[status(thm)],['97','123'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g1CKoZqoTe
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.30/3.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.30/3.48  % Solved by: fo/fo7.sh
% 3.30/3.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.30/3.48  % done 3069 iterations in 2.994s
% 3.30/3.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.30/3.48  % SZS output start Refutation
% 3.30/3.48  thf(sk_B_type, type, sk_B: $i).
% 3.30/3.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.30/3.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 3.30/3.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.30/3.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.30/3.48  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.30/3.48  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.30/3.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.30/3.48  thf(sk_D_type, type, sk_D: $i).
% 3.30/3.48  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.30/3.48  thf(sk_A_type, type, sk_A: $i).
% 3.30/3.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.30/3.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.30/3.48  thf(sk_C_type, type, sk_C: $i).
% 3.30/3.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.30/3.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.30/3.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.30/3.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.30/3.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.30/3.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.30/3.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.30/3.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.30/3.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.30/3.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.30/3.48  thf(l13_xboole_0, axiom,
% 3.30/3.48    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.30/3.48  thf('0', plain,
% 3.30/3.48      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.30/3.48      inference('cnf', [status(esa)], [l13_xboole_0])).
% 3.30/3.48  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.30/3.48  thf('1', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.30/3.48      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.30/3.48  thf(redefinition_k6_partfun1, axiom,
% 3.30/3.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.30/3.48  thf('2', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.30/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.30/3.48  thf('3', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.30/3.48      inference('demod', [status(thm)], ['1', '2'])).
% 3.30/3.48  thf(fc4_funct_1, axiom,
% 3.30/3.48    (![A:$i]:
% 3.30/3.48     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.30/3.48       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.30/3.48  thf('4', plain, (![X20 : $i]: (v2_funct_1 @ (k6_relat_1 @ X20))),
% 3.30/3.48      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.30/3.48  thf('5', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.30/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.30/3.48  thf('6', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 3.30/3.48      inference('demod', [status(thm)], ['4', '5'])).
% 3.30/3.48  thf('7', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.30/3.48      inference('sup+', [status(thm)], ['3', '6'])).
% 3.30/3.48  thf('8', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.30/3.48      inference('sup+', [status(thm)], ['0', '7'])).
% 3.30/3.48  thf(t29_funct_2, conjecture,
% 3.30/3.48    (![A:$i,B:$i,C:$i]:
% 3.30/3.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.30/3.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.48       ( ![D:$i]:
% 3.30/3.48         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.30/3.48             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.30/3.48           ( ( r2_relset_1 @
% 3.30/3.48               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.30/3.48               ( k6_partfun1 @ A ) ) =>
% 3.30/3.48             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.30/3.48  thf(zf_stmt_0, negated_conjecture,
% 3.30/3.48    (~( ![A:$i,B:$i,C:$i]:
% 3.30/3.48        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.30/3.48            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.48          ( ![D:$i]:
% 3.30/3.48            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.30/3.48                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.30/3.48              ( ( r2_relset_1 @
% 3.30/3.48                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.30/3.48                  ( k6_partfun1 @ A ) ) =>
% 3.30/3.48                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.30/3.48    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.30/3.48  thf('9', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('10', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.30/3.48      inference('split', [status(esa)], ['9'])).
% 3.30/3.48  thf('11', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.30/3.48      inference('sup-', [status(thm)], ['8', '10'])).
% 3.30/3.48  thf('12', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('13', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf(dt_k1_partfun1, axiom,
% 3.30/3.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.30/3.48     ( ( ( v1_funct_1 @ E ) & 
% 3.30/3.48         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.30/3.48         ( v1_funct_1 @ F ) & 
% 3.30/3.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.30/3.48       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.30/3.48         ( m1_subset_1 @
% 3.30/3.48           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.30/3.48           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.30/3.48  thf('14', plain,
% 3.30/3.48      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.30/3.48         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 3.30/3.48          | ~ (v1_funct_1 @ X31)
% 3.30/3.48          | ~ (v1_funct_1 @ X34)
% 3.30/3.48          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.30/3.48          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 3.30/3.48             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 3.30/3.48      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.30/3.48  thf('15', plain,
% 3.30/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.48         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.30/3.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.30/3.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.30/3.48          | ~ (v1_funct_1 @ X1)
% 3.30/3.48          | ~ (v1_funct_1 @ sk_C))),
% 3.30/3.48      inference('sup-', [status(thm)], ['13', '14'])).
% 3.30/3.48  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('17', plain,
% 3.30/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.48         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 3.30/3.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.30/3.48          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.30/3.48          | ~ (v1_funct_1 @ X1))),
% 3.30/3.48      inference('demod', [status(thm)], ['15', '16'])).
% 3.30/3.48  thf('18', plain,
% 3.30/3.48      ((~ (v1_funct_1 @ sk_D)
% 3.30/3.48        | (m1_subset_1 @ 
% 3.30/3.48           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.30/3.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.30/3.48      inference('sup-', [status(thm)], ['12', '17'])).
% 3.30/3.48  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('20', plain,
% 3.30/3.48      ((m1_subset_1 @ 
% 3.30/3.48        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.30/3.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.30/3.48      inference('demod', [status(thm)], ['18', '19'])).
% 3.30/3.48  thf(cc2_relat_1, axiom,
% 3.30/3.48    (![A:$i]:
% 3.30/3.48     ( ( v1_relat_1 @ A ) =>
% 3.30/3.48       ( ![B:$i]:
% 3.30/3.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 3.30/3.48  thf('21', plain,
% 3.30/3.48      (![X9 : $i, X10 : $i]:
% 3.30/3.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.30/3.48          | (v1_relat_1 @ X9)
% 3.30/3.48          | ~ (v1_relat_1 @ X10))),
% 3.30/3.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.30/3.48  thf('22', plain,
% 3.30/3.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 3.30/3.48        | (v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 3.30/3.48      inference('sup-', [status(thm)], ['20', '21'])).
% 3.30/3.48  thf(fc6_relat_1, axiom,
% 3.30/3.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 3.30/3.48  thf('23', plain,
% 3.30/3.48      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 3.30/3.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.30/3.48  thf('24', plain,
% 3.30/3.48      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['22', '23'])).
% 3.30/3.48  thf('25', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('26', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf(redefinition_k1_partfun1, axiom,
% 3.30/3.48    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.30/3.48     ( ( ( v1_funct_1 @ E ) & 
% 3.30/3.48         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.30/3.48         ( v1_funct_1 @ F ) & 
% 3.30/3.48         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.30/3.48       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 3.30/3.48  thf('27', plain,
% 3.30/3.48      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 3.30/3.48         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 3.30/3.48          | ~ (v1_funct_1 @ X37)
% 3.30/3.48          | ~ (v1_funct_1 @ X40)
% 3.30/3.48          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.30/3.48          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 3.30/3.48              = (k5_relat_1 @ X37 @ X40)))),
% 3.30/3.48      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 3.30/3.48  thf('28', plain,
% 3.30/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.48         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.30/3.48            = (k5_relat_1 @ sk_C @ X0))
% 3.30/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.30/3.48          | ~ (v1_funct_1 @ X0)
% 3.30/3.48          | ~ (v1_funct_1 @ sk_C))),
% 3.30/3.48      inference('sup-', [status(thm)], ['26', '27'])).
% 3.30/3.48  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('30', plain,
% 3.30/3.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.30/3.48         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 3.30/3.48            = (k5_relat_1 @ sk_C @ X0))
% 3.30/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 3.30/3.48          | ~ (v1_funct_1 @ X0))),
% 3.30/3.48      inference('demod', [status(thm)], ['28', '29'])).
% 3.30/3.48  thf('31', plain,
% 3.30/3.48      ((~ (v1_funct_1 @ sk_D)
% 3.30/3.48        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.48            = (k5_relat_1 @ sk_C @ sk_D)))),
% 3.30/3.48      inference('sup-', [status(thm)], ['25', '30'])).
% 3.30/3.48  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('33', plain,
% 3.30/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['31', '32'])).
% 3.30/3.48  thf('34', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['24', '33'])).
% 3.30/3.48  thf(t45_relat_1, axiom,
% 3.30/3.48    (![A:$i]:
% 3.30/3.48     ( ( v1_relat_1 @ A ) =>
% 3.30/3.48       ( ![B:$i]:
% 3.30/3.48         ( ( v1_relat_1 @ B ) =>
% 3.30/3.48           ( r1_tarski @
% 3.30/3.48             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 3.30/3.48  thf('35', plain,
% 3.30/3.48      (![X15 : $i, X16 : $i]:
% 3.30/3.48         (~ (v1_relat_1 @ X15)
% 3.30/3.48          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X16 @ X15)) @ 
% 3.30/3.48             (k2_relat_1 @ X15))
% 3.30/3.48          | ~ (v1_relat_1 @ X16))),
% 3.30/3.48      inference('cnf', [status(esa)], [t45_relat_1])).
% 3.30/3.48  thf(d19_relat_1, axiom,
% 3.30/3.48    (![A:$i,B:$i]:
% 3.30/3.48     ( ( v1_relat_1 @ B ) =>
% 3.30/3.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 3.30/3.48  thf('36', plain,
% 3.30/3.48      (![X11 : $i, X12 : $i]:
% 3.30/3.48         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.30/3.48          | (v5_relat_1 @ X11 @ X12)
% 3.30/3.48          | ~ (v1_relat_1 @ X11))),
% 3.30/3.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.30/3.48  thf('37', plain,
% 3.30/3.48      (![X0 : $i, X1 : $i]:
% 3.30/3.48         (~ (v1_relat_1 @ X1)
% 3.30/3.48          | ~ (v1_relat_1 @ X0)
% 3.30/3.48          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 3.30/3.48          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 3.30/3.48      inference('sup-', [status(thm)], ['35', '36'])).
% 3.30/3.48  thf('38', plain,
% 3.30/3.48      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 3.30/3.48        | ~ (v1_relat_1 @ sk_D)
% 3.30/3.48        | ~ (v1_relat_1 @ sk_C))),
% 3.30/3.48      inference('sup-', [status(thm)], ['34', '37'])).
% 3.30/3.48  thf('39', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('40', plain,
% 3.30/3.48      (![X9 : $i, X10 : $i]:
% 3.30/3.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.30/3.48          | (v1_relat_1 @ X9)
% 3.30/3.48          | ~ (v1_relat_1 @ X10))),
% 3.30/3.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.30/3.48  thf('41', plain,
% 3.30/3.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 3.30/3.48      inference('sup-', [status(thm)], ['39', '40'])).
% 3.30/3.48  thf('42', plain,
% 3.30/3.48      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 3.30/3.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.30/3.48  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 3.30/3.48      inference('demod', [status(thm)], ['41', '42'])).
% 3.30/3.48  thf('44', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('45', plain,
% 3.30/3.48      (![X9 : $i, X10 : $i]:
% 3.30/3.48         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 3.30/3.48          | (v1_relat_1 @ X9)
% 3.30/3.48          | ~ (v1_relat_1 @ X10))),
% 3.30/3.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 3.30/3.48  thf('46', plain,
% 3.30/3.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 3.30/3.48      inference('sup-', [status(thm)], ['44', '45'])).
% 3.30/3.48  thf('47', plain,
% 3.30/3.48      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 3.30/3.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 3.30/3.48  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 3.30/3.48      inference('demod', [status(thm)], ['46', '47'])).
% 3.30/3.48  thf('49', plain,
% 3.30/3.48      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['38', '43', '48'])).
% 3.30/3.48  thf('50', plain,
% 3.30/3.48      (![X11 : $i, X12 : $i]:
% 3.30/3.48         (~ (v5_relat_1 @ X11 @ X12)
% 3.30/3.48          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.30/3.48          | ~ (v1_relat_1 @ X11))),
% 3.30/3.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.30/3.48  thf('51', plain,
% 3.30/3.48      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 3.30/3.48        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 3.30/3.48           (k2_relat_1 @ sk_D)))),
% 3.30/3.48      inference('sup-', [status(thm)], ['49', '50'])).
% 3.30/3.48  thf('52', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['24', '33'])).
% 3.30/3.48  thf('53', plain,
% 3.30/3.48      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 3.30/3.48        (k2_relat_1 @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['51', '52'])).
% 3.30/3.48  thf(d10_xboole_0, axiom,
% 3.30/3.48    (![A:$i,B:$i]:
% 3.30/3.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.30/3.48  thf('54', plain,
% 3.30/3.48      (![X1 : $i, X3 : $i]:
% 3.30/3.48         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 3.30/3.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.30/3.48  thf('55', plain,
% 3.30/3.48      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 3.30/3.48           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 3.30/3.48        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 3.30/3.48      inference('sup-', [status(thm)], ['53', '54'])).
% 3.30/3.48  thf('56', plain,
% 3.30/3.48      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.30/3.48        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.30/3.48        (k6_partfun1 @ sk_A))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('57', plain,
% 3.30/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['31', '32'])).
% 3.30/3.48  thf('58', plain,
% 3.30/3.48      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.30/3.48        (k6_partfun1 @ sk_A))),
% 3.30/3.48      inference('demod', [status(thm)], ['56', '57'])).
% 3.30/3.48  thf('59', plain,
% 3.30/3.48      ((m1_subset_1 @ 
% 3.30/3.48        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 3.30/3.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.30/3.48      inference('demod', [status(thm)], ['18', '19'])).
% 3.30/3.48  thf('60', plain,
% 3.30/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['31', '32'])).
% 3.30/3.48  thf('61', plain,
% 3.30/3.48      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 3.30/3.48        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.30/3.48      inference('demod', [status(thm)], ['59', '60'])).
% 3.30/3.48  thf(redefinition_r2_relset_1, axiom,
% 3.30/3.48    (![A:$i,B:$i,C:$i,D:$i]:
% 3.30/3.48     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.30/3.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.48       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.30/3.48  thf('62', plain,
% 3.30/3.48      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 3.30/3.48         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.30/3.48          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 3.30/3.48          | ((X24) = (X27))
% 3.30/3.48          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 3.30/3.48      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.30/3.48  thf('63', plain,
% 3.30/3.48      (![X0 : $i]:
% 3.30/3.48         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 3.30/3.48          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 3.30/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.30/3.48      inference('sup-', [status(thm)], ['61', '62'])).
% 3.30/3.48  thf('64', plain,
% 3.30/3.48      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.30/3.48           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.30/3.48        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 3.30/3.48      inference('sup-', [status(thm)], ['58', '63'])).
% 3.30/3.48  thf(t29_relset_1, axiom,
% 3.30/3.48    (![A:$i]:
% 3.30/3.48     ( m1_subset_1 @
% 3.30/3.48       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.30/3.48  thf('65', plain,
% 3.30/3.48      (![X28 : $i]:
% 3.30/3.48         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 3.30/3.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 3.30/3.48      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.30/3.48  thf('66', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.30/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.30/3.48  thf('67', plain,
% 3.30/3.48      (![X28 : $i]:
% 3.30/3.48         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 3.30/3.48          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 3.30/3.48      inference('demod', [status(thm)], ['65', '66'])).
% 3.30/3.48  thf('68', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.30/3.48      inference('demod', [status(thm)], ['64', '67'])).
% 3.30/3.48  thf(t71_relat_1, axiom,
% 3.30/3.48    (![A:$i]:
% 3.30/3.48     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 3.30/3.48       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 3.30/3.48  thf('69', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 3.30/3.48      inference('cnf', [status(esa)], [t71_relat_1])).
% 3.30/3.48  thf('70', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 3.30/3.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.30/3.48  thf('71', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 3.30/3.48      inference('demod', [status(thm)], ['69', '70'])).
% 3.30/3.48  thf('72', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf(cc2_relset_1, axiom,
% 3.30/3.48    (![A:$i,B:$i,C:$i]:
% 3.30/3.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.30/3.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.30/3.48  thf('73', plain,
% 3.30/3.48      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.30/3.48         ((v5_relat_1 @ X21 @ X23)
% 3.30/3.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 3.30/3.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.30/3.48  thf('74', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.30/3.48      inference('sup-', [status(thm)], ['72', '73'])).
% 3.30/3.48  thf('75', plain,
% 3.30/3.48      (![X11 : $i, X12 : $i]:
% 3.30/3.48         (~ (v5_relat_1 @ X11 @ X12)
% 3.30/3.48          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.30/3.48          | ~ (v1_relat_1 @ X11))),
% 3.30/3.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.30/3.48  thf('76', plain,
% 3.30/3.48      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 3.30/3.48      inference('sup-', [status(thm)], ['74', '75'])).
% 3.30/3.48  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 3.30/3.48      inference('demod', [status(thm)], ['41', '42'])).
% 3.30/3.48  thf('78', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 3.30/3.48      inference('demod', [status(thm)], ['76', '77'])).
% 3.30/3.48  thf('79', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.30/3.48      inference('demod', [status(thm)], ['64', '67'])).
% 3.30/3.48  thf('80', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 3.30/3.48      inference('demod', [status(thm)], ['69', '70'])).
% 3.30/3.48  thf('81', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.30/3.48      inference('demod', [status(thm)], ['55', '68', '71', '78', '79', '80'])).
% 3.30/3.48  thf('82', plain,
% 3.30/3.48      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 3.30/3.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.30/3.48  thf('83', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 3.30/3.48      inference('simplify', [status(thm)], ['82'])).
% 3.30/3.48  thf('84', plain,
% 3.30/3.48      (![X11 : $i, X12 : $i]:
% 3.30/3.48         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 3.30/3.48          | (v5_relat_1 @ X11 @ X12)
% 3.30/3.48          | ~ (v1_relat_1 @ X11))),
% 3.30/3.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 3.30/3.48  thf('85', plain,
% 3.30/3.48      (![X0 : $i]:
% 3.30/3.48         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 3.30/3.48      inference('sup-', [status(thm)], ['83', '84'])).
% 3.30/3.48  thf(d3_funct_2, axiom,
% 3.30/3.48    (![A:$i,B:$i]:
% 3.30/3.48     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.30/3.48       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.30/3.48  thf('86', plain,
% 3.30/3.48      (![X29 : $i, X30 : $i]:
% 3.30/3.48         (((k2_relat_1 @ X30) != (X29))
% 3.30/3.48          | (v2_funct_2 @ X30 @ X29)
% 3.30/3.48          | ~ (v5_relat_1 @ X30 @ X29)
% 3.30/3.48          | ~ (v1_relat_1 @ X30))),
% 3.30/3.48      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.30/3.48  thf('87', plain,
% 3.30/3.48      (![X30 : $i]:
% 3.30/3.48         (~ (v1_relat_1 @ X30)
% 3.30/3.48          | ~ (v5_relat_1 @ X30 @ (k2_relat_1 @ X30))
% 3.30/3.48          | (v2_funct_2 @ X30 @ (k2_relat_1 @ X30)))),
% 3.30/3.48      inference('simplify', [status(thm)], ['86'])).
% 3.30/3.48  thf('88', plain,
% 3.30/3.48      (![X0 : $i]:
% 3.30/3.48         (~ (v1_relat_1 @ X0)
% 3.30/3.48          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 3.30/3.48          | ~ (v1_relat_1 @ X0))),
% 3.30/3.48      inference('sup-', [status(thm)], ['85', '87'])).
% 3.30/3.48  thf('89', plain,
% 3.30/3.48      (![X0 : $i]:
% 3.30/3.48         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 3.30/3.48      inference('simplify', [status(thm)], ['88'])).
% 3.30/3.48  thf('90', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 3.30/3.48      inference('sup+', [status(thm)], ['81', '89'])).
% 3.30/3.48  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 3.30/3.48      inference('demod', [status(thm)], ['41', '42'])).
% 3.30/3.48  thf('92', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.30/3.48      inference('demod', [status(thm)], ['90', '91'])).
% 3.30/3.48  thf('93', plain,
% 3.30/3.48      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.30/3.48      inference('split', [status(esa)], ['9'])).
% 3.30/3.48  thf('94', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.30/3.48      inference('sup-', [status(thm)], ['92', '93'])).
% 3.30/3.48  thf('95', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.30/3.48      inference('split', [status(esa)], ['9'])).
% 3.30/3.48  thf('96', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.30/3.48      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 3.30/3.48  thf('97', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.30/3.48      inference('simpl_trail', [status(thm)], ['11', '96'])).
% 3.30/3.48  thf('98', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf(cc1_subset_1, axiom,
% 3.30/3.48    (![A:$i]:
% 3.30/3.48     ( ( v1_xboole_0 @ A ) =>
% 3.30/3.48       ( ![B:$i]:
% 3.30/3.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 3.30/3.48  thf('99', plain,
% 3.30/3.48      (![X7 : $i, X8 : $i]:
% 3.30/3.48         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 3.30/3.48          | (v1_xboole_0 @ X7)
% 3.30/3.48          | ~ (v1_xboole_0 @ X8))),
% 3.30/3.48      inference('cnf', [status(esa)], [cc1_subset_1])).
% 3.30/3.48  thf('100', plain,
% 3.30/3.48      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 3.30/3.48      inference('sup-', [status(thm)], ['98', '99'])).
% 3.30/3.48  thf('101', plain,
% 3.30/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.48         = (k5_relat_1 @ sk_C @ sk_D))),
% 3.30/3.48      inference('demod', [status(thm)], ['31', '32'])).
% 3.30/3.48  thf('102', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 3.30/3.48      inference('demod', [status(thm)], ['64', '67'])).
% 3.30/3.48  thf('103', plain,
% 3.30/3.48      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 3.30/3.48         = (k6_partfun1 @ sk_A))),
% 3.30/3.48      inference('demod', [status(thm)], ['101', '102'])).
% 3.30/3.48  thf('104', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf(t26_funct_2, axiom,
% 3.30/3.48    (![A:$i,B:$i,C:$i,D:$i]:
% 3.30/3.48     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.30/3.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.30/3.48       ( ![E:$i]:
% 3.30/3.48         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.30/3.48             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.30/3.48           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.30/3.48             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.30/3.48               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.30/3.48  thf('105', plain,
% 3.30/3.48      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 3.30/3.48         (~ (v1_funct_1 @ X44)
% 3.30/3.48          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 3.30/3.48          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 3.30/3.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 3.30/3.48          | (v2_funct_1 @ X48)
% 3.30/3.48          | ((X46) = (k1_xboole_0))
% 3.30/3.48          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 3.30/3.48          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 3.30/3.48          | ~ (v1_funct_1 @ X48))),
% 3.30/3.48      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.30/3.48  thf('106', plain,
% 3.30/3.48      (![X0 : $i, X1 : $i]:
% 3.30/3.48         (~ (v1_funct_1 @ X0)
% 3.30/3.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.30/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.30/3.48          | ((sk_A) = (k1_xboole_0))
% 3.30/3.48          | (v2_funct_1 @ X0)
% 3.30/3.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 3.30/3.48          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 3.30/3.48          | ~ (v1_funct_1 @ sk_D))),
% 3.30/3.48      inference('sup-', [status(thm)], ['104', '105'])).
% 3.30/3.48  thf('107', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('108', plain, ((v1_funct_1 @ sk_D)),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('109', plain,
% 3.30/3.48      (![X0 : $i, X1 : $i]:
% 3.30/3.48         (~ (v1_funct_1 @ X0)
% 3.30/3.48          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 3.30/3.48          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 3.30/3.48          | ((sk_A) = (k1_xboole_0))
% 3.30/3.48          | (v2_funct_1 @ X0)
% 3.30/3.48          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 3.30/3.48      inference('demod', [status(thm)], ['106', '107', '108'])).
% 3.30/3.48  thf('110', plain,
% 3.30/3.48      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.30/3.48        | (v2_funct_1 @ sk_C)
% 3.30/3.48        | ((sk_A) = (k1_xboole_0))
% 3.30/3.48        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 3.30/3.48        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 3.30/3.48        | ~ (v1_funct_1 @ sk_C))),
% 3.30/3.48      inference('sup-', [status(thm)], ['103', '109'])).
% 3.30/3.48  thf('111', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 3.30/3.48      inference('demod', [status(thm)], ['4', '5'])).
% 3.30/3.48  thf('112', plain,
% 3.30/3.48      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('113', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('114', plain, ((v1_funct_1 @ sk_C)),
% 3.30/3.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.30/3.48  thf('115', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.30/3.48      inference('demod', [status(thm)], ['110', '111', '112', '113', '114'])).
% 3.30/3.48  thf('116', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.30/3.48      inference('split', [status(esa)], ['9'])).
% 3.30/3.48  thf('117', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.30/3.48      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 3.30/3.48  thf('118', plain, (~ (v2_funct_1 @ sk_C)),
% 3.30/3.48      inference('simpl_trail', [status(thm)], ['116', '117'])).
% 3.30/3.48  thf('119', plain, (((sk_A) = (k1_xboole_0))),
% 3.30/3.48      inference('clc', [status(thm)], ['115', '118'])).
% 3.30/3.48  thf(t113_zfmisc_1, axiom,
% 3.30/3.48    (![A:$i,B:$i]:
% 3.30/3.48     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.30/3.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.30/3.48  thf('120', plain,
% 3.30/3.48      (![X5 : $i, X6 : $i]:
% 3.30/3.48         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 3.30/3.48      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.30/3.48  thf('121', plain,
% 3.30/3.48      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 3.30/3.48      inference('simplify', [status(thm)], ['120'])).
% 3.30/3.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.30/3.48  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.30/3.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.30/3.48  thf('123', plain, ((v1_xboole_0 @ sk_C)),
% 3.30/3.48      inference('demod', [status(thm)], ['100', '119', '121', '122'])).
% 3.30/3.48  thf('124', plain, ($false), inference('demod', [status(thm)], ['97', '123'])).
% 3.30/3.48  
% 3.30/3.48  % SZS output end Refutation
% 3.30/3.48  
% 3.30/3.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
