%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bsekB7OPAA

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:25 EST 2020

% Result     : Theorem 8.98s
% Output     : Refutation 8.98s
% Verified   : 
% Statistics : Number of formulae       :  191 (1012 expanded)
%              Number of leaves         :   46 ( 305 expanded)
%              Depth                    :   24
%              Number of atoms          : 1434 (19704 expanded)
%              Number of equality atoms :   59 ( 242 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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
    ! [X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
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

thf('98',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('99',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('100',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ( ( k1_relat_1 @ X0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k6_partfun1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('104',plain,(
    ! [X43: $i] :
      ( ( k6_partfun1 @ X43 )
      = ( k6_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('105',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('108',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['106','107'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('109',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('110',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('112',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('114',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('115',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('116',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['102','105','112','113','114','115','116'])).

thf('118',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('119',plain,(
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

thf('120',plain,(
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

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['125','126','127','128'])).

thf('130',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('131',plain,(
    ! [X20: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X20 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('132',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('134',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['94','95'])).

thf('136',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['117','136'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('138',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('139',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('140',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('141',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('142',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['139','140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['97','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bsekB7OPAA
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:32:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.98/9.21  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.98/9.21  % Solved by: fo/fo7.sh
% 8.98/9.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.98/9.21  % done 6979 iterations in 8.751s
% 8.98/9.21  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.98/9.21  % SZS output start Refutation
% 8.98/9.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.98/9.21  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.98/9.21  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 8.98/9.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.98/9.21  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.98/9.21  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 8.98/9.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.98/9.21  thf(sk_B_type, type, sk_B: $i).
% 8.98/9.21  thf(sk_A_type, type, sk_A: $i).
% 8.98/9.21  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.98/9.21  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 8.98/9.21  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 8.98/9.21  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.98/9.21  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.98/9.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.98/9.21  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 8.98/9.21  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.98/9.21  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.98/9.21  thf(sk_D_type, type, sk_D: $i).
% 8.98/9.21  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.98/9.21  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.98/9.21  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.98/9.21  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.98/9.21  thf(sk_C_type, type, sk_C: $i).
% 8.98/9.21  thf(l13_xboole_0, axiom,
% 8.98/9.21    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 8.98/9.21  thf('0', plain,
% 8.98/9.21      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 8.98/9.21      inference('cnf', [status(esa)], [l13_xboole_0])).
% 8.98/9.21  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 8.98/9.21  thf('1', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.21      inference('cnf', [status(esa)], [t81_relat_1])).
% 8.98/9.21  thf(redefinition_k6_partfun1, axiom,
% 8.98/9.21    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 8.98/9.21  thf('2', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 8.98/9.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.98/9.21  thf('3', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.98/9.21      inference('demod', [status(thm)], ['1', '2'])).
% 8.98/9.21  thf(fc4_funct_1, axiom,
% 8.98/9.21    (![A:$i]:
% 8.98/9.21     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 8.98/9.21       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 8.98/9.21  thf('4', plain, (![X20 : $i]: (v2_funct_1 @ (k6_relat_1 @ X20))),
% 8.98/9.21      inference('cnf', [status(esa)], [fc4_funct_1])).
% 8.98/9.21  thf('5', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 8.98/9.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.98/9.21  thf('6', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 8.98/9.21      inference('demod', [status(thm)], ['4', '5'])).
% 8.98/9.21  thf('7', plain, ((v2_funct_1 @ k1_xboole_0)),
% 8.98/9.21      inference('sup+', [status(thm)], ['3', '6'])).
% 8.98/9.21  thf('8', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 8.98/9.21      inference('sup+', [status(thm)], ['0', '7'])).
% 8.98/9.21  thf(t29_funct_2, conjecture,
% 8.98/9.21    (![A:$i,B:$i,C:$i]:
% 8.98/9.21     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.98/9.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.98/9.21       ( ![D:$i]:
% 8.98/9.21         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.98/9.21             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.98/9.21           ( ( r2_relset_1 @
% 8.98/9.21               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.98/9.21               ( k6_partfun1 @ A ) ) =>
% 8.98/9.21             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 8.98/9.21  thf(zf_stmt_0, negated_conjecture,
% 8.98/9.21    (~( ![A:$i,B:$i,C:$i]:
% 8.98/9.21        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.98/9.21            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.98/9.21          ( ![D:$i]:
% 8.98/9.21            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.98/9.21                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.98/9.21              ( ( r2_relset_1 @
% 8.98/9.21                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.98/9.21                  ( k6_partfun1 @ A ) ) =>
% 8.98/9.21                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 8.98/9.21    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 8.98/9.21  thf('9', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('10', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 8.98/9.21      inference('split', [status(esa)], ['9'])).
% 8.98/9.21  thf('11', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 8.98/9.21      inference('sup-', [status(thm)], ['8', '10'])).
% 8.98/9.21  thf('12', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('13', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf(dt_k1_partfun1, axiom,
% 8.98/9.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.98/9.21     ( ( ( v1_funct_1 @ E ) & 
% 8.98/9.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.98/9.21         ( v1_funct_1 @ F ) & 
% 8.98/9.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.98/9.21       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 8.98/9.21         ( m1_subset_1 @
% 8.98/9.21           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 8.98/9.21           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 8.98/9.21  thf('14', plain,
% 8.98/9.21      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 8.98/9.21         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 8.98/9.21          | ~ (v1_funct_1 @ X31)
% 8.98/9.21          | ~ (v1_funct_1 @ X34)
% 8.98/9.21          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 8.98/9.21          | (m1_subset_1 @ (k1_partfun1 @ X32 @ X33 @ X35 @ X36 @ X31 @ X34) @ 
% 8.98/9.21             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X36))))),
% 8.98/9.21      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 8.98/9.21  thf('15', plain,
% 8.98/9.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.98/9.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.98/9.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 8.98/9.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.98/9.21          | ~ (v1_funct_1 @ X1)
% 8.98/9.21          | ~ (v1_funct_1 @ sk_C))),
% 8.98/9.21      inference('sup-', [status(thm)], ['13', '14'])).
% 8.98/9.21  thf('16', plain, ((v1_funct_1 @ sk_C)),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('17', plain,
% 8.98/9.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.98/9.21         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.98/9.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 8.98/9.21          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.98/9.21          | ~ (v1_funct_1 @ X1))),
% 8.98/9.21      inference('demod', [status(thm)], ['15', '16'])).
% 8.98/9.21  thf('18', plain,
% 8.98/9.21      ((~ (v1_funct_1 @ sk_D)
% 8.98/9.21        | (m1_subset_1 @ 
% 8.98/9.21           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.98/9.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 8.98/9.21      inference('sup-', [status(thm)], ['12', '17'])).
% 8.98/9.21  thf('19', plain, ((v1_funct_1 @ sk_D)),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('20', plain,
% 8.98/9.21      ((m1_subset_1 @ 
% 8.98/9.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.98/9.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 8.98/9.21      inference('demod', [status(thm)], ['18', '19'])).
% 8.98/9.21  thf(cc2_relat_1, axiom,
% 8.98/9.21    (![A:$i]:
% 8.98/9.21     ( ( v1_relat_1 @ A ) =>
% 8.98/9.21       ( ![B:$i]:
% 8.98/9.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.98/9.21  thf('21', plain,
% 8.98/9.21      (![X4 : $i, X5 : $i]:
% 8.98/9.21         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 8.98/9.21          | (v1_relat_1 @ X4)
% 8.98/9.21          | ~ (v1_relat_1 @ X5))),
% 8.98/9.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.98/9.21  thf('22', plain,
% 8.98/9.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 8.98/9.21        | (v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)))),
% 8.98/9.21      inference('sup-', [status(thm)], ['20', '21'])).
% 8.98/9.21  thf(fc6_relat_1, axiom,
% 8.98/9.21    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.98/9.21  thf('23', plain,
% 8.98/9.21      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 8.98/9.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.98/9.21  thf('24', plain,
% 8.98/9.21      ((v1_relat_1 @ (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['22', '23'])).
% 8.98/9.21  thf('25', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('26', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf(redefinition_k1_partfun1, axiom,
% 8.98/9.21    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.98/9.21     ( ( ( v1_funct_1 @ E ) & 
% 8.98/9.21         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.98/9.21         ( v1_funct_1 @ F ) & 
% 8.98/9.21         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.98/9.21       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 8.98/9.21  thf('27', plain,
% 8.98/9.21      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 8.98/9.21         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 8.98/9.21          | ~ (v1_funct_1 @ X37)
% 8.98/9.21          | ~ (v1_funct_1 @ X40)
% 8.98/9.21          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 8.98/9.21          | ((k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40)
% 8.98/9.21              = (k5_relat_1 @ X37 @ X40)))),
% 8.98/9.21      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 8.98/9.21  thf('28', plain,
% 8.98/9.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.98/9.21         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.98/9.21            = (k5_relat_1 @ sk_C @ X0))
% 8.98/9.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.98/9.21          | ~ (v1_funct_1 @ X0)
% 8.98/9.21          | ~ (v1_funct_1 @ sk_C))),
% 8.98/9.21      inference('sup-', [status(thm)], ['26', '27'])).
% 8.98/9.21  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('30', plain,
% 8.98/9.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.98/9.21         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.98/9.21            = (k5_relat_1 @ sk_C @ X0))
% 8.98/9.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.98/9.21          | ~ (v1_funct_1 @ X0))),
% 8.98/9.21      inference('demod', [status(thm)], ['28', '29'])).
% 8.98/9.21  thf('31', plain,
% 8.98/9.21      ((~ (v1_funct_1 @ sk_D)
% 8.98/9.21        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.98/9.21            = (k5_relat_1 @ sk_C @ sk_D)))),
% 8.98/9.21      inference('sup-', [status(thm)], ['25', '30'])).
% 8.98/9.21  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('33', plain,
% 8.98/9.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.98/9.21         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['31', '32'])).
% 8.98/9.21  thf('34', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['24', '33'])).
% 8.98/9.21  thf(t45_relat_1, axiom,
% 8.98/9.21    (![A:$i]:
% 8.98/9.21     ( ( v1_relat_1 @ A ) =>
% 8.98/9.21       ( ![B:$i]:
% 8.98/9.21         ( ( v1_relat_1 @ B ) =>
% 8.98/9.21           ( r1_tarski @
% 8.98/9.21             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 8.98/9.21  thf('35', plain,
% 8.98/9.21      (![X15 : $i, X16 : $i]:
% 8.98/9.21         (~ (v1_relat_1 @ X15)
% 8.98/9.21          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X16 @ X15)) @ 
% 8.98/9.21             (k2_relat_1 @ X15))
% 8.98/9.21          | ~ (v1_relat_1 @ X16))),
% 8.98/9.21      inference('cnf', [status(esa)], [t45_relat_1])).
% 8.98/9.21  thf(d19_relat_1, axiom,
% 8.98/9.21    (![A:$i,B:$i]:
% 8.98/9.21     ( ( v1_relat_1 @ B ) =>
% 8.98/9.21       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 8.98/9.21  thf('36', plain,
% 8.98/9.21      (![X8 : $i, X9 : $i]:
% 8.98/9.21         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 8.98/9.21          | (v5_relat_1 @ X8 @ X9)
% 8.98/9.21          | ~ (v1_relat_1 @ X8))),
% 8.98/9.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.98/9.21  thf('37', plain,
% 8.98/9.21      (![X0 : $i, X1 : $i]:
% 8.98/9.21         (~ (v1_relat_1 @ X1)
% 8.98/9.21          | ~ (v1_relat_1 @ X0)
% 8.98/9.21          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 8.98/9.21          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 8.98/9.21      inference('sup-', [status(thm)], ['35', '36'])).
% 8.98/9.21  thf('38', plain,
% 8.98/9.21      (((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))
% 8.98/9.21        | ~ (v1_relat_1 @ sk_D)
% 8.98/9.21        | ~ (v1_relat_1 @ sk_C))),
% 8.98/9.21      inference('sup-', [status(thm)], ['34', '37'])).
% 8.98/9.21  thf('39', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('40', plain,
% 8.98/9.21      (![X4 : $i, X5 : $i]:
% 8.98/9.21         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 8.98/9.21          | (v1_relat_1 @ X4)
% 8.98/9.21          | ~ (v1_relat_1 @ X5))),
% 8.98/9.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.98/9.21  thf('41', plain,
% 8.98/9.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 8.98/9.21      inference('sup-', [status(thm)], ['39', '40'])).
% 8.98/9.21  thf('42', plain,
% 8.98/9.21      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 8.98/9.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.98/9.21  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 8.98/9.21      inference('demod', [status(thm)], ['41', '42'])).
% 8.98/9.21  thf('44', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('45', plain,
% 8.98/9.21      (![X4 : $i, X5 : $i]:
% 8.98/9.21         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 8.98/9.21          | (v1_relat_1 @ X4)
% 8.98/9.21          | ~ (v1_relat_1 @ X5))),
% 8.98/9.21      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.98/9.21  thf('46', plain,
% 8.98/9.21      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 8.98/9.21      inference('sup-', [status(thm)], ['44', '45'])).
% 8.98/9.21  thf('47', plain,
% 8.98/9.21      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 8.98/9.21      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.98/9.21  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.21      inference('demod', [status(thm)], ['46', '47'])).
% 8.98/9.21  thf('49', plain,
% 8.98/9.21      ((v5_relat_1 @ (k5_relat_1 @ sk_C @ sk_D) @ (k2_relat_1 @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['38', '43', '48'])).
% 8.98/9.21  thf('50', plain,
% 8.98/9.21      (![X8 : $i, X9 : $i]:
% 8.98/9.21         (~ (v5_relat_1 @ X8 @ X9)
% 8.98/9.21          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 8.98/9.21          | ~ (v1_relat_1 @ X8))),
% 8.98/9.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.98/9.21  thf('51', plain,
% 8.98/9.21      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 8.98/9.21        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 8.98/9.21           (k2_relat_1 @ sk_D)))),
% 8.98/9.21      inference('sup-', [status(thm)], ['49', '50'])).
% 8.98/9.21  thf('52', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['24', '33'])).
% 8.98/9.21  thf('53', plain,
% 8.98/9.21      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 8.98/9.21        (k2_relat_1 @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['51', '52'])).
% 8.98/9.21  thf(d10_xboole_0, axiom,
% 8.98/9.21    (![A:$i,B:$i]:
% 8.98/9.21     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.98/9.21  thf('54', plain,
% 8.98/9.21      (![X1 : $i, X3 : $i]:
% 8.98/9.21         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 8.98/9.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.98/9.21  thf('55', plain,
% 8.98/9.21      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 8.98/9.21           (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 8.98/9.21        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 8.98/9.21      inference('sup-', [status(thm)], ['53', '54'])).
% 8.98/9.21  thf('56', plain,
% 8.98/9.21      ((r2_relset_1 @ sk_A @ sk_A @ 
% 8.98/9.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.98/9.21        (k6_partfun1 @ sk_A))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('57', plain,
% 8.98/9.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.98/9.21         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['31', '32'])).
% 8.98/9.21  thf('58', plain,
% 8.98/9.21      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 8.98/9.21        (k6_partfun1 @ sk_A))),
% 8.98/9.21      inference('demod', [status(thm)], ['56', '57'])).
% 8.98/9.21  thf('59', plain,
% 8.98/9.21      ((m1_subset_1 @ 
% 8.98/9.21        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.98/9.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 8.98/9.21      inference('demod', [status(thm)], ['18', '19'])).
% 8.98/9.21  thf('60', plain,
% 8.98/9.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.98/9.21         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['31', '32'])).
% 8.98/9.21  thf('61', plain,
% 8.98/9.21      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 8.98/9.21        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 8.98/9.21      inference('demod', [status(thm)], ['59', '60'])).
% 8.98/9.21  thf(redefinition_r2_relset_1, axiom,
% 8.98/9.21    (![A:$i,B:$i,C:$i,D:$i]:
% 8.98/9.21     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.98/9.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.98/9.21       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 8.98/9.21  thf('62', plain,
% 8.98/9.21      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 8.98/9.21         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 8.98/9.21          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 8.98/9.21          | ((X24) = (X27))
% 8.98/9.21          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 8.98/9.21      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 8.98/9.21  thf('63', plain,
% 8.98/9.21      (![X0 : $i]:
% 8.98/9.21         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 8.98/9.21          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 8.98/9.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 8.98/9.21      inference('sup-', [status(thm)], ['61', '62'])).
% 8.98/9.21  thf('64', plain,
% 8.98/9.21      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 8.98/9.21           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 8.98/9.21        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 8.98/9.21      inference('sup-', [status(thm)], ['58', '63'])).
% 8.98/9.21  thf(t29_relset_1, axiom,
% 8.98/9.21    (![A:$i]:
% 8.98/9.21     ( m1_subset_1 @
% 8.98/9.21       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 8.98/9.21  thf('65', plain,
% 8.98/9.21      (![X28 : $i]:
% 8.98/9.21         (m1_subset_1 @ (k6_relat_1 @ X28) @ 
% 8.98/9.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 8.98/9.21      inference('cnf', [status(esa)], [t29_relset_1])).
% 8.98/9.21  thf('66', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 8.98/9.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.98/9.21  thf('67', plain,
% 8.98/9.21      (![X28 : $i]:
% 8.98/9.21         (m1_subset_1 @ (k6_partfun1 @ X28) @ 
% 8.98/9.21          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X28)))),
% 8.98/9.21      inference('demod', [status(thm)], ['65', '66'])).
% 8.98/9.21  thf('68', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 8.98/9.21      inference('demod', [status(thm)], ['64', '67'])).
% 8.98/9.21  thf(t71_relat_1, axiom,
% 8.98/9.21    (![A:$i]:
% 8.98/9.21     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.98/9.21       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.98/9.21  thf('69', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X18)) = (X18))),
% 8.98/9.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.98/9.21  thf('70', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 8.98/9.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.98/9.21  thf('71', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 8.98/9.21      inference('demod', [status(thm)], ['69', '70'])).
% 8.98/9.21  thf('72', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf(cc2_relset_1, axiom,
% 8.98/9.21    (![A:$i,B:$i,C:$i]:
% 8.98/9.21     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.98/9.21       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.98/9.21  thf('73', plain,
% 8.98/9.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.98/9.21         ((v5_relat_1 @ X21 @ X23)
% 8.98/9.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 8.98/9.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.98/9.21  thf('74', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 8.98/9.21      inference('sup-', [status(thm)], ['72', '73'])).
% 8.98/9.21  thf('75', plain,
% 8.98/9.21      (![X8 : $i, X9 : $i]:
% 8.98/9.21         (~ (v5_relat_1 @ X8 @ X9)
% 8.98/9.21          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 8.98/9.21          | ~ (v1_relat_1 @ X8))),
% 8.98/9.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.98/9.21  thf('76', plain,
% 8.98/9.21      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 8.98/9.21      inference('sup-', [status(thm)], ['74', '75'])).
% 8.98/9.21  thf('77', plain, ((v1_relat_1 @ sk_D)),
% 8.98/9.21      inference('demod', [status(thm)], ['41', '42'])).
% 8.98/9.21  thf('78', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 8.98/9.21      inference('demod', [status(thm)], ['76', '77'])).
% 8.98/9.21  thf('79', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 8.98/9.21      inference('demod', [status(thm)], ['64', '67'])).
% 8.98/9.21  thf('80', plain, (![X18 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X18)) = (X18))),
% 8.98/9.21      inference('demod', [status(thm)], ['69', '70'])).
% 8.98/9.21  thf('81', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 8.98/9.21      inference('demod', [status(thm)], ['55', '68', '71', '78', '79', '80'])).
% 8.98/9.21  thf('82', plain,
% 8.98/9.21      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 8.98/9.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.98/9.21  thf('83', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 8.98/9.21      inference('simplify', [status(thm)], ['82'])).
% 8.98/9.21  thf('84', plain,
% 8.98/9.21      (![X8 : $i, X9 : $i]:
% 8.98/9.21         (~ (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 8.98/9.21          | (v5_relat_1 @ X8 @ X9)
% 8.98/9.21          | ~ (v1_relat_1 @ X8))),
% 8.98/9.21      inference('cnf', [status(esa)], [d19_relat_1])).
% 8.98/9.21  thf('85', plain,
% 8.98/9.21      (![X0 : $i]:
% 8.98/9.21         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 8.98/9.21      inference('sup-', [status(thm)], ['83', '84'])).
% 8.98/9.21  thf(d3_funct_2, axiom,
% 8.98/9.21    (![A:$i,B:$i]:
% 8.98/9.21     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 8.98/9.21       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 8.98/9.21  thf('86', plain,
% 8.98/9.21      (![X29 : $i, X30 : $i]:
% 8.98/9.21         (((k2_relat_1 @ X30) != (X29))
% 8.98/9.21          | (v2_funct_2 @ X30 @ X29)
% 8.98/9.21          | ~ (v5_relat_1 @ X30 @ X29)
% 8.98/9.21          | ~ (v1_relat_1 @ X30))),
% 8.98/9.21      inference('cnf', [status(esa)], [d3_funct_2])).
% 8.98/9.21  thf('87', plain,
% 8.98/9.21      (![X30 : $i]:
% 8.98/9.21         (~ (v1_relat_1 @ X30)
% 8.98/9.21          | ~ (v5_relat_1 @ X30 @ (k2_relat_1 @ X30))
% 8.98/9.21          | (v2_funct_2 @ X30 @ (k2_relat_1 @ X30)))),
% 8.98/9.21      inference('simplify', [status(thm)], ['86'])).
% 8.98/9.21  thf('88', plain,
% 8.98/9.21      (![X0 : $i]:
% 8.98/9.21         (~ (v1_relat_1 @ X0)
% 8.98/9.21          | (v2_funct_2 @ X0 @ (k2_relat_1 @ X0))
% 8.98/9.21          | ~ (v1_relat_1 @ X0))),
% 8.98/9.21      inference('sup-', [status(thm)], ['85', '87'])).
% 8.98/9.21  thf('89', plain,
% 8.98/9.21      (![X0 : $i]:
% 8.98/9.21         ((v2_funct_2 @ X0 @ (k2_relat_1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 8.98/9.21      inference('simplify', [status(thm)], ['88'])).
% 8.98/9.21  thf('90', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 8.98/9.21      inference('sup+', [status(thm)], ['81', '89'])).
% 8.98/9.21  thf('91', plain, ((v1_relat_1 @ sk_D)),
% 8.98/9.21      inference('demod', [status(thm)], ['41', '42'])).
% 8.98/9.21  thf('92', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 8.98/9.21      inference('demod', [status(thm)], ['90', '91'])).
% 8.98/9.21  thf('93', plain,
% 8.98/9.21      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 8.98/9.21      inference('split', [status(esa)], ['9'])).
% 8.98/9.21  thf('94', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 8.98/9.21      inference('sup-', [status(thm)], ['92', '93'])).
% 8.98/9.21  thf('95', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 8.98/9.21      inference('split', [status(esa)], ['9'])).
% 8.98/9.21  thf('96', plain, (~ ((v2_funct_1 @ sk_C))),
% 8.98/9.21      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 8.98/9.21  thf('97', plain, (~ (v1_xboole_0 @ sk_C)),
% 8.98/9.21      inference('simpl_trail', [status(thm)], ['11', '96'])).
% 8.98/9.21  thf('98', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 8.98/9.21      inference('demod', [status(thm)], ['64', '67'])).
% 8.98/9.21  thf(t44_relat_1, axiom,
% 8.98/9.21    (![A:$i]:
% 8.98/9.21     ( ( v1_relat_1 @ A ) =>
% 8.98/9.21       ( ![B:$i]:
% 8.98/9.21         ( ( v1_relat_1 @ B ) =>
% 8.98/9.21           ( r1_tarski @
% 8.98/9.21             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 8.98/9.21  thf('99', plain,
% 8.98/9.21      (![X13 : $i, X14 : $i]:
% 8.98/9.21         (~ (v1_relat_1 @ X13)
% 8.98/9.21          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 8.98/9.21             (k1_relat_1 @ X14))
% 8.98/9.21          | ~ (v1_relat_1 @ X14))),
% 8.98/9.21      inference('cnf', [status(esa)], [t44_relat_1])).
% 8.98/9.21  thf('100', plain,
% 8.98/9.21      (![X1 : $i, X3 : $i]:
% 8.98/9.21         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 8.98/9.21      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.98/9.21  thf('101', plain,
% 8.98/9.21      (![X0 : $i, X1 : $i]:
% 8.98/9.21         (~ (v1_relat_1 @ X0)
% 8.98/9.21          | ~ (v1_relat_1 @ X1)
% 8.98/9.21          | ~ (r1_tarski @ (k1_relat_1 @ X0) @ 
% 8.98/9.21               (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 8.98/9.21          | ((k1_relat_1 @ X0) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 8.98/9.21      inference('sup-', [status(thm)], ['99', '100'])).
% 8.98/9.21  thf('102', plain,
% 8.98/9.21      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 8.98/9.21           (k1_relat_1 @ (k6_partfun1 @ sk_A)))
% 8.98/9.21        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 8.98/9.21        | ~ (v1_relat_1 @ sk_D)
% 8.98/9.21        | ~ (v1_relat_1 @ sk_C))),
% 8.98/9.21      inference('sup-', [status(thm)], ['98', '101'])).
% 8.98/9.21  thf('103', plain, (![X17 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X17)) = (X17))),
% 8.98/9.21      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.98/9.21  thf('104', plain, (![X43 : $i]: ((k6_partfun1 @ X43) = (k6_relat_1 @ X43))),
% 8.98/9.21      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.98/9.21  thf('105', plain,
% 8.98/9.21      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 8.98/9.21      inference('demod', [status(thm)], ['103', '104'])).
% 8.98/9.21  thf('106', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('107', plain,
% 8.98/9.21      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.98/9.21         ((v4_relat_1 @ X21 @ X22)
% 8.98/9.21          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 8.98/9.21      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.98/9.21  thf('108', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 8.98/9.21      inference('sup-', [status(thm)], ['106', '107'])).
% 8.98/9.21  thf(d18_relat_1, axiom,
% 8.98/9.21    (![A:$i,B:$i]:
% 8.98/9.21     ( ( v1_relat_1 @ B ) =>
% 8.98/9.21       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 8.98/9.21  thf('109', plain,
% 8.98/9.21      (![X6 : $i, X7 : $i]:
% 8.98/9.21         (~ (v4_relat_1 @ X6 @ X7)
% 8.98/9.21          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 8.98/9.21          | ~ (v1_relat_1 @ X6))),
% 8.98/9.21      inference('cnf', [status(esa)], [d18_relat_1])).
% 8.98/9.21  thf('110', plain,
% 8.98/9.21      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 8.98/9.21      inference('sup-', [status(thm)], ['108', '109'])).
% 8.98/9.21  thf('111', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.21      inference('demod', [status(thm)], ['46', '47'])).
% 8.98/9.21  thf('112', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 8.98/9.21      inference('demod', [status(thm)], ['110', '111'])).
% 8.98/9.21  thf('113', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 8.98/9.21      inference('demod', [status(thm)], ['64', '67'])).
% 8.98/9.21  thf('114', plain,
% 8.98/9.21      (![X17 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X17)) = (X17))),
% 8.98/9.21      inference('demod', [status(thm)], ['103', '104'])).
% 8.98/9.21  thf('115', plain, ((v1_relat_1 @ sk_D)),
% 8.98/9.21      inference('demod', [status(thm)], ['41', '42'])).
% 8.98/9.21  thf('116', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.21      inference('demod', [status(thm)], ['46', '47'])).
% 8.98/9.21  thf('117', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 8.98/9.21      inference('demod', [status(thm)],
% 8.98/9.21                ['102', '105', '112', '113', '114', '115', '116'])).
% 8.98/9.21  thf('118', plain,
% 8.98/9.21      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.98/9.21         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.98/9.21      inference('demod', [status(thm)], ['31', '32'])).
% 8.98/9.21  thf('119', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf(t26_funct_2, axiom,
% 8.98/9.21    (![A:$i,B:$i,C:$i,D:$i]:
% 8.98/9.21     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 8.98/9.21         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.98/9.21       ( ![E:$i]:
% 8.98/9.21         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 8.98/9.21             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 8.98/9.21           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 8.98/9.21             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 8.98/9.21               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 8.98/9.21  thf('120', plain,
% 8.98/9.21      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 8.98/9.21         (~ (v1_funct_1 @ X44)
% 8.98/9.21          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 8.98/9.21          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 8.98/9.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X47 @ X45 @ X45 @ X46 @ X48 @ X44))
% 8.98/9.21          | (v2_funct_1 @ X48)
% 8.98/9.21          | ((X46) = (k1_xboole_0))
% 8.98/9.21          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X45)))
% 8.98/9.21          | ~ (v1_funct_2 @ X48 @ X47 @ X45)
% 8.98/9.21          | ~ (v1_funct_1 @ X48))),
% 8.98/9.21      inference('cnf', [status(esa)], [t26_funct_2])).
% 8.98/9.21  thf('121', plain,
% 8.98/9.21      (![X0 : $i, X1 : $i]:
% 8.98/9.21         (~ (v1_funct_1 @ X0)
% 8.98/9.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.98/9.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.98/9.21          | ((sk_A) = (k1_xboole_0))
% 8.98/9.21          | (v2_funct_1 @ X0)
% 8.98/9.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 8.98/9.21          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 8.98/9.21          | ~ (v1_funct_1 @ sk_D))),
% 8.98/9.21      inference('sup-', [status(thm)], ['119', '120'])).
% 8.98/9.21  thf('122', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('123', plain, ((v1_funct_1 @ sk_D)),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('124', plain,
% 8.98/9.21      (![X0 : $i, X1 : $i]:
% 8.98/9.21         (~ (v1_funct_1 @ X0)
% 8.98/9.21          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 8.98/9.21          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 8.98/9.21          | ((sk_A) = (k1_xboole_0))
% 8.98/9.21          | (v2_funct_1 @ X0)
% 8.98/9.21          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 8.98/9.21      inference('demod', [status(thm)], ['121', '122', '123'])).
% 8.98/9.21  thf('125', plain,
% 8.98/9.21      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 8.98/9.21        | (v2_funct_1 @ sk_C)
% 8.98/9.21        | ((sk_A) = (k1_xboole_0))
% 8.98/9.21        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 8.98/9.21        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 8.98/9.21        | ~ (v1_funct_1 @ sk_C))),
% 8.98/9.21      inference('sup-', [status(thm)], ['118', '124'])).
% 8.98/9.21  thf('126', plain,
% 8.98/9.21      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('127', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 8.98/9.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.98/9.21  thf('129', plain,
% 8.98/9.21      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C @ sk_D))
% 8.98/9.21        | (v2_funct_1 @ sk_C)
% 8.98/9.21        | ((sk_A) = (k1_xboole_0)))),
% 8.98/9.21      inference('demod', [status(thm)], ['125', '126', '127', '128'])).
% 8.98/9.21  thf('130', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 8.98/9.21      inference('demod', [status(thm)], ['64', '67'])).
% 8.98/9.21  thf('131', plain, (![X20 : $i]: (v2_funct_1 @ (k6_partfun1 @ X20))),
% 8.98/9.21      inference('demod', [status(thm)], ['4', '5'])).
% 8.98/9.21  thf('132', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 8.98/9.21      inference('demod', [status(thm)], ['129', '130', '131'])).
% 8.98/9.21  thf('133', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 8.98/9.21      inference('split', [status(esa)], ['9'])).
% 8.98/9.21  thf('134', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 8.98/9.21      inference('sup-', [status(thm)], ['132', '133'])).
% 8.98/9.21  thf('135', plain, (~ ((v2_funct_1 @ sk_C))),
% 8.98/9.21      inference('sat_resolution*', [status(thm)], ['94', '95'])).
% 8.98/9.21  thf('136', plain, (((sk_A) = (k1_xboole_0))),
% 8.98/9.21      inference('simpl_trail', [status(thm)], ['134', '135'])).
% 8.98/9.21  thf('137', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 8.98/9.21      inference('demod', [status(thm)], ['117', '136'])).
% 8.98/9.21  thf(fc8_relat_1, axiom,
% 8.98/9.21    (![A:$i]:
% 8.98/9.21     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 8.98/9.21       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 8.98/9.21  thf('138', plain,
% 8.98/9.21      (![X12 : $i]:
% 8.98/9.21         (~ (v1_xboole_0 @ (k1_relat_1 @ X12))
% 8.98/9.21          | ~ (v1_relat_1 @ X12)
% 8.98/9.21          | (v1_xboole_0 @ X12))),
% 8.98/9.21      inference('cnf', [status(esa)], [fc8_relat_1])).
% 8.98/9.21  thf('139', plain,
% 8.98/9.21      ((~ (v1_xboole_0 @ k1_xboole_0)
% 8.98/9.21        | (v1_xboole_0 @ sk_C)
% 8.98/9.21        | ~ (v1_relat_1 @ sk_C))),
% 8.98/9.21      inference('sup-', [status(thm)], ['137', '138'])).
% 8.98/9.21  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 8.98/9.21  thf('140', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.98/9.21      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 8.98/9.21  thf('141', plain, ((v1_relat_1 @ sk_C)),
% 8.98/9.21      inference('demod', [status(thm)], ['46', '47'])).
% 8.98/9.21  thf('142', plain, ((v1_xboole_0 @ sk_C)),
% 8.98/9.21      inference('demod', [status(thm)], ['139', '140', '141'])).
% 8.98/9.21  thf('143', plain, ($false), inference('demod', [status(thm)], ['97', '142'])).
% 8.98/9.21  
% 8.98/9.21  % SZS output end Refutation
% 8.98/9.21  
% 8.98/9.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
