%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aItDxTJVgM

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:28 EST 2020

% Result     : Theorem 14.50s
% Output     : Refutation 14.53s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 958 expanded)
%              Number of leaves         :   48 ( 320 expanded)
%              Depth                    :   24
%              Number of atoms          : 1401 (12769 expanded)
%              Number of equality atoms :   77 ( 472 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_ordinal1_type,type,(
    v5_ordinal1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('19',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('22',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('23',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X48 ) @ X49 )
      | ( v1_funct_2 @ X48 @ ( k1_relat_1 @ X48 ) @ X49 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('25',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v5_ordinal1 @ k1_xboole_0 )
      & ( v1_funct_1 @ k1_xboole_0 )
      & ( v5_relat_1 @ k1_xboole_0 @ A )
      & ( v1_relat_1 @ k1_xboole_0 ) ) )).

thf('26',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('27',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('28',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','29'])).

thf('31',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('32',plain,(
    ! [X18: $i] :
      ( ~ ( v2_funct_1 @ X18 )
      | ( ( k2_funct_1 @ X18 )
        = ( k4_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('33',plain,
    ( ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( ( k2_funct_1 @ k1_xboole_0 )
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('35',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('36',plain,(
    ! [X17: $i] :
      ( ( v2_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('38',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('39',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('40',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','40'])).

thf('42',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','40'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k1_relat_1 @ X26 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('44',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('47',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('48',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('49',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('50',plain,(
    ! [X11: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('51',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34','40'])).

thf('54',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('55',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('57',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[t45_ordinal1])).

thf('58',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['51','52','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['41','61'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('63',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('67',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X31 ) ) )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('68',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0 = sk_C ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ sk_B @ sk_A )
        | ~ ( v1_xboole_0 @ X0 )
        | ( zip_tseitin_0 @ sk_B @ X1 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ sk_B @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['62','75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_B )
        | ( zip_tseitin_0 @ sk_B @ X0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['30','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('81',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('83',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('84',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('88',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('90',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('91',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('95',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('96',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('98',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['96','97','98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('102',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('103',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['103','104'])).

thf('106',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','105'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('107',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('108',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X48 ) @ X49 )
      | ( v1_funct_2 @ X48 @ ( k1_relat_1 @ X48 ) @ X49 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['106','110'])).

thf('112',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('113',plain,(
    ! [X26: $i] :
      ( ~ ( v2_funct_1 @ X26 )
      | ( ( k1_relat_1 @ X26 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('114',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('120',plain,(
    ! [X19: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('121',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('125',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('126',plain,(
    ! [X19: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X19 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('127',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('129',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','118','124','130'])).

thf('132',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['93','131'])).

thf('133',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['20','132'])).

thf('134',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('135',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','133','134'])).

thf('136',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','135'])).

thf('137',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf(fc14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) )
        & ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ) )).

thf('139',plain,(
    ! [X10: $i] :
      ( ( v1_xboole_0 @ ( k4_relat_1 @ X10 ) )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc14_relat_1])).

thf('140',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('142',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('145',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,
    ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','145'])).

thf('147',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['139','146'])).

thf('148',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_0 @ sk_B @ X0 )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['138','147'])).

thf('149',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('150',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('152',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['17','133','134'])).

thf('154',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['152','153'])).

thf('155',plain,
    ( sk_A
    = ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','154'])).

thf('156',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['107'])).

thf('157',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X48 ) @ X49 )
      | ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X48 ) @ X49 ) ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('158',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['155','158'])).

thf('160',plain,
    ( sk_B
    = ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','105'])).

thf('161',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['121','122','123'])).

thf('162',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('163',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','160','161','162'])).

thf('164',plain,(
    $false ),
    inference(demod,[status(thm)],['136','163'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aItDxTJVgM
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 18:14:21 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 14.50/14.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.50/14.68  % Solved by: fo/fo7.sh
% 14.50/14.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.50/14.68  % done 14465 iterations in 14.205s
% 14.50/14.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.50/14.68  % SZS output start Refutation
% 14.50/14.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 14.50/14.68  thf(sk_A_type, type, sk_A: $i).
% 14.50/14.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 14.50/14.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 14.50/14.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 14.50/14.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 14.50/14.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 14.50/14.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 14.50/14.68  thf(sk_C_type, type, sk_C: $i).
% 14.50/14.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 14.50/14.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 14.50/14.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.50/14.68  thf(v5_ordinal1_type, type, v5_ordinal1: $i > $o).
% 14.50/14.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.50/14.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 14.50/14.68  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 14.50/14.68  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 14.50/14.68  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 14.50/14.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.50/14.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.50/14.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.50/14.68  thf(sk_B_type, type, sk_B: $i).
% 14.50/14.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.50/14.68  thf(t31_funct_2, conjecture,
% 14.50/14.68    (![A:$i,B:$i,C:$i]:
% 14.50/14.68     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 14.50/14.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.50/14.68       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 14.50/14.68         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 14.50/14.68           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 14.50/14.68           ( m1_subset_1 @
% 14.50/14.68             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 14.50/14.68  thf(zf_stmt_0, negated_conjecture,
% 14.50/14.68    (~( ![A:$i,B:$i,C:$i]:
% 14.50/14.68        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 14.50/14.68            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 14.50/14.68          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 14.50/14.68            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 14.50/14.68              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 14.50/14.68              ( m1_subset_1 @
% 14.50/14.68                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 14.50/14.68    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 14.50/14.68  thf('0', plain,
% 14.50/14.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 14.50/14.68        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 14.50/14.68        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.50/14.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf('1', plain,
% 14.50/14.68      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.50/14.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 14.50/14.68         <= (~
% 14.50/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.50/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.50/14.68      inference('split', [status(esa)], ['0'])).
% 14.50/14.68  thf('2', plain,
% 14.50/14.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf(cc1_relset_1, axiom,
% 14.50/14.68    (![A:$i,B:$i,C:$i]:
% 14.50/14.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.50/14.68       ( v1_relat_1 @ C ) ))).
% 14.50/14.68  thf('3', plain,
% 14.50/14.68      (![X28 : $i, X29 : $i, X30 : $i]:
% 14.50/14.68         ((v1_relat_1 @ X28)
% 14.50/14.68          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 14.50/14.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 14.50/14.68  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 14.50/14.68      inference('sup-', [status(thm)], ['2', '3'])).
% 14.50/14.68  thf(d9_funct_1, axiom,
% 14.50/14.68    (![A:$i]:
% 14.50/14.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.50/14.68       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 14.50/14.68  thf('5', plain,
% 14.50/14.68      (![X18 : $i]:
% 14.50/14.68         (~ (v2_funct_1 @ X18)
% 14.50/14.68          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 14.50/14.68          | ~ (v1_funct_1 @ X18)
% 14.50/14.68          | ~ (v1_relat_1 @ X18))),
% 14.50/14.68      inference('cnf', [status(esa)], [d9_funct_1])).
% 14.50/14.68  thf('6', plain,
% 14.50/14.68      ((~ (v1_funct_1 @ sk_C)
% 14.50/14.68        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 14.50/14.68        | ~ (v2_funct_1 @ sk_C))),
% 14.50/14.68      inference('sup-', [status(thm)], ['4', '5'])).
% 14.50/14.68  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.50/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.50/14.68  thf('10', plain,
% 14.50/14.68      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 14.50/14.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 14.50/14.68         <= (~
% 14.50/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.50/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.50/14.68      inference('demod', [status(thm)], ['1', '9'])).
% 14.50/14.68  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 14.50/14.68      inference('sup-', [status(thm)], ['2', '3'])).
% 14.50/14.68  thf(dt_k2_funct_1, axiom,
% 14.50/14.68    (![A:$i]:
% 14.50/14.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.50/14.68       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 14.50/14.68         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 14.50/14.68  thf('12', plain,
% 14.50/14.68      (![X19 : $i]:
% 14.50/14.68         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 14.50/14.68          | ~ (v1_funct_1 @ X19)
% 14.50/14.68          | ~ (v1_relat_1 @ X19))),
% 14.50/14.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 14.50/14.68  thf('13', plain,
% 14.50/14.68      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 14.50/14.68         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 14.50/14.68      inference('split', [status(esa)], ['0'])).
% 14.50/14.68  thf('14', plain,
% 14.50/14.68      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 14.50/14.68         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 14.50/14.68      inference('sup-', [status(thm)], ['12', '13'])).
% 14.50/14.68  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf('16', plain,
% 14.50/14.68      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 14.50/14.68      inference('demod', [status(thm)], ['14', '15'])).
% 14.50/14.68  thf('17', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['11', '16'])).
% 14.50/14.68  thf('18', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.50/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.50/14.68  thf('19', plain,
% 14.50/14.68      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('split', [status(esa)], ['0'])).
% 14.50/14.68  thf('20', plain,
% 14.50/14.68      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['18', '19'])).
% 14.50/14.68  thf(l13_xboole_0, axiom,
% 14.50/14.68    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 14.50/14.68  thf('21', plain,
% 14.50/14.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.50/14.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.50/14.68  thf(t60_relat_1, axiom,
% 14.50/14.68    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 14.50/14.68     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 14.50/14.68  thf('22', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.50/14.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 14.50/14.68  thf(t4_funct_2, axiom,
% 14.50/14.68    (![A:$i,B:$i]:
% 14.50/14.68     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 14.50/14.68       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 14.50/14.68         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 14.50/14.68           ( m1_subset_1 @
% 14.50/14.68             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 14.50/14.68  thf('23', plain,
% 14.50/14.68      (![X48 : $i, X49 : $i]:
% 14.50/14.68         (~ (r1_tarski @ (k2_relat_1 @ X48) @ X49)
% 14.50/14.68          | (v1_funct_2 @ X48 @ (k1_relat_1 @ X48) @ X49)
% 14.50/14.68          | ~ (v1_funct_1 @ X48)
% 14.50/14.68          | ~ (v1_relat_1 @ X48))),
% 14.50/14.68      inference('cnf', [status(esa)], [t4_funct_2])).
% 14.50/14.68  thf('24', plain,
% 14.50/14.68      (![X0 : $i]:
% 14.50/14.68         (~ (r1_tarski @ k1_xboole_0 @ X0)
% 14.50/14.68          | ~ (v1_relat_1 @ k1_xboole_0)
% 14.50/14.68          | ~ (v1_funct_1 @ k1_xboole_0)
% 14.50/14.68          | (v1_funct_2 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 14.50/14.68      inference('sup-', [status(thm)], ['22', '23'])).
% 14.50/14.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 14.50/14.68  thf('25', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 14.50/14.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.50/14.68  thf(t45_ordinal1, axiom,
% 14.50/14.68    (![A:$i]:
% 14.50/14.68     ( ( v5_ordinal1 @ k1_xboole_0 ) & ( v1_funct_1 @ k1_xboole_0 ) & 
% 14.50/14.68       ( v5_relat_1 @ k1_xboole_0 @ A ) & ( v1_relat_1 @ k1_xboole_0 ) ))).
% 14.50/14.68  thf('26', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('27', plain, ((v1_funct_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('28', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.50/14.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 14.50/14.68  thf('29', plain, (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 14.50/14.68      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 14.50/14.68  thf('30', plain,
% 14.50/14.68      (![X0 : $i, X1 : $i]:
% 14.50/14.68         ((v1_funct_2 @ k1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 14.50/14.68      inference('sup+', [status(thm)], ['21', '29'])).
% 14.50/14.68  thf('31', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('32', plain,
% 14.50/14.68      (![X18 : $i]:
% 14.50/14.68         (~ (v2_funct_1 @ X18)
% 14.50/14.68          | ((k2_funct_1 @ X18) = (k4_relat_1 @ X18))
% 14.50/14.68          | ~ (v1_funct_1 @ X18)
% 14.50/14.68          | ~ (v1_relat_1 @ X18))),
% 14.50/14.68      inference('cnf', [status(esa)], [d9_funct_1])).
% 14.50/14.68  thf('33', plain,
% 14.50/14.68      ((~ (v1_funct_1 @ k1_xboole_0)
% 14.50/14.68        | ((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 14.50/14.68        | ~ (v2_funct_1 @ k1_xboole_0))),
% 14.50/14.68      inference('sup-', [status(thm)], ['31', '32'])).
% 14.50/14.68  thf('34', plain, ((v1_funct_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('35', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf(cc2_funct_1, axiom,
% 14.50/14.68    (![A:$i]:
% 14.50/14.68     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.50/14.68       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 14.50/14.68  thf('36', plain,
% 14.50/14.68      (![X17 : $i]:
% 14.50/14.68         ((v2_funct_1 @ X17)
% 14.50/14.68          | ~ (v1_funct_1 @ X17)
% 14.50/14.68          | ~ (v1_relat_1 @ X17)
% 14.50/14.68          | ~ (v1_xboole_0 @ X17))),
% 14.50/14.68      inference('cnf', [status(esa)], [cc2_funct_1])).
% 14.50/14.68  thf('37', plain,
% 14.50/14.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 14.50/14.68        | ~ (v1_funct_1 @ k1_xboole_0)
% 14.50/14.68        | (v2_funct_1 @ k1_xboole_0))),
% 14.50/14.68      inference('sup-', [status(thm)], ['35', '36'])).
% 14.50/14.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 14.50/14.68  thf('38', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 14.50/14.68  thf('39', plain, ((v1_funct_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('40', plain, ((v2_funct_1 @ k1_xboole_0)),
% 14.50/14.68      inference('demod', [status(thm)], ['37', '38', '39'])).
% 14.50/14.68  thf('41', plain, (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 14.50/14.68      inference('demod', [status(thm)], ['33', '34', '40'])).
% 14.50/14.68  thf('42', plain, (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 14.50/14.68      inference('demod', [status(thm)], ['33', '34', '40'])).
% 14.50/14.68  thf(t55_funct_1, axiom,
% 14.50/14.68    (![A:$i]:
% 14.50/14.68     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 14.50/14.68       ( ( v2_funct_1 @ A ) =>
% 14.50/14.68         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 14.50/14.68           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 14.50/14.68  thf('43', plain,
% 14.50/14.68      (![X26 : $i]:
% 14.50/14.68         (~ (v2_funct_1 @ X26)
% 14.50/14.68          | ((k1_relat_1 @ X26) = (k2_relat_1 @ (k2_funct_1 @ X26)))
% 14.50/14.68          | ~ (v1_funct_1 @ X26)
% 14.50/14.68          | ~ (v1_relat_1 @ X26))),
% 14.50/14.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 14.50/14.68  thf('44', plain,
% 14.50/14.68      ((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0)))
% 14.50/14.68        | ~ (v1_relat_1 @ k1_xboole_0)
% 14.50/14.68        | ~ (v1_funct_1 @ k1_xboole_0)
% 14.50/14.68        | ~ (v2_funct_1 @ k1_xboole_0))),
% 14.50/14.68      inference('sup+', [status(thm)], ['42', '43'])).
% 14.50/14.68  thf('45', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.50/14.68      inference('cnf', [status(esa)], [t60_relat_1])).
% 14.50/14.68  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('47', plain, ((v1_funct_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('48', plain, ((v2_funct_1 @ k1_xboole_0)),
% 14.50/14.68      inference('demod', [status(thm)], ['37', '38', '39'])).
% 14.50/14.68  thf('49', plain,
% 14.50/14.68      (((k1_xboole_0) = (k2_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 14.50/14.68      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 14.50/14.68  thf(fc9_relat_1, axiom,
% 14.50/14.68    (![A:$i]:
% 14.50/14.68     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 14.50/14.68       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 14.50/14.68  thf('50', plain,
% 14.50/14.68      (![X11 : $i]:
% 14.50/14.68         (~ (v1_xboole_0 @ (k2_relat_1 @ X11))
% 14.50/14.68          | ~ (v1_relat_1 @ X11)
% 14.50/14.68          | (v1_xboole_0 @ X11))),
% 14.50/14.68      inference('cnf', [status(esa)], [fc9_relat_1])).
% 14.50/14.68  thf('51', plain,
% 14.50/14.68      ((~ (v1_xboole_0 @ k1_xboole_0)
% 14.50/14.68        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))
% 14.50/14.68        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['49', '50'])).
% 14.50/14.68  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 14.50/14.68  thf('53', plain, (((k2_funct_1 @ k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))),
% 14.50/14.68      inference('demod', [status(thm)], ['33', '34', '40'])).
% 14.50/14.68  thf('54', plain,
% 14.50/14.68      (![X19 : $i]:
% 14.50/14.68         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 14.50/14.68          | ~ (v1_funct_1 @ X19)
% 14.50/14.68          | ~ (v1_relat_1 @ X19))),
% 14.50/14.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 14.50/14.68  thf('55', plain,
% 14.50/14.68      (((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 14.50/14.68        | ~ (v1_relat_1 @ k1_xboole_0)
% 14.50/14.68        | ~ (v1_funct_1 @ k1_xboole_0))),
% 14.50/14.68      inference('sup+', [status(thm)], ['53', '54'])).
% 14.50/14.68  thf('56', plain, ((v1_relat_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('57', plain, ((v1_funct_1 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [t45_ordinal1])).
% 14.50/14.68  thf('58', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 14.50/14.68      inference('demod', [status(thm)], ['55', '56', '57'])).
% 14.50/14.68  thf('59', plain, ((v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))),
% 14.50/14.68      inference('demod', [status(thm)], ['51', '52', '58'])).
% 14.50/14.68  thf('60', plain,
% 14.50/14.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.50/14.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.50/14.68  thf('61', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.50/14.68      inference('sup-', [status(thm)], ['59', '60'])).
% 14.50/14.68  thf('62', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 14.50/14.68      inference('demod', [status(thm)], ['41', '61'])).
% 14.50/14.68  thf(d1_funct_2, axiom,
% 14.50/14.68    (![A:$i,B:$i,C:$i]:
% 14.50/14.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.50/14.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.50/14.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 14.50/14.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 14.50/14.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.50/14.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 14.50/14.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 14.50/14.68  thf(zf_stmt_1, axiom,
% 14.50/14.68    (![B:$i,A:$i]:
% 14.50/14.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 14.50/14.68       ( zip_tseitin_0 @ B @ A ) ))).
% 14.50/14.68  thf('63', plain,
% 14.50/14.68      (![X40 : $i, X41 : $i]:
% 14.50/14.68         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 14.50/14.68  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 14.50/14.68  thf('65', plain,
% 14.50/14.68      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 14.50/14.68      inference('sup+', [status(thm)], ['63', '64'])).
% 14.50/14.68  thf('66', plain,
% 14.50/14.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf(cc4_relset_1, axiom,
% 14.50/14.68    (![A:$i,B:$i]:
% 14.50/14.68     ( ( v1_xboole_0 @ A ) =>
% 14.50/14.68       ( ![C:$i]:
% 14.50/14.68         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 14.50/14.68           ( v1_xboole_0 @ C ) ) ) ))).
% 14.50/14.68  thf('67', plain,
% 14.50/14.68      (![X31 : $i, X32 : $i, X33 : $i]:
% 14.50/14.68         (~ (v1_xboole_0 @ X31)
% 14.50/14.68          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X31)))
% 14.50/14.68          | (v1_xboole_0 @ X32))),
% 14.50/14.68      inference('cnf', [status(esa)], [cc4_relset_1])).
% 14.50/14.68  thf('68', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_B))),
% 14.50/14.68      inference('sup-', [status(thm)], ['66', '67'])).
% 14.50/14.68  thf('69', plain,
% 14.50/14.68      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C))),
% 14.50/14.68      inference('sup-', [status(thm)], ['65', '68'])).
% 14.50/14.68  thf('70', plain,
% 14.50/14.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.50/14.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.50/14.68  thf('71', plain,
% 14.50/14.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.50/14.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.50/14.68  thf('72', plain,
% 14.50/14.68      (![X0 : $i, X1 : $i]:
% 14.50/14.68         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 14.50/14.68      inference('sup+', [status(thm)], ['70', '71'])).
% 14.50/14.68  thf('73', plain,
% 14.50/14.68      (![X0 : $i, X1 : $i]:
% 14.50/14.68         ((zip_tseitin_0 @ sk_B @ X1) | ~ (v1_xboole_0 @ X0) | ((X0) = (sk_C)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['69', '72'])).
% 14.50/14.68  thf('74', plain,
% 14.50/14.68      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('split', [status(esa)], ['0'])).
% 14.50/14.68  thf('75', plain,
% 14.50/14.68      ((![X0 : $i, X1 : $i]:
% 14.50/14.68          (~ (v1_funct_2 @ (k2_funct_1 @ X0) @ sk_B @ sk_A)
% 14.50/14.68           | ~ (v1_xboole_0 @ X0)
% 14.50/14.68           | (zip_tseitin_0 @ sk_B @ X1)))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['73', '74'])).
% 14.50/14.68  thf('76', plain,
% 14.50/14.68      ((![X0 : $i]:
% 14.50/14.68          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 14.50/14.68           | (zip_tseitin_0 @ sk_B @ X0)
% 14.50/14.68           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['62', '75'])).
% 14.50/14.68  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 14.50/14.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 14.50/14.68  thf('78', plain,
% 14.50/14.68      ((![X0 : $i]:
% 14.50/14.68          (~ (v1_funct_2 @ k1_xboole_0 @ sk_B @ sk_A)
% 14.50/14.68           | (zip_tseitin_0 @ sk_B @ X0)))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('demod', [status(thm)], ['76', '77'])).
% 14.50/14.68  thf('79', plain,
% 14.50/14.68      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_B) | (zip_tseitin_0 @ sk_B @ X0)))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['30', '78'])).
% 14.50/14.68  thf('80', plain,
% 14.50/14.68      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 14.50/14.68      inference('sup+', [status(thm)], ['63', '64'])).
% 14.50/14.68  thf('81', plain,
% 14.50/14.68      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('clc', [status(thm)], ['79', '80'])).
% 14.50/14.68  thf('82', plain,
% 14.50/14.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 14.50/14.68  thf(zf_stmt_3, axiom,
% 14.50/14.68    (![C:$i,B:$i,A:$i]:
% 14.50/14.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 14.50/14.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 14.50/14.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 14.50/14.68  thf(zf_stmt_5, axiom,
% 14.50/14.68    (![A:$i,B:$i,C:$i]:
% 14.50/14.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.50/14.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 14.50/14.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 14.50/14.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 14.50/14.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 14.50/14.68  thf('83', plain,
% 14.50/14.68      (![X45 : $i, X46 : $i, X47 : $i]:
% 14.50/14.68         (~ (zip_tseitin_0 @ X45 @ X46)
% 14.50/14.68          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 14.50/14.68          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 14.50/14.68  thf('84', plain,
% 14.50/14.68      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 14.50/14.68      inference('sup-', [status(thm)], ['82', '83'])).
% 14.50/14.68  thf('85', plain,
% 14.50/14.68      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['81', '84'])).
% 14.50/14.68  thf('86', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf('87', plain,
% 14.50/14.68      (![X42 : $i, X43 : $i, X44 : $i]:
% 14.50/14.68         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 14.50/14.68          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 14.50/14.68          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 14.50/14.68  thf('88', plain,
% 14.50/14.68      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 14.50/14.68        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['86', '87'])).
% 14.50/14.68  thf('89', plain,
% 14.50/14.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf(redefinition_k1_relset_1, axiom,
% 14.50/14.68    (![A:$i,B:$i,C:$i]:
% 14.50/14.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.50/14.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 14.50/14.68  thf('90', plain,
% 14.50/14.68      (![X34 : $i, X35 : $i, X36 : $i]:
% 14.50/14.68         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 14.50/14.68          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 14.50/14.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 14.50/14.68  thf('91', plain,
% 14.50/14.68      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 14.50/14.68      inference('sup-', [status(thm)], ['89', '90'])).
% 14.50/14.68  thf('92', plain,
% 14.50/14.68      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 14.50/14.68      inference('demod', [status(thm)], ['88', '91'])).
% 14.50/14.68  thf('93', plain,
% 14.50/14.68      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 14.50/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['85', '92'])).
% 14.50/14.68  thf('94', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.50/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.50/14.68  thf('95', plain,
% 14.50/14.68      (![X26 : $i]:
% 14.50/14.68         (~ (v2_funct_1 @ X26)
% 14.50/14.68          | ((k2_relat_1 @ X26) = (k1_relat_1 @ (k2_funct_1 @ X26)))
% 14.50/14.68          | ~ (v1_funct_1 @ X26)
% 14.50/14.68          | ~ (v1_relat_1 @ X26))),
% 14.50/14.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 14.50/14.68  thf('96', plain,
% 14.50/14.68      ((((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))
% 14.50/14.68        | ~ (v1_relat_1 @ sk_C)
% 14.50/14.68        | ~ (v1_funct_1 @ sk_C)
% 14.50/14.68        | ~ (v2_funct_1 @ sk_C))),
% 14.50/14.68      inference('sup+', [status(thm)], ['94', '95'])).
% 14.50/14.68  thf('97', plain, ((v1_relat_1 @ sk_C)),
% 14.50/14.68      inference('sup-', [status(thm)], ['2', '3'])).
% 14.50/14.68  thf('98', plain, ((v1_funct_1 @ sk_C)),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf('100', plain,
% 14.50/14.68      (((k2_relat_1 @ sk_C) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.50/14.68      inference('demod', [status(thm)], ['96', '97', '98', '99'])).
% 14.50/14.68  thf('101', plain,
% 14.50/14.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf(redefinition_k2_relset_1, axiom,
% 14.50/14.68    (![A:$i,B:$i,C:$i]:
% 14.50/14.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 14.50/14.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 14.50/14.68  thf('102', plain,
% 14.50/14.68      (![X37 : $i, X38 : $i, X39 : $i]:
% 14.50/14.68         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 14.50/14.68          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 14.50/14.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 14.50/14.68  thf('103', plain,
% 14.50/14.68      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 14.50/14.68      inference('sup-', [status(thm)], ['101', '102'])).
% 14.50/14.68  thf('104', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 14.50/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.50/14.68  thf('105', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 14.50/14.68      inference('sup+', [status(thm)], ['103', '104'])).
% 14.50/14.68  thf('106', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.50/14.68      inference('demod', [status(thm)], ['100', '105'])).
% 14.50/14.68  thf(d10_xboole_0, axiom,
% 14.50/14.68    (![A:$i,B:$i]:
% 14.50/14.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.50/14.68  thf('107', plain,
% 14.50/14.68      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 14.50/14.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.50/14.68  thf('108', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 14.50/14.68      inference('simplify', [status(thm)], ['107'])).
% 14.50/14.68  thf('109', plain,
% 14.50/14.68      (![X48 : $i, X49 : $i]:
% 14.50/14.68         (~ (r1_tarski @ (k2_relat_1 @ X48) @ X49)
% 14.50/14.68          | (v1_funct_2 @ X48 @ (k1_relat_1 @ X48) @ X49)
% 14.50/14.68          | ~ (v1_funct_1 @ X48)
% 14.50/14.68          | ~ (v1_relat_1 @ X48))),
% 14.50/14.68      inference('cnf', [status(esa)], [t4_funct_2])).
% 14.50/14.68  thf('110', plain,
% 14.50/14.68      (![X0 : $i]:
% 14.50/14.68         (~ (v1_relat_1 @ X0)
% 14.50/14.68          | ~ (v1_funct_1 @ X0)
% 14.50/14.68          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 14.50/14.68      inference('sup-', [status(thm)], ['108', '109'])).
% 14.50/14.68  thf('111', plain,
% 14.50/14.68      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ 
% 14.50/14.68         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 14.50/14.68        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 14.50/14.68        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.50/14.68      inference('sup+', [status(thm)], ['106', '110'])).
% 14.50/14.68  thf('112', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.53/14.68  thf('113', plain,
% 14.53/14.68      (![X26 : $i]:
% 14.53/14.68         (~ (v2_funct_1 @ X26)
% 14.53/14.68          | ((k1_relat_1 @ X26) = (k2_relat_1 @ (k2_funct_1 @ X26)))
% 14.53/14.68          | ~ (v1_funct_1 @ X26)
% 14.53/14.68          | ~ (v1_relat_1 @ X26))),
% 14.53/14.68      inference('cnf', [status(esa)], [t55_funct_1])).
% 14.53/14.68  thf('114', plain,
% 14.53/14.68      ((((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 14.53/14.68        | ~ (v1_relat_1 @ sk_C)
% 14.53/14.68        | ~ (v1_funct_1 @ sk_C)
% 14.53/14.68        | ~ (v2_funct_1 @ sk_C))),
% 14.53/14.68      inference('sup+', [status(thm)], ['112', '113'])).
% 14.53/14.68  thf('115', plain, ((v1_relat_1 @ sk_C)),
% 14.53/14.68      inference('sup-', [status(thm)], ['2', '3'])).
% 14.53/14.68  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 14.53/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.53/14.68  thf('117', plain, ((v2_funct_1 @ sk_C)),
% 14.53/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.53/14.68  thf('118', plain,
% 14.53/14.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.53/14.68      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 14.53/14.68  thf('119', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.53/14.68  thf('120', plain,
% 14.53/14.68      (![X19 : $i]:
% 14.53/14.68         ((v1_funct_1 @ (k2_funct_1 @ X19))
% 14.53/14.68          | ~ (v1_funct_1 @ X19)
% 14.53/14.68          | ~ (v1_relat_1 @ X19))),
% 14.53/14.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 14.53/14.68  thf('121', plain,
% 14.53/14.68      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 14.53/14.68        | ~ (v1_relat_1 @ sk_C)
% 14.53/14.68        | ~ (v1_funct_1 @ sk_C))),
% 14.53/14.68      inference('sup+', [status(thm)], ['119', '120'])).
% 14.53/14.68  thf('122', plain, ((v1_relat_1 @ sk_C)),
% 14.53/14.68      inference('sup-', [status(thm)], ['2', '3'])).
% 14.53/14.68  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 14.53/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.53/14.68  thf('124', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['121', '122', '123'])).
% 14.53/14.68  thf('125', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.53/14.68  thf('126', plain,
% 14.53/14.68      (![X19 : $i]:
% 14.53/14.68         ((v1_relat_1 @ (k2_funct_1 @ X19))
% 14.53/14.68          | ~ (v1_funct_1 @ X19)
% 14.53/14.68          | ~ (v1_relat_1 @ X19))),
% 14.53/14.68      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 14.53/14.68  thf('127', plain,
% 14.53/14.68      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 14.53/14.68        | ~ (v1_relat_1 @ sk_C)
% 14.53/14.68        | ~ (v1_funct_1 @ sk_C))),
% 14.53/14.68      inference('sup+', [status(thm)], ['125', '126'])).
% 14.53/14.68  thf('128', plain, ((v1_relat_1 @ sk_C)),
% 14.53/14.68      inference('sup-', [status(thm)], ['2', '3'])).
% 14.53/14.68  thf('129', plain, ((v1_funct_1 @ sk_C)),
% 14.53/14.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.53/14.68  thf('130', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['127', '128', '129'])).
% 14.53/14.68  thf('131', plain,
% 14.53/14.68      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['111', '118', '124', '130'])).
% 14.53/14.68  thf('132', plain,
% 14.53/14.68      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 14.53/14.68         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 14.53/14.68      inference('sup+', [status(thm)], ['93', '131'])).
% 14.53/14.68  thf('133', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 14.53/14.68      inference('demod', [status(thm)], ['20', '132'])).
% 14.53/14.68  thf('134', plain,
% 14.53/14.68      (~
% 14.53/14.68       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 14.53/14.68       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 14.53/14.68       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 14.53/14.68      inference('split', [status(esa)], ['0'])).
% 14.53/14.68  thf('135', plain,
% 14.53/14.68      (~
% 14.53/14.68       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 14.53/14.68      inference('sat_resolution*', [status(thm)], ['17', '133', '134'])).
% 14.53/14.68  thf('136', plain,
% 14.53/14.68      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 14.53/14.68          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 14.53/14.68      inference('simpl_trail', [status(thm)], ['10', '135'])).
% 14.53/14.68  thf('137', plain,
% 14.53/14.68      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.53/14.68      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 14.53/14.68  thf('138', plain,
% 14.53/14.68      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (v1_xboole_0 @ sk_C))),
% 14.53/14.68      inference('sup-', [status(thm)], ['65', '68'])).
% 14.53/14.68  thf(fc14_relat_1, axiom,
% 14.53/14.68    (![A:$i]:
% 14.53/14.68     ( ( v1_xboole_0 @ A ) =>
% 14.53/14.68       ( ( v1_xboole_0 @ ( k4_relat_1 @ A ) ) & 
% 14.53/14.68         ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) ))).
% 14.53/14.68  thf('139', plain,
% 14.53/14.68      (![X10 : $i]:
% 14.53/14.68         ((v1_xboole_0 @ (k4_relat_1 @ X10)) | ~ (v1_xboole_0 @ X10))),
% 14.53/14.68      inference('cnf', [status(esa)], [fc14_relat_1])).
% 14.53/14.68  thf('140', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['6', '7', '8'])).
% 14.53/14.68  thf('141', plain,
% 14.53/14.68      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 14.53/14.68      inference('cnf', [status(esa)], [l13_xboole_0])).
% 14.53/14.68  thf(t4_subset_1, axiom,
% 14.53/14.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 14.53/14.68  thf('142', plain,
% 14.53/14.68      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X5))),
% 14.53/14.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 14.53/14.68  thf('143', plain,
% 14.53/14.68      (![X0 : $i, X1 : $i]:
% 14.53/14.68         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 14.53/14.68      inference('sup+', [status(thm)], ['141', '142'])).
% 14.53/14.68  thf('144', plain,
% 14.53/14.68      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 14.53/14.68         <= (~
% 14.53/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.53/14.68      inference('split', [status(esa)], ['0'])).
% 14.53/14.68  thf('145', plain,
% 14.53/14.68      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_C)))
% 14.53/14.68         <= (~
% 14.53/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.53/14.68      inference('sup-', [status(thm)], ['143', '144'])).
% 14.53/14.68  thf('146', plain,
% 14.53/14.68      ((~ (v1_xboole_0 @ (k4_relat_1 @ sk_C)))
% 14.53/14.68         <= (~
% 14.53/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.53/14.68      inference('sup-', [status(thm)], ['140', '145'])).
% 14.53/14.68  thf('147', plain,
% 14.53/14.68      ((~ (v1_xboole_0 @ sk_C))
% 14.53/14.68         <= (~
% 14.53/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.53/14.68      inference('sup-', [status(thm)], ['139', '146'])).
% 14.53/14.68  thf('148', plain,
% 14.53/14.68      ((![X0 : $i]: (zip_tseitin_0 @ sk_B @ X0))
% 14.53/14.68         <= (~
% 14.53/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.53/14.68      inference('sup-', [status(thm)], ['138', '147'])).
% 14.53/14.68  thf('149', plain,
% 14.53/14.68      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 14.53/14.68      inference('sup-', [status(thm)], ['82', '83'])).
% 14.53/14.68  thf('150', plain,
% 14.53/14.68      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A))
% 14.53/14.68         <= (~
% 14.53/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.53/14.68      inference('sup-', [status(thm)], ['148', '149'])).
% 14.53/14.68  thf('151', plain,
% 14.53/14.68      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 14.53/14.68      inference('demod', [status(thm)], ['88', '91'])).
% 14.53/14.68  thf('152', plain,
% 14.53/14.68      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 14.53/14.68         <= (~
% 14.53/14.68             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 14.53/14.68      inference('sup-', [status(thm)], ['150', '151'])).
% 14.53/14.68  thf('153', plain,
% 14.53/14.68      (~
% 14.53/14.68       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 14.53/14.68         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 14.53/14.68      inference('sat_resolution*', [status(thm)], ['17', '133', '134'])).
% 14.53/14.68  thf('154', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 14.53/14.68      inference('simpl_trail', [status(thm)], ['152', '153'])).
% 14.53/14.68  thf('155', plain, (((sk_A) = (k2_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.53/14.68      inference('demod', [status(thm)], ['137', '154'])).
% 14.53/14.68  thf('156', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 14.53/14.68      inference('simplify', [status(thm)], ['107'])).
% 14.53/14.68  thf('157', plain,
% 14.53/14.68      (![X48 : $i, X49 : $i]:
% 14.53/14.68         (~ (r1_tarski @ (k2_relat_1 @ X48) @ X49)
% 14.53/14.68          | (m1_subset_1 @ X48 @ 
% 14.53/14.68             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X48) @ X49)))
% 14.53/14.68          | ~ (v1_funct_1 @ X48)
% 14.53/14.68          | ~ (v1_relat_1 @ X48))),
% 14.53/14.68      inference('cnf', [status(esa)], [t4_funct_2])).
% 14.53/14.68  thf('158', plain,
% 14.53/14.68      (![X0 : $i]:
% 14.53/14.68         (~ (v1_relat_1 @ X0)
% 14.53/14.68          | ~ (v1_funct_1 @ X0)
% 14.53/14.68          | (m1_subset_1 @ X0 @ 
% 14.53/14.68             (k1_zfmisc_1 @ 
% 14.53/14.68              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 14.53/14.68      inference('sup-', [status(thm)], ['156', '157'])).
% 14.53/14.68  thf('159', plain,
% 14.53/14.68      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 14.53/14.68         (k1_zfmisc_1 @ 
% 14.53/14.68          (k2_zfmisc_1 @ (k1_relat_1 @ (k4_relat_1 @ sk_C)) @ sk_A)))
% 14.53/14.68        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 14.53/14.68        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.53/14.68      inference('sup+', [status(thm)], ['155', '158'])).
% 14.53/14.68  thf('160', plain, (((sk_B) = (k1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 14.53/14.68      inference('demod', [status(thm)], ['100', '105'])).
% 14.53/14.68  thf('161', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['121', '122', '123'])).
% 14.53/14.68  thf('162', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 14.53/14.68      inference('demod', [status(thm)], ['127', '128', '129'])).
% 14.53/14.68  thf('163', plain,
% 14.53/14.68      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 14.53/14.68        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 14.53/14.68      inference('demod', [status(thm)], ['159', '160', '161', '162'])).
% 14.53/14.68  thf('164', plain, ($false), inference('demod', [status(thm)], ['136', '163'])).
% 14.53/14.68  
% 14.53/14.68  % SZS output end Refutation
% 14.53/14.68  
% 14.53/14.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
