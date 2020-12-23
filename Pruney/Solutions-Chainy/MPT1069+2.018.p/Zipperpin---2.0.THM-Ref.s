%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3GR9KsGttf

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:03 EST 2020

% Result     : Theorem 29.20s
% Output     : Refutation 29.20s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 305 expanded)
%              Number of leaves         :   47 ( 109 expanded)
%              Depth                    :   16
%              Number of atoms          : 1400 (5601 expanded)
%              Number of equality atoms :   59 ( 223 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t186_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ~ ( v1_xboole_0 @ C )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
           => ! [E: $i] :
                ( ( ( v1_funct_1 @ E )
                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
               => ! [F: $i] :
                    ( ( m1_subset_1 @ F @ B )
                   => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                     => ( ( B = k1_xboole_0 )
                        | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                          = ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_funct_2])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X30 ) @ X31 )
      | ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_B @ sk_D ) @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['7','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(condensation,[status(thm)],['22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc6_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ~ ( v1_xboole_0 @ C )
              & ( v1_funct_2 @ C @ A @ B ) ) ) ) ) )).

thf('25',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ~ ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc6_funct_2])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('33',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['31','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['23','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r2_hidden @ X13 @ X14 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ sk_F @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('simplify_reflect+',[status(thm)],['35','36'])).

thf('47',plain,(
    r2_hidden @ sk_F @ sk_B_1 ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(t7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf('49',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i] :
      ( ~ ( r2_hidden @ X52 @ X53 )
      | ( X54 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_funct_2 @ X55 @ X53 @ X54 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X55 @ X52 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[t7_funct_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('52',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_partfun1 @ X34 @ X35 )
      | ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('53',plain,
    ( ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_partfun1 @ sk_D @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v1_funct_2 @ sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_partfun1 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
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

thf('57',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ( v1_partfun1 @ X37 @ X38 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( v1_funct_1 @ X37 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
    | ( v1_partfun1 @ sk_D @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_partfun1 @ sk_D @ sk_B_1 ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_partfun1 @ sk_D @ sk_B_1 ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['55','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['50','64','65'])).

thf('67',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','66'])).

thf('68',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('71',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('74',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('75',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_E ) )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['67','78'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('80',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k1_relat_1 @ X44 ) )
      | ( ( k7_partfun1 @ X45 @ X44 @ X43 )
        = ( k1_funct_1 @ X44 @ X43 ) )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v5_relat_1 @ X44 @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('83',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('84',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['81','84','85'])).

thf('87',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','86'])).

thf('88',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    m1_subset_1 @ sk_F @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_C_1 @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('91',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( m1_subset_1 @ X49 @ X47 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X47 @ X48 @ X51 @ X46 @ X50 ) @ X49 )
        = ( k1_funct_1 @ X50 @ ( k1_funct_1 @ X46 @ X49 ) ) )
      | ( X47 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X47 @ X48 @ X46 ) @ ( k1_relset_1 @ X48 @ X51 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X51 ) ) )
      | ~ ( v1_funct_1 @ X50 )
      | ( v1_xboole_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('95',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( sk_B_1 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C_1 @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['72','75'])).

thf('102',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['89','106'])).

thf('108',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['88','107'])).

thf('109',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','108'])).

thf('110',plain,
    ( ( k2_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['109'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('111',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_zfmisc_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ( X12 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('112',plain,(
    ! [X11: $i] :
      ( ( k2_zfmisc_1 @ X11 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['39','110','112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3GR9KsGttf
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 29.20/29.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 29.20/29.38  % Solved by: fo/fo7.sh
% 29.20/29.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 29.20/29.38  % done 6368 iterations in 28.925s
% 29.20/29.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 29.20/29.38  % SZS output start Refutation
% 29.20/29.38  thf(sk_F_type, type, sk_F: $i).
% 29.20/29.38  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 29.20/29.38  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 29.20/29.38  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 29.20/29.38  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 29.20/29.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 29.20/29.38  thf(sk_A_type, type, sk_A: $i).
% 29.20/29.38  thf(sk_E_type, type, sk_E: $i).
% 29.20/29.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 29.20/29.38  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 29.20/29.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 29.20/29.38  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 29.20/29.38  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 29.20/29.38  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 29.20/29.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 29.20/29.38  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 29.20/29.38  thf(sk_B_type, type, sk_B: $i > $i).
% 29.20/29.38  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 29.20/29.38  thf(sk_C_1_type, type, sk_C_1: $i).
% 29.20/29.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 29.20/29.38  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 29.20/29.38  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 29.20/29.38  thf(sk_D_type, type, sk_D: $i).
% 29.20/29.38  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 29.20/29.38  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 29.20/29.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 29.20/29.38  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 29.20/29.38  thf(sk_B_1_type, type, sk_B_1: $i).
% 29.20/29.38  thf(d3_tarski, axiom,
% 29.20/29.38    (![A:$i,B:$i]:
% 29.20/29.38     ( ( r1_tarski @ A @ B ) <=>
% 29.20/29.38       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 29.20/29.38  thf('0', plain,
% 29.20/29.38      (![X4 : $i, X6 : $i]:
% 29.20/29.38         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 29.20/29.38      inference('cnf', [status(esa)], [d3_tarski])).
% 29.20/29.38  thf(d1_xboole_0, axiom,
% 29.20/29.38    (![A:$i]:
% 29.20/29.38     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 29.20/29.38  thf('1', plain,
% 29.20/29.38      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 29.20/29.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 29.20/29.38  thf('2', plain,
% 29.20/29.38      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 29.20/29.38      inference('sup-', [status(thm)], ['0', '1'])).
% 29.20/29.38  thf('3', plain,
% 29.20/29.38      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 29.20/29.38      inference('sup-', [status(thm)], ['0', '1'])).
% 29.20/29.38  thf(d10_xboole_0, axiom,
% 29.20/29.38    (![A:$i,B:$i]:
% 29.20/29.38     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 29.20/29.38  thf('4', plain,
% 29.20/29.38      (![X7 : $i, X9 : $i]:
% 29.20/29.38         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 29.20/29.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.20/29.38  thf('5', plain,
% 29.20/29.38      (![X0 : $i, X1 : $i]:
% 29.20/29.38         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 29.20/29.38      inference('sup-', [status(thm)], ['3', '4'])).
% 29.20/29.38  thf('6', plain,
% 29.20/29.38      (![X0 : $i, X1 : $i]:
% 29.20/29.38         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 29.20/29.38      inference('sup-', [status(thm)], ['2', '5'])).
% 29.20/29.38  thf('7', plain,
% 29.20/29.38      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 29.20/29.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 29.20/29.38  thf('8', plain,
% 29.20/29.38      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 29.20/29.38      inference('cnf', [status(esa)], [d10_xboole_0])).
% 29.20/29.38  thf('9', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 29.20/29.38      inference('simplify', [status(thm)], ['8'])).
% 29.20/29.38  thf(t186_funct_2, conjecture,
% 29.20/29.38    (![A:$i,B:$i,C:$i]:
% 29.20/29.38     ( ( ~( v1_xboole_0 @ C ) ) =>
% 29.20/29.38       ( ![D:$i]:
% 29.20/29.38         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 29.20/29.38             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 29.20/29.38           ( ![E:$i]:
% 29.20/29.38             ( ( ( v1_funct_1 @ E ) & 
% 29.20/29.38                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 29.20/29.38               ( ![F:$i]:
% 29.20/29.38                 ( ( m1_subset_1 @ F @ B ) =>
% 29.20/29.38                   ( ( r1_tarski @
% 29.20/29.38                       ( k2_relset_1 @ B @ C @ D ) @ 
% 29.20/29.38                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 29.20/29.38                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.20/29.38                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 29.20/29.38                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 29.20/29.38  thf(zf_stmt_0, negated_conjecture,
% 29.20/29.38    (~( ![A:$i,B:$i,C:$i]:
% 29.20/29.38        ( ( ~( v1_xboole_0 @ C ) ) =>
% 29.20/29.38          ( ![D:$i]:
% 29.20/29.38            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 29.20/29.38                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 29.20/29.38              ( ![E:$i]:
% 29.20/29.38                ( ( ( v1_funct_1 @ E ) & 
% 29.20/29.38                    ( m1_subset_1 @
% 29.20/29.38                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 29.20/29.38                  ( ![F:$i]:
% 29.20/29.38                    ( ( m1_subset_1 @ F @ B ) =>
% 29.20/29.38                      ( ( r1_tarski @
% 29.20/29.38                          ( k2_relset_1 @ B @ C @ D ) @ 
% 29.20/29.38                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 29.20/29.38                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.20/29.38                          ( ( k1_funct_1 @
% 29.20/29.38                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 29.20/29.38                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 29.20/29.38    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 29.20/29.38  thf('10', plain,
% 29.20/29.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf(t14_relset_1, axiom,
% 29.20/29.38    (![A:$i,B:$i,C:$i,D:$i]:
% 29.20/29.38     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 29.20/29.38       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 29.20/29.38         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 29.20/29.38  thf('11', plain,
% 29.20/29.38      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 29.20/29.38         (~ (r1_tarski @ (k2_relat_1 @ X30) @ X31)
% 29.20/29.38          | (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 29.20/29.38          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 29.20/29.38      inference('cnf', [status(esa)], [t14_relset_1])).
% 29.20/29.38  thf('12', plain,
% 29.20/29.38      (![X0 : $i]:
% 29.20/29.38         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ X0)))
% 29.20/29.38          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 29.20/29.38      inference('sup-', [status(thm)], ['10', '11'])).
% 29.20/29.38  thf('13', plain,
% 29.20/29.38      ((m1_subset_1 @ sk_D @ 
% 29.20/29.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D))))),
% 29.20/29.38      inference('sup-', [status(thm)], ['9', '12'])).
% 29.20/29.38  thf(t3_subset, axiom,
% 29.20/29.38    (![A:$i,B:$i]:
% 29.20/29.38     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 29.20/29.38  thf('14', plain,
% 29.20/29.38      (![X15 : $i, X16 : $i]:
% 29.20/29.38         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 29.20/29.38      inference('cnf', [status(esa)], [t3_subset])).
% 29.20/29.38  thf('15', plain,
% 29.20/29.38      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D)))),
% 29.20/29.38      inference('sup-', [status(thm)], ['13', '14'])).
% 29.20/29.38  thf('16', plain,
% 29.20/29.38      (![X3 : $i, X4 : $i, X5 : $i]:
% 29.20/29.38         (~ (r2_hidden @ X3 @ X4)
% 29.20/29.38          | (r2_hidden @ X3 @ X5)
% 29.20/29.38          | ~ (r1_tarski @ X4 @ X5))),
% 29.20/29.38      inference('cnf', [status(esa)], [d3_tarski])).
% 29.20/29.38  thf('17', plain,
% 29.20/29.38      (![X0 : $i]:
% 29.20/29.38         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D)))
% 29.20/29.38          | ~ (r2_hidden @ X0 @ sk_D))),
% 29.20/29.38      inference('sup-', [status(thm)], ['15', '16'])).
% 29.20/29.38  thf('18', plain,
% 29.20/29.38      (((v1_xboole_0 @ sk_D)
% 29.20/29.38        | (r2_hidden @ (sk_B @ sk_D) @ 
% 29.20/29.38           (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D))))),
% 29.20/29.38      inference('sup-', [status(thm)], ['7', '17'])).
% 29.20/29.38  thf('19', plain,
% 29.20/29.38      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 29.20/29.38      inference('cnf', [status(esa)], [d1_xboole_0])).
% 29.20/29.38  thf('20', plain,
% 29.20/29.38      (((v1_xboole_0 @ sk_D)
% 29.20/29.38        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D))))),
% 29.20/29.38      inference('sup-', [status(thm)], ['18', '19'])).
% 29.20/29.38  thf('21', plain,
% 29.20/29.38      (![X0 : $i]:
% 29.20/29.38         (~ (v1_xboole_0 @ X0)
% 29.20/29.38          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D)))
% 29.20/29.38          | ~ (v1_xboole_0 @ X0)
% 29.20/29.38          | (v1_xboole_0 @ sk_D))),
% 29.20/29.38      inference('sup-', [status(thm)], ['6', '20'])).
% 29.20/29.38  thf('22', plain,
% 29.20/29.38      (![X0 : $i]:
% 29.20/29.38         ((v1_xboole_0 @ sk_D)
% 29.20/29.38          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D)))
% 29.20/29.38          | ~ (v1_xboole_0 @ X0))),
% 29.20/29.38      inference('simplify', [status(thm)], ['21'])).
% 29.20/29.38  thf('23', plain,
% 29.20/29.38      (((v1_xboole_0 @ sk_D)
% 29.20/29.38        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D))))),
% 29.20/29.38      inference('condensation', [status(thm)], ['22'])).
% 29.20/29.38  thf('24', plain,
% 29.20/29.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf(cc6_funct_2, axiom,
% 29.20/29.38    (![A:$i,B:$i]:
% 29.20/29.38     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 29.20/29.38       ( ![C:$i]:
% 29.20/29.38         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.20/29.38           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 29.20/29.38             ( ( v1_funct_1 @ C ) & ( ~( v1_xboole_0 @ C ) ) & 
% 29.20/29.38               ( v1_funct_2 @ C @ A @ B ) ) ) ) ) ))).
% 29.20/29.38  thf('25', plain,
% 29.20/29.38      (![X40 : $i, X41 : $i, X42 : $i]:
% 29.20/29.38         ((v1_xboole_0 @ X40)
% 29.20/29.38          | (v1_xboole_0 @ X41)
% 29.20/29.38          | ~ (v1_funct_1 @ X42)
% 29.20/29.38          | ~ (v1_funct_2 @ X42 @ X40 @ X41)
% 29.20/29.38          | ~ (v1_xboole_0 @ X42)
% 29.20/29.38          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 29.20/29.38      inference('cnf', [status(esa)], [cc6_funct_2])).
% 29.20/29.38  thf('26', plain,
% 29.20/29.38      ((~ (v1_xboole_0 @ sk_D)
% 29.20/29.38        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 29.20/29.38        | ~ (v1_funct_1 @ sk_D)
% 29.20/29.38        | (v1_xboole_0 @ sk_C_1)
% 29.20/29.38        | (v1_xboole_0 @ sk_B_1))),
% 29.20/29.38      inference('sup-', [status(thm)], ['24', '25'])).
% 29.20/29.38  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf('29', plain,
% 29.20/29.38      ((~ (v1_xboole_0 @ sk_D)
% 29.20/29.38        | (v1_xboole_0 @ sk_C_1)
% 29.20/29.38        | (v1_xboole_0 @ sk_B_1))),
% 29.20/29.38      inference('demod', [status(thm)], ['26', '27', '28'])).
% 29.20/29.38  thf('30', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf('31', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_D))),
% 29.20/29.38      inference('clc', [status(thm)], ['29', '30'])).
% 29.20/29.38  thf('32', plain,
% 29.20/29.38      (![X0 : $i, X1 : $i]:
% 29.20/29.38         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 29.20/29.38      inference('sup-', [status(thm)], ['2', '5'])).
% 29.20/29.38  thf('33', plain, (((sk_B_1) != (k1_xboole_0))),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf('34', plain,
% 29.20/29.38      (![X0 : $i]:
% 29.20/29.38         (((X0) != (k1_xboole_0))
% 29.20/29.38          | ~ (v1_xboole_0 @ sk_B_1)
% 29.20/29.38          | ~ (v1_xboole_0 @ X0))),
% 29.20/29.38      inference('sup-', [status(thm)], ['32', '33'])).
% 29.20/29.38  thf('35', plain,
% 29.20/29.38      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1))),
% 29.20/29.38      inference('simplify', [status(thm)], ['34'])).
% 29.20/29.38  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 29.20/29.38  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 29.20/29.38      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 29.20/29.38  thf('37', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 29.20/29.38      inference('simplify_reflect+', [status(thm)], ['35', '36'])).
% 29.20/29.38  thf('38', plain, (~ (v1_xboole_0 @ sk_D)),
% 29.20/29.38      inference('clc', [status(thm)], ['31', '37'])).
% 29.20/29.38  thf('39', plain,
% 29.20/29.38      (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D)))),
% 29.20/29.38      inference('clc', [status(thm)], ['23', '38'])).
% 29.20/29.38  thf('40', plain,
% 29.20/29.38      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf(cc2_relset_1, axiom,
% 29.20/29.38    (![A:$i,B:$i,C:$i]:
% 29.20/29.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.20/29.38       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 29.20/29.38  thf('41', plain,
% 29.20/29.38      (![X21 : $i, X22 : $i, X23 : $i]:
% 29.20/29.38         ((v5_relat_1 @ X21 @ X23)
% 29.20/29.38          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 29.20/29.38      inference('cnf', [status(esa)], [cc2_relset_1])).
% 29.20/29.38  thf('42', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 29.20/29.38      inference('sup-', [status(thm)], ['40', '41'])).
% 29.20/29.38  thf('43', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf(t2_subset, axiom,
% 29.20/29.38    (![A:$i,B:$i]:
% 29.20/29.38     ( ( m1_subset_1 @ A @ B ) =>
% 29.20/29.38       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 29.20/29.38  thf('44', plain,
% 29.20/29.38      (![X13 : $i, X14 : $i]:
% 29.20/29.38         ((r2_hidden @ X13 @ X14)
% 29.20/29.38          | (v1_xboole_0 @ X14)
% 29.20/29.38          | ~ (m1_subset_1 @ X13 @ X14))),
% 29.20/29.38      inference('cnf', [status(esa)], [t2_subset])).
% 29.20/29.38  thf('45', plain, (((v1_xboole_0 @ sk_B_1) | (r2_hidden @ sk_F @ sk_B_1))),
% 29.20/29.38      inference('sup-', [status(thm)], ['43', '44'])).
% 29.20/29.38  thf('46', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 29.20/29.38      inference('simplify_reflect+', [status(thm)], ['35', '36'])).
% 29.20/29.38  thf('47', plain, ((r2_hidden @ sk_F @ sk_B_1)),
% 29.20/29.38      inference('clc', [status(thm)], ['45', '46'])).
% 29.20/29.38  thf('48', plain,
% 29.20/29.38      ((m1_subset_1 @ sk_D @ 
% 29.20/29.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D))))),
% 29.20/29.38      inference('sup-', [status(thm)], ['9', '12'])).
% 29.20/29.38  thf(t7_funct_2, axiom,
% 29.20/29.38    (![A:$i,B:$i,C:$i,D:$i]:
% 29.20/29.38     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 29.20/29.38         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 29.20/29.38       ( ( r2_hidden @ C @ A ) =>
% 29.20/29.38         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.20/29.38           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 29.20/29.38  thf('49', plain,
% 29.20/29.38      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i]:
% 29.20/29.38         (~ (r2_hidden @ X52 @ X53)
% 29.20/29.38          | ((X54) = (k1_xboole_0))
% 29.20/29.38          | ~ (v1_funct_1 @ X55)
% 29.20/29.38          | ~ (v1_funct_2 @ X55 @ X53 @ X54)
% 29.20/29.38          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 29.20/29.38          | (r2_hidden @ (k1_funct_1 @ X55 @ X52) @ X54))),
% 29.20/29.38      inference('cnf', [status(esa)], [t7_funct_2])).
% 29.20/29.38  thf('50', plain,
% 29.20/29.38      (![X0 : $i]:
% 29.20/29.38         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 29.20/29.38          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ (k2_relat_1 @ sk_D))
% 29.20/29.38          | ~ (v1_funct_1 @ sk_D)
% 29.20/29.38          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 29.20/29.38          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 29.20/29.38      inference('sup-', [status(thm)], ['48', '49'])).
% 29.20/29.38  thf('51', plain,
% 29.20/29.38      ((m1_subset_1 @ sk_D @ 
% 29.20/29.38        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ (k2_relat_1 @ sk_D))))),
% 29.20/29.38      inference('sup-', [status(thm)], ['9', '12'])).
% 29.20/29.38  thf(cc1_funct_2, axiom,
% 29.20/29.38    (![A:$i,B:$i,C:$i]:
% 29.20/29.38     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.20/29.38       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 29.20/29.38         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 29.20/29.38  thf('52', plain,
% 29.20/29.38      (![X34 : $i, X35 : $i, X36 : $i]:
% 29.20/29.38         (~ (v1_funct_1 @ X34)
% 29.20/29.38          | ~ (v1_partfun1 @ X34 @ X35)
% 29.20/29.38          | (v1_funct_2 @ X34 @ X35 @ X36)
% 29.20/29.38          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 29.20/29.38      inference('cnf', [status(esa)], [cc1_funct_2])).
% 29.20/29.38  thf('53', plain,
% 29.20/29.38      (((v1_funct_2 @ sk_D @ sk_B_1 @ (k2_relat_1 @ sk_D))
% 29.20/29.38        | ~ (v1_partfun1 @ sk_D @ sk_B_1)
% 29.20/29.38        | ~ (v1_funct_1 @ sk_D))),
% 29.20/29.38      inference('sup-', [status(thm)], ['51', '52'])).
% 29.20/29.38  thf('54', plain, ((v1_funct_1 @ sk_D)),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf('55', plain,
% 29.20/29.38      (((v1_funct_2 @ sk_D @ sk_B_1 @ (k2_relat_1 @ sk_D))
% 29.20/29.38        | ~ (v1_partfun1 @ sk_D @ sk_B_1))),
% 29.20/29.38      inference('demod', [status(thm)], ['53', '54'])).
% 29.20/29.38  thf('56', plain,
% 29.20/29.38      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf(cc5_funct_2, axiom,
% 29.20/29.38    (![A:$i,B:$i]:
% 29.20/29.38     ( ( ~( v1_xboole_0 @ B ) ) =>
% 29.20/29.38       ( ![C:$i]:
% 29.20/29.38         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.20/29.38           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 29.20/29.38             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 29.20/29.38  thf('57', plain,
% 29.20/29.38      (![X37 : $i, X38 : $i, X39 : $i]:
% 29.20/29.38         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 29.20/29.38          | (v1_partfun1 @ X37 @ X38)
% 29.20/29.38          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 29.20/29.38          | ~ (v1_funct_1 @ X37)
% 29.20/29.38          | (v1_xboole_0 @ X39))),
% 29.20/29.38      inference('cnf', [status(esa)], [cc5_funct_2])).
% 29.20/29.38  thf('58', plain,
% 29.20/29.38      (((v1_xboole_0 @ sk_C_1)
% 29.20/29.38        | ~ (v1_funct_1 @ sk_D)
% 29.20/29.38        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 29.20/29.38        | (v1_partfun1 @ sk_D @ sk_B_1))),
% 29.20/29.38      inference('sup-', [status(thm)], ['56', '57'])).
% 29.20/29.38  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 29.20/29.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.38  thf('61', plain, (((v1_xboole_0 @ sk_C_1) | (v1_partfun1 @ sk_D @ sk_B_1))),
% 29.20/29.38      inference('demod', [status(thm)], ['58', '59', '60'])).
% 29.20/29.38  thf('62', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('63', plain, ((v1_partfun1 @ sk_D @ sk_B_1)),
% 29.20/29.39      inference('clc', [status(thm)], ['61', '62'])).
% 29.20/29.39  thf('64', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ (k2_relat_1 @ sk_D))),
% 29.20/29.39      inference('demod', [status(thm)], ['55', '63'])).
% 29.20/29.39  thf('65', plain, ((v1_funct_1 @ sk_D)),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('66', plain,
% 29.20/29.39      (![X0 : $i]:
% 29.20/29.39         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 29.20/29.39          | ((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 29.20/29.39          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 29.20/29.39      inference('demod', [status(thm)], ['50', '64', '65'])).
% 29.20/29.39  thf('67', plain,
% 29.20/29.39      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 29.20/29.39        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D)))),
% 29.20/29.39      inference('sup-', [status(thm)], ['47', '66'])).
% 29.20/29.39  thf('68', plain,
% 29.20/29.39      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 29.20/29.39        (k1_relset_1 @ sk_C_1 @ sk_A @ sk_E))),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('69', plain,
% 29.20/29.39      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf(redefinition_k1_relset_1, axiom,
% 29.20/29.39    (![A:$i,B:$i,C:$i]:
% 29.20/29.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.20/29.39       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 29.20/29.39  thf('70', plain,
% 29.20/29.39      (![X24 : $i, X25 : $i, X26 : $i]:
% 29.20/29.39         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 29.20/29.39          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 29.20/29.39      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 29.20/29.39  thf('71', plain,
% 29.20/29.39      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 29.20/29.39      inference('sup-', [status(thm)], ['69', '70'])).
% 29.20/29.39  thf('72', plain,
% 29.20/29.39      ((r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 29.20/29.39        (k1_relat_1 @ sk_E))),
% 29.20/29.39      inference('demod', [status(thm)], ['68', '71'])).
% 29.20/29.39  thf('73', plain,
% 29.20/29.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf(redefinition_k2_relset_1, axiom,
% 29.20/29.39    (![A:$i,B:$i,C:$i]:
% 29.20/29.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.20/29.39       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 29.20/29.39  thf('74', plain,
% 29.20/29.39      (![X27 : $i, X28 : $i, X29 : $i]:
% 29.20/29.39         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 29.20/29.39          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 29.20/29.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 29.20/29.39  thf('75', plain,
% 29.20/29.39      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 29.20/29.39      inference('sup-', [status(thm)], ['73', '74'])).
% 29.20/29.39  thf('76', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 29.20/29.39      inference('demod', [status(thm)], ['72', '75'])).
% 29.20/29.39  thf('77', plain,
% 29.20/29.39      (![X3 : $i, X4 : $i, X5 : $i]:
% 29.20/29.39         (~ (r2_hidden @ X3 @ X4)
% 29.20/29.39          | (r2_hidden @ X3 @ X5)
% 29.20/29.39          | ~ (r1_tarski @ X4 @ X5))),
% 29.20/29.39      inference('cnf', [status(esa)], [d3_tarski])).
% 29.20/29.39  thf('78', plain,
% 29.20/29.39      (![X0 : $i]:
% 29.20/29.39         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_E))
% 29.20/29.39          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D)))),
% 29.20/29.39      inference('sup-', [status(thm)], ['76', '77'])).
% 29.20/29.39  thf('79', plain,
% 29.20/29.39      ((((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 29.20/29.39        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E)))),
% 29.20/29.39      inference('sup-', [status(thm)], ['67', '78'])).
% 29.20/29.39  thf(d8_partfun1, axiom,
% 29.20/29.39    (![A:$i,B:$i]:
% 29.20/29.39     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 29.20/29.39       ( ![C:$i]:
% 29.20/29.39         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 29.20/29.39           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 29.20/29.39  thf('80', plain,
% 29.20/29.39      (![X43 : $i, X44 : $i, X45 : $i]:
% 29.20/29.39         (~ (r2_hidden @ X43 @ (k1_relat_1 @ X44))
% 29.20/29.39          | ((k7_partfun1 @ X45 @ X44 @ X43) = (k1_funct_1 @ X44 @ X43))
% 29.20/29.39          | ~ (v1_funct_1 @ X44)
% 29.20/29.39          | ~ (v5_relat_1 @ X44 @ X45)
% 29.20/29.39          | ~ (v1_relat_1 @ X44))),
% 29.20/29.39      inference('cnf', [status(esa)], [d8_partfun1])).
% 29.20/29.39  thf('81', plain,
% 29.20/29.39      (![X0 : $i]:
% 29.20/29.39         (((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 29.20/29.39          | ~ (v1_relat_1 @ sk_E)
% 29.20/29.39          | ~ (v5_relat_1 @ sk_E @ X0)
% 29.20/29.39          | ~ (v1_funct_1 @ sk_E)
% 29.20/29.39          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 29.20/29.39              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 29.20/29.39      inference('sup-', [status(thm)], ['79', '80'])).
% 29.20/29.39  thf('82', plain,
% 29.20/29.39      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf(cc1_relset_1, axiom,
% 29.20/29.39    (![A:$i,B:$i,C:$i]:
% 29.20/29.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 29.20/29.39       ( v1_relat_1 @ C ) ))).
% 29.20/29.39  thf('83', plain,
% 29.20/29.39      (![X18 : $i, X19 : $i, X20 : $i]:
% 29.20/29.39         ((v1_relat_1 @ X18)
% 29.20/29.39          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 29.20/29.39      inference('cnf', [status(esa)], [cc1_relset_1])).
% 29.20/29.39  thf('84', plain, ((v1_relat_1 @ sk_E)),
% 29.20/29.39      inference('sup-', [status(thm)], ['82', '83'])).
% 29.20/29.39  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('86', plain,
% 29.20/29.39      (![X0 : $i]:
% 29.20/29.39         (((k2_relat_1 @ sk_D) = (k1_xboole_0))
% 29.20/29.39          | ~ (v5_relat_1 @ sk_E @ X0)
% 29.20/29.39          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 29.20/29.39              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 29.20/29.39      inference('demod', [status(thm)], ['81', '84', '85'])).
% 29.20/29.39  thf('87', plain,
% 29.20/29.39      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 29.20/29.39          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 29.20/29.39        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 29.20/29.39      inference('sup-', [status(thm)], ['42', '86'])).
% 29.20/29.39  thf('88', plain,
% 29.20/29.39      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 29.20/29.39         sk_F) != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('89', plain, ((m1_subset_1 @ sk_F @ sk_B_1)),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('90', plain,
% 29.20/29.39      (((k1_relset_1 @ sk_C_1 @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 29.20/29.39      inference('sup-', [status(thm)], ['69', '70'])).
% 29.20/29.39  thf('91', plain,
% 29.20/29.39      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf(t185_funct_2, axiom,
% 29.20/29.39    (![A:$i,B:$i,C:$i]:
% 29.20/29.39     ( ( ~( v1_xboole_0 @ C ) ) =>
% 29.20/29.39       ( ![D:$i]:
% 29.20/29.39         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 29.20/29.39             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 29.20/29.39           ( ![E:$i]:
% 29.20/29.39             ( ( ( v1_funct_1 @ E ) & 
% 29.20/29.39                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 29.20/29.39               ( ![F:$i]:
% 29.20/29.39                 ( ( m1_subset_1 @ F @ B ) =>
% 29.20/29.39                   ( ( r1_tarski @
% 29.20/29.39                       ( k2_relset_1 @ B @ C @ D ) @ 
% 29.20/29.39                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 29.20/29.39                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 29.20/29.39                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 29.20/29.39                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 29.20/29.39  thf('92', plain,
% 29.20/29.39      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 29.20/29.39         (~ (v1_funct_1 @ X46)
% 29.20/29.39          | ~ (v1_funct_2 @ X46 @ X47 @ X48)
% 29.20/29.39          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 29.20/29.39          | ~ (m1_subset_1 @ X49 @ X47)
% 29.20/29.39          | ((k1_funct_1 @ (k8_funct_2 @ X47 @ X48 @ X51 @ X46 @ X50) @ X49)
% 29.20/29.39              = (k1_funct_1 @ X50 @ (k1_funct_1 @ X46 @ X49)))
% 29.20/29.39          | ((X47) = (k1_xboole_0))
% 29.20/29.39          | ~ (r1_tarski @ (k2_relset_1 @ X47 @ X48 @ X46) @ 
% 29.20/29.39               (k1_relset_1 @ X48 @ X51 @ X50))
% 29.20/29.39          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X51)))
% 29.20/29.39          | ~ (v1_funct_1 @ X50)
% 29.20/29.39          | (v1_xboole_0 @ X48))),
% 29.20/29.39      inference('cnf', [status(esa)], [t185_funct_2])).
% 29.20/29.39  thf('93', plain,
% 29.20/29.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.20/29.39         ((v1_xboole_0 @ sk_C_1)
% 29.20/29.39          | ~ (v1_funct_1 @ X0)
% 29.20/29.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 29.20/29.39          | ~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) @ 
% 29.20/29.39               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 29.20/29.39          | ((sk_B_1) = (k1_xboole_0))
% 29.20/29.39          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 29.20/29.39              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 29.20/29.39          | ~ (m1_subset_1 @ X2 @ sk_B_1)
% 29.20/29.39          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)
% 29.20/29.39          | ~ (v1_funct_1 @ sk_D))),
% 29.20/29.39      inference('sup-', [status(thm)], ['91', '92'])).
% 29.20/29.39  thf('94', plain,
% 29.20/29.39      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D) = (k2_relat_1 @ sk_D))),
% 29.20/29.39      inference('sup-', [status(thm)], ['73', '74'])).
% 29.20/29.39  thf('95', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_C_1)),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('96', plain, ((v1_funct_1 @ sk_D)),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('97', plain,
% 29.20/29.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.20/29.39         ((v1_xboole_0 @ sk_C_1)
% 29.20/29.39          | ~ (v1_funct_1 @ X0)
% 29.20/29.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 29.20/29.39          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 29.20/29.39               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 29.20/29.39          | ((sk_B_1) = (k1_xboole_0))
% 29.20/29.39          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 29.20/29.39              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 29.20/29.39          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 29.20/29.39      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 29.20/29.39  thf('98', plain, (((sk_B_1) != (k1_xboole_0))),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('99', plain,
% 29.20/29.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 29.20/29.39         ((v1_xboole_0 @ sk_C_1)
% 29.20/29.39          | ~ (v1_funct_1 @ X0)
% 29.20/29.39          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ X1)))
% 29.20/29.39          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 29.20/29.39               (k1_relset_1 @ sk_C_1 @ X1 @ X0))
% 29.20/29.39          | ((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_D @ X0) @ X2)
% 29.20/29.39              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 29.20/29.39          | ~ (m1_subset_1 @ X2 @ sk_B_1))),
% 29.20/29.39      inference('simplify_reflect-', [status(thm)], ['97', '98'])).
% 29.20/29.39  thf('100', plain,
% 29.20/29.39      (![X0 : $i]:
% 29.20/29.39         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 29.20/29.39          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 29.20/29.39          | ((k1_funct_1 @ 
% 29.20/29.39              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 29.20/29.39              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 29.20/29.39          | ~ (m1_subset_1 @ sk_E @ 
% 29.20/29.39               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))
% 29.20/29.39          | ~ (v1_funct_1 @ sk_E)
% 29.20/29.39          | (v1_xboole_0 @ sk_C_1))),
% 29.20/29.39      inference('sup-', [status(thm)], ['90', '99'])).
% 29.20/29.39  thf('101', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 29.20/29.39      inference('demod', [status(thm)], ['72', '75'])).
% 29.20/29.39  thf('102', plain,
% 29.20/29.39      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_A)))),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('103', plain, ((v1_funct_1 @ sk_E)),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('104', plain,
% 29.20/29.39      (![X0 : $i]:
% 29.20/29.39         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 29.20/29.39          | ((k1_funct_1 @ 
% 29.20/29.39              (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ X0)
% 29.20/29.39              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 29.20/29.39          | (v1_xboole_0 @ sk_C_1))),
% 29.20/29.39      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 29.20/29.39  thf('105', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 29.20/29.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 29.20/29.39  thf('106', plain,
% 29.20/29.39      (![X0 : $i]:
% 29.20/29.39         (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 29.20/29.39            X0) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 29.20/29.39          | ~ (m1_subset_1 @ X0 @ sk_B_1))),
% 29.20/29.39      inference('clc', [status(thm)], ['104', '105'])).
% 29.20/29.39  thf('107', plain,
% 29.20/29.39      (((k1_funct_1 @ (k8_funct_2 @ sk_B_1 @ sk_C_1 @ sk_A @ sk_D @ sk_E) @ 
% 29.20/29.39         sk_F) = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 29.20/29.39      inference('sup-', [status(thm)], ['89', '106'])).
% 29.20/29.39  thf('108', plain,
% 29.20/29.39      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 29.20/29.39         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 29.20/29.39      inference('demod', [status(thm)], ['88', '107'])).
% 29.20/29.39  thf('109', plain,
% 29.20/29.39      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 29.20/29.39          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 29.20/29.39        | ((k2_relat_1 @ sk_D) = (k1_xboole_0)))),
% 29.20/29.39      inference('sup-', [status(thm)], ['87', '108'])).
% 29.20/29.39  thf('110', plain, (((k2_relat_1 @ sk_D) = (k1_xboole_0))),
% 29.20/29.39      inference('simplify', [status(thm)], ['109'])).
% 29.20/29.39  thf(t113_zfmisc_1, axiom,
% 29.20/29.39    (![A:$i,B:$i]:
% 29.20/29.39     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 29.20/29.39       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 29.20/29.39  thf('111', plain,
% 29.20/29.39      (![X11 : $i, X12 : $i]:
% 29.20/29.39         (((k2_zfmisc_1 @ X11 @ X12) = (k1_xboole_0))
% 29.20/29.39          | ((X12) != (k1_xboole_0)))),
% 29.20/29.39      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 29.20/29.39  thf('112', plain,
% 29.20/29.39      (![X11 : $i]: ((k2_zfmisc_1 @ X11 @ k1_xboole_0) = (k1_xboole_0))),
% 29.20/29.39      inference('simplify', [status(thm)], ['111'])).
% 29.20/29.39  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 29.20/29.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 29.20/29.39  thf('114', plain, ($false),
% 29.20/29.39      inference('demod', [status(thm)], ['39', '110', '112', '113'])).
% 29.20/29.39  
% 29.20/29.39  % SZS output end Refutation
% 29.20/29.39  
% 29.20/29.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
