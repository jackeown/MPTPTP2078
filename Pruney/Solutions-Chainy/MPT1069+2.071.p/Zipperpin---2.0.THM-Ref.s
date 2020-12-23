%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESK0355iKy

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:11 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 212 expanded)
%              Number of leaves         :   39 (  80 expanded)
%              Depth                    :   15
%              Number of atoms          : 1108 (4381 expanded)
%              Number of equality atoms :   55 ( 184 expanded)
%              Maximal formula depth    :   22 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ sk_A @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('6',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('7',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['4','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('13',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X32 ) @ X33 )
      | ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X32 ) @ X33 ) ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('19',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['14','19','20'])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v5_relat_1 @ sk_D @ ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('25',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('28',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X34 @ X35 )
      | ( X36 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X37 @ X34 ) @ ( k2_relset_1 @ X35 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('31',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ( sk_C = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['39'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k2_relat_1 @ sk_D ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['34','42'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('44',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k2_relat_1 @ X8 ) )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( v5_relat_1 @ X8 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['17','18'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_F ) @ ( k1_relat_1 @ sk_E ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','47'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ( ( k7_partfun1 @ X25 @ X24 @ X23 )
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('55',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( sk_C = k1_xboole_0 )
      | ~ ( v5_relat_1 @ sk_E @ X0 )
      | ( ( k7_partfun1 @ X0 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ) ),
    inference(demod,[status(thm)],['50','55','56'])).

thf('58',plain,
    ( ( ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','57'])).

thf('59',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k1_relset_1 @ sk_C @ sk_A @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('62',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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

thf('63',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X29 @ X27 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X27 @ X28 @ X31 @ X26 @ X30 ) @ X29 )
        = ( k1_funct_1 @ X30 @ ( k1_funct_1 @ X26 @ X29 ) ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X27 @ X28 @ X26 ) @ ( k1_relset_1 @ X28 @ X31 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('64',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_C )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('66',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_C @ X1 @ X0 ) )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','70'])).

thf('72',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72','73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['60','77'])).

thf('79',plain,(
    ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
 != ( k7_partfun1 @ sk_A @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['59','78'])).

thf('80',plain,
    ( ( ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
     != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','79'])).

thf('81',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ESK0355iKy
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 477 iterations in 0.274s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.51/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.51/0.70  thf(sk_F_type, type, sk_F: $i).
% 0.51/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.51/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.51/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.51/0.70  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.51/0.70  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.51/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.51/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.51/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.51/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.51/0.70  thf(sk_E_type, type, sk_E: $i).
% 0.51/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.51/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.51/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.70  thf(t186_funct_2, conjecture,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.51/0.70       ( ![D:$i]:
% 0.51/0.70         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.51/0.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.51/0.70           ( ![E:$i]:
% 0.51/0.70             ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.70                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.51/0.70               ( ![F:$i]:
% 0.51/0.70                 ( ( m1_subset_1 @ F @ B ) =>
% 0.51/0.70                   ( ( r1_tarski @
% 0.51/0.70                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.51/0.70                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.51/0.70                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.51/0.70                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.51/0.70                         ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.70        ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.51/0.70          ( ![D:$i]:
% 0.51/0.70            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.51/0.70                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.51/0.70              ( ![E:$i]:
% 0.51/0.70                ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.70                    ( m1_subset_1 @
% 0.51/0.70                      E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.51/0.70                  ( ![F:$i]:
% 0.51/0.70                    ( ( m1_subset_1 @ F @ B ) =>
% 0.51/0.70                      ( ( r1_tarski @
% 0.51/0.70                          ( k2_relset_1 @ B @ C @ D ) @ 
% 0.51/0.70                          ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.51/0.70                        ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.51/0.70                          ( ( k1_funct_1 @
% 0.51/0.70                              ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.51/0.70                            ( k7_partfun1 @ A @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t186_funct_2])).
% 0.51/0.70  thf('0', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('1', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(cc2_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.51/0.70  thf('2', plain,
% 0.51/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.70         ((v5_relat_1 @ X14 @ X16)
% 0.51/0.70          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.70  thf('3', plain, ((v5_relat_1 @ sk_E @ sk_A)),
% 0.51/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.51/0.70  thf('4', plain,
% 0.51/0.70      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.51/0.70        (k1_relset_1 @ sk_C @ sk_A @ sk_E))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('5', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.70         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.51/0.70          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.51/0.70  thf('7', plain, (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.51/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('8', plain,
% 0.51/0.70      ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.51/0.70      inference('demod', [status(thm)], ['4', '7'])).
% 0.51/0.70  thf('9', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.51/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.51/0.70  thf('10', plain,
% 0.51/0.70      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.51/0.70         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.51/0.70          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.51/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.51/0.70  thf('11', plain,
% 0.51/0.70      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.51/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.70  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.51/0.70      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.70  thf(t4_funct_2, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.70       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.51/0.70         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.51/0.70           ( m1_subset_1 @
% 0.51/0.70             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.51/0.70  thf('13', plain,
% 0.51/0.70      (![X32 : $i, X33 : $i]:
% 0.51/0.70         (~ (r1_tarski @ (k2_relat_1 @ X32) @ X33)
% 0.51/0.70          | (m1_subset_1 @ X32 @ 
% 0.51/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X32) @ X33)))
% 0.51/0.70          | ~ (v1_funct_1 @ X32)
% 0.51/0.70          | ~ (v1_relat_1 @ X32))),
% 0.51/0.70      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      ((~ (v1_relat_1 @ sk_D)
% 0.51/0.70        | ~ (v1_funct_1 @ sk_D)
% 0.51/0.70        | (m1_subset_1 @ sk_D @ 
% 0.51/0.70           (k1_zfmisc_1 @ 
% 0.51/0.70            (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E)))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(cc2_relat_1, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( v1_relat_1 @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (![X3 : $i, X4 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.51/0.70          | (v1_relat_1 @ X3)
% 0.51/0.70          | ~ (v1_relat_1 @ X4))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D))),
% 0.51/0.70      inference('sup-', [status(thm)], ['15', '16'])).
% 0.51/0.70  thf(fc6_relat_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.51/0.70  thf('18', plain,
% 0.51/0.70      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.51/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.70  thf('19', plain, ((v1_relat_1 @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['17', '18'])).
% 0.51/0.70  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('21', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_D @ 
% 0.51/0.70        (k1_zfmisc_1 @ 
% 0.51/0.70         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))))),
% 0.51/0.70      inference('demod', [status(thm)], ['14', '19', '20'])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.51/0.70         ((v5_relat_1 @ X14 @ X16)
% 0.51/0.70          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.51/0.70  thf('23', plain, ((v5_relat_1 @ sk_D @ (k1_relat_1 @ sk_E))),
% 0.51/0.70      inference('sup-', [status(thm)], ['21', '22'])).
% 0.51/0.70  thf('24', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(t2_subset, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ A @ B ) =>
% 0.51/0.70       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.51/0.70  thf('25', plain,
% 0.51/0.70      (![X1 : $i, X2 : $i]:
% 0.51/0.70         ((r2_hidden @ X1 @ X2)
% 0.51/0.70          | (v1_xboole_0 @ X2)
% 0.51/0.70          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.51/0.70      inference('cnf', [status(esa)], [t2_subset])).
% 0.51/0.70  thf('26', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.51/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.70  thf('27', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(t6_funct_2, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.51/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.51/0.70       ( ( r2_hidden @ C @ A ) =>
% 0.51/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.51/0.70           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X34 @ X35)
% 0.51/0.70          | ((X36) = (k1_xboole_0))
% 0.51/0.70          | ~ (v1_funct_1 @ X37)
% 0.51/0.70          | ~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.51/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.51/0.70          | (r2_hidden @ (k1_funct_1 @ X37 @ X34) @ 
% 0.51/0.70             (k2_relset_1 @ X35 @ X36 @ X37)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.51/0.70  thf('29', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ 
% 0.51/0.70           (k2_relset_1 @ sk_B @ sk_C @ sk_D))
% 0.51/0.70          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.51/0.70          | ~ (v1_funct_1 @ sk_D)
% 0.51/0.70          | ((sk_C) = (k1_xboole_0))
% 0.51/0.70          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.51/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.51/0.70  thf('30', plain,
% 0.51/0.70      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.51/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.70  thf('31', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('32', plain, ((v1_funct_1 @ sk_D)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('33', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r2_hidden @ (k1_funct_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.51/0.70          | ((sk_C) = (k1_xboole_0))
% 0.51/0.70          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.51/0.70      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (((v1_xboole_0 @ sk_B)
% 0.51/0.70        | ((sk_C) = (k1_xboole_0))
% 0.51/0.70        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['26', '33'])).
% 0.51/0.70  thf(l13_xboole_0, axiom,
% 0.51/0.70    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.51/0.70  thf('35', plain,
% 0.51/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.51/0.70  thf('36', plain,
% 0.51/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.70      inference('sup+', [status(thm)], ['35', '36'])).
% 0.51/0.70  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('39', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((X0) != (k1_xboole_0))
% 0.51/0.70          | ~ (v1_xboole_0 @ X0)
% 0.51/0.70          | ~ (v1_xboole_0 @ sk_B))),
% 0.51/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.51/0.70  thf('40', plain, ((~ (v1_xboole_0 @ sk_B) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['39'])).
% 0.51/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.51/0.70  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.70  thf('42', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.51/0.70      inference('simplify_reflect+', [status(thm)], ['40', '41'])).
% 0.51/0.70  thf('43', plain,
% 0.51/0.70      (((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k2_relat_1 @ sk_D))
% 0.51/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['34', '42'])).
% 0.51/0.70  thf(t202_relat_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.51/0.70       ( ![C:$i]:
% 0.51/0.70         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.51/0.70  thf('44', plain,
% 0.51/0.70      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X7 @ (k2_relat_1 @ X8))
% 0.51/0.70          | (r2_hidden @ X7 @ X9)
% 0.51/0.70          | ~ (v5_relat_1 @ X8 @ X9)
% 0.51/0.70          | ~ (v1_relat_1 @ X8))),
% 0.51/0.70      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.51/0.70  thf('45', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((sk_C) = (k1_xboole_0))
% 0.51/0.70          | ~ (v1_relat_1 @ sk_D)
% 0.51/0.70          | ~ (v5_relat_1 @ sk_D @ X0)
% 0.51/0.70          | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['43', '44'])).
% 0.51/0.70  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.51/0.70      inference('demod', [status(thm)], ['17', '18'])).
% 0.51/0.70  thf('47', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((sk_C) = (k1_xboole_0))
% 0.51/0.70          | ~ (v5_relat_1 @ sk_D @ X0)
% 0.51/0.70          | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ X0))),
% 0.51/0.70      inference('demod', [status(thm)], ['45', '46'])).
% 0.51/0.70  thf('48', plain,
% 0.51/0.70      (((r2_hidden @ (k1_funct_1 @ sk_D @ sk_F) @ (k1_relat_1 @ sk_E))
% 0.51/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['23', '47'])).
% 0.51/0.70  thf(d8_partfun1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.51/0.70       ( ![C:$i]:
% 0.51/0.70         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.51/0.70           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.51/0.70  thf('49', plain,
% 0.51/0.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.51/0.70          | ((k7_partfun1 @ X25 @ X24 @ X23) = (k1_funct_1 @ X24 @ X23))
% 0.51/0.70          | ~ (v1_funct_1 @ X24)
% 0.51/0.70          | ~ (v5_relat_1 @ X24 @ X25)
% 0.51/0.70          | ~ (v1_relat_1 @ X24))),
% 0.51/0.70      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.51/0.70  thf('50', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((sk_C) = (k1_xboole_0))
% 0.51/0.70          | ~ (v1_relat_1 @ sk_E)
% 0.51/0.70          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.51/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.51/0.70          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.51/0.70              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.51/0.70  thf('51', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('52', plain,
% 0.51/0.70      (![X3 : $i, X4 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.51/0.70          | (v1_relat_1 @ X3)
% 0.51/0.70          | ~ (v1_relat_1 @ X4))),
% 0.51/0.70      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.51/0.70  thf('53', plain,
% 0.51/0.70      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)) | (v1_relat_1 @ sk_E))),
% 0.51/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.51/0.70  thf('54', plain,
% 0.51/0.70      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.51/0.70      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.51/0.70  thf('55', plain, ((v1_relat_1 @ sk_E)),
% 0.51/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.51/0.70  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('57', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((sk_C) = (k1_xboole_0))
% 0.51/0.70          | ~ (v5_relat_1 @ sk_E @ X0)
% 0.51/0.70          | ((k7_partfun1 @ X0 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.51/0.70              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.51/0.70      inference('demod', [status(thm)], ['50', '55', '56'])).
% 0.51/0.70  thf('58', plain,
% 0.51/0.70      ((((k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.51/0.70          = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.51/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['3', '57'])).
% 0.51/0.70  thf('59', plain,
% 0.51/0.70      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.51/0.70         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('60', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('61', plain,
% 0.51/0.70      (((k1_relset_1 @ sk_C @ sk_A @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.51/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.51/0.70  thf('62', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf(t185_funct_2, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.51/0.70       ( ![D:$i]:
% 0.51/0.70         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.51/0.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.51/0.70           ( ![E:$i]:
% 0.51/0.70             ( ( ( v1_funct_1 @ E ) & 
% 0.51/0.70                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.51/0.70               ( ![F:$i]:
% 0.51/0.70                 ( ( m1_subset_1 @ F @ B ) =>
% 0.51/0.70                   ( ( r1_tarski @
% 0.51/0.70                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.51/0.70                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.51/0.70                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.51/0.70                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.51/0.70                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.70  thf('63', plain,
% 0.51/0.70      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.70         (~ (v1_funct_1 @ X26)
% 0.51/0.70          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.51/0.70          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.51/0.70          | ~ (m1_subset_1 @ X29 @ X27)
% 0.51/0.70          | ((k1_funct_1 @ (k8_funct_2 @ X27 @ X28 @ X31 @ X26 @ X30) @ X29)
% 0.51/0.70              = (k1_funct_1 @ X30 @ (k1_funct_1 @ X26 @ X29)))
% 0.51/0.70          | ((X27) = (k1_xboole_0))
% 0.51/0.70          | ~ (r1_tarski @ (k2_relset_1 @ X27 @ X28 @ X26) @ 
% 0.51/0.70               (k1_relset_1 @ X28 @ X31 @ X30))
% 0.51/0.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X31)))
% 0.51/0.70          | ~ (v1_funct_1 @ X30)
% 0.51/0.70          | (v1_xboole_0 @ X28))),
% 0.51/0.70      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.51/0.70  thf('64', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         ((v1_xboole_0 @ sk_C)
% 0.51/0.70          | ~ (v1_funct_1 @ X0)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.51/0.70          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D) @ 
% 0.51/0.70               (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.51/0.70          | ((sk_B) = (k1_xboole_0))
% 0.51/0.70          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.51/0.70              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.51/0.70          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.51/0.70          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_C)
% 0.51/0.70          | ~ (v1_funct_1 @ sk_D))),
% 0.51/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.51/0.70  thf('65', plain,
% 0.51/0.70      (((k2_relset_1 @ sk_B @ sk_C @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.51/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.51/0.70  thf('66', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_C)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('67', plain, ((v1_funct_1 @ sk_D)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('68', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         ((v1_xboole_0 @ sk_C)
% 0.51/0.70          | ~ (v1_funct_1 @ X0)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.51/0.70          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.51/0.70          | ((sk_B) = (k1_xboole_0))
% 0.51/0.70          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.51/0.70              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.51/0.70          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.51/0.70      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.51/0.70  thf('69', plain, (((sk_B) != (k1_xboole_0))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('70', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         ((v1_xboole_0 @ sk_C)
% 0.51/0.70          | ~ (v1_funct_1 @ X0)
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X1)))
% 0.51/0.70          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_C @ X1 @ X0))
% 0.51/0.70          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ X1 @ sk_D @ X0) @ X2)
% 0.51/0.70              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.51/0.70          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.51/0.70      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.51/0.70  thf('71', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.51/0.70          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.51/0.70              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.51/0.70          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))
% 0.51/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.51/0.70          | (v1_xboole_0 @ sk_C))),
% 0.51/0.70      inference('sup-', [status(thm)], ['61', '70'])).
% 0.51/0.70  thf('72', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relat_1 @ sk_E))),
% 0.51/0.70      inference('demod', [status(thm)], ['8', '11'])).
% 0.51/0.70  thf('73', plain,
% 0.51/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('74', plain, ((v1_funct_1 @ sk_E)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('75', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.51/0.70          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.51/0.70              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.51/0.70          | (v1_xboole_0 @ sk_C))),
% 0.51/0.70      inference('demod', [status(thm)], ['71', '72', '73', '74'])).
% 0.51/0.70  thf('76', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('77', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ X0)
% 0.51/0.70            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.51/0.70          | ~ (m1_subset_1 @ X0 @ sk_B))),
% 0.51/0.70      inference('clc', [status(thm)], ['75', '76'])).
% 0.51/0.70  thf('78', plain,
% 0.51/0.70      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_C @ sk_A @ sk_D @ sk_E) @ sk_F)
% 0.51/0.70         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['60', '77'])).
% 0.51/0.70  thf('79', plain,
% 0.51/0.70      (((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.51/0.70         != (k7_partfun1 @ sk_A @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.51/0.70      inference('demod', [status(thm)], ['59', '78'])).
% 0.51/0.70  thf('80', plain,
% 0.51/0.70      ((((k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.51/0.70          != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.51/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['58', '79'])).
% 0.51/0.70  thf('81', plain, (((sk_C) = (k1_xboole_0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['80'])).
% 0.51/0.70  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.51/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.51/0.70  thf('83', plain, ($false),
% 0.51/0.70      inference('demod', [status(thm)], ['0', '81', '82'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
