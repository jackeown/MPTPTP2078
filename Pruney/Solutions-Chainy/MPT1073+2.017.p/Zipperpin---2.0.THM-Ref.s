%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.diJUKlj6Sb

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:15 EST 2020

% Result     : Theorem 1.82s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 237 expanded)
%              Number of leaves         :   43 (  90 expanded)
%              Depth                    :   12
%              Number of atoms          :  870 (3056 expanded)
%              Number of equality atoms :   52 ( 147 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_D_3 @ sk_C_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_2 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('9',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_2 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_relat_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_D_2 @ sk_A @ sk_D_3 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['10','11','14'])).

thf(t172_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X18 @ X17 ) @ X19 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v5_relat_1 @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t172_funct_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_3 )
      | ~ ( v5_relat_1 @ sk_D_3 @ X0 )
      | ~ ( v1_funct_1 @ sk_D_3 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('19',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('21',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_2 @ X14 @ X11 ) ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('22',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_2 @ X14 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('26',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_A @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v5_relat_1 @ sk_D_3 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18','19','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['2','27'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('33',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( X43 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X43 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X43 ) ) )
      | ( ( k8_relset_1 @ X41 @ X43 @ X42 @ X43 )
        = X41 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('34',plain,
    ( ( ( k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ sk_C_1 )
      = sk_B_1 )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( ( k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ sk_C_1 )
      = sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('39',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( ( k7_relset_1 @ X38 @ X39 @ X40 @ ( k8_relset_1 @ X38 @ X39 @ X40 @ X39 ) )
        = ( k2_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('40',plain,
    ( ( k7_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ ( k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ sk_C_1 ) )
    = ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('42',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('45',plain,
    ( ( k9_relat_1 @ sk_D_3 @ ( k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['40','43','44'])).

thf('46',plain,
    ( ( ( k9_relat_1 @ sk_D_3 @ sk_B_1 )
      = ( k2_relat_1 @ sk_D_3 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_3 @ sk_B_1 @ X0 ) @ X0 ) @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_3 @ sk_B_1 @ X0 ) @ X0 ) @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_3 @ sk_B_1 @ sk_A ) @ sk_A ) @ sk_D_3 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','50'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ X21 )
      | ( X22
        = ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('53',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('55',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_B_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('58',plain,
    ( ( ( k9_relat_1 @ sk_D_3 @ sk_B_1 )
      = ( k2_relat_1 @ sk_D_3 ) )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_3 )
      | ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_B_1 @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_3 ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_B_1 @ X0 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_B_1 @ sk_A ) @ sk_B_1 )
    | ( sk_C_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','62'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('65',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X44: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_3 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( sk_C_1 = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    sk_C_1 = k1_xboole_0 ),
    inference(clc,[status(thm)],['56','67'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('71',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    $false ),
    inference(demod,[status(thm)],['30','68','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.diJUKlj6Sb
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 1.82/2.07  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.82/2.07  % Solved by: fo/fo7.sh
% 1.82/2.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.82/2.07  % done 570 iterations in 1.596s
% 1.82/2.07  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.82/2.07  % SZS output start Refutation
% 1.82/2.07  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.82/2.07  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.82/2.07  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 1.82/2.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.82/2.07  thf(sk_A_type, type, sk_A: $i).
% 1.82/2.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.82/2.07  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.82/2.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.82/2.07  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.82/2.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.82/2.07  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.82/2.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.82/2.07  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.82/2.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.82/2.07  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.82/2.07  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 1.82/2.07  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.82/2.07  thf(sk_D_3_type, type, sk_D_3: $i).
% 1.82/2.07  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.82/2.07  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 1.82/2.07  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.82/2.07  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.82/2.07  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.82/2.07  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 1.82/2.07  thf(sk_B_type, type, sk_B: $i > $i).
% 1.82/2.07  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.82/2.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.82/2.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.82/2.07  thf(t190_funct_2, conjecture,
% 1.82/2.07    (![A:$i,B:$i,C:$i,D:$i]:
% 1.82/2.07     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.82/2.07         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.82/2.07       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 1.82/2.07            ( ![E:$i]:
% 1.82/2.07              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 1.82/2.07  thf(zf_stmt_0, negated_conjecture,
% 1.82/2.07    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.82/2.07        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.82/2.07            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.82/2.07          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 1.82/2.07               ( ![E:$i]:
% 1.82/2.07                 ( ( m1_subset_1 @ E @ B ) =>
% 1.82/2.07                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 1.82/2.07    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 1.82/2.07  thf('0', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(cc2_relset_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.07       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.82/2.07  thf('1', plain,
% 1.82/2.07      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.82/2.07         ((v5_relat_1 @ X28 @ X30)
% 1.82/2.07          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.82/2.07      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.82/2.07  thf('2', plain, ((v5_relat_1 @ sk_D_3 @ sk_C_1)),
% 1.82/2.07      inference('sup-', [status(thm)], ['0', '1'])).
% 1.82/2.07  thf('3', plain,
% 1.82/2.07      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('4', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(redefinition_k2_relset_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.07       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.82/2.07  thf('5', plain,
% 1.82/2.07      (![X31 : $i, X32 : $i, X33 : $i]:
% 1.82/2.07         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 1.82/2.07          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 1.82/2.07      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.82/2.07  thf('6', plain,
% 1.82/2.07      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('sup-', [status(thm)], ['4', '5'])).
% 1.82/2.07  thf('7', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('demod', [status(thm)], ['3', '6'])).
% 1.82/2.07  thf(d5_funct_1, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.82/2.07       ( ![B:$i]:
% 1.82/2.07         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.82/2.07           ( ![C:$i]:
% 1.82/2.07             ( ( r2_hidden @ C @ B ) <=>
% 1.82/2.07               ( ?[D:$i]:
% 1.82/2.07                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.82/2.07                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.82/2.07  thf('8', plain,
% 1.82/2.07      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.82/2.07         (((X13) != (k2_relat_1 @ X11))
% 1.82/2.07          | (r2_hidden @ (sk_D_2 @ X14 @ X11) @ (k1_relat_1 @ X11))
% 1.82/2.07          | ~ (r2_hidden @ X14 @ X13)
% 1.82/2.07          | ~ (v1_funct_1 @ X11)
% 1.82/2.07          | ~ (v1_relat_1 @ X11))),
% 1.82/2.07      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.82/2.07  thf('9', plain,
% 1.82/2.07      (![X11 : $i, X14 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X11)
% 1.82/2.07          | ~ (v1_funct_1 @ X11)
% 1.82/2.07          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 1.82/2.07          | (r2_hidden @ (sk_D_2 @ X14 @ X11) @ (k1_relat_1 @ X11)))),
% 1.82/2.07      inference('simplify', [status(thm)], ['8'])).
% 1.82/2.07  thf('10', plain,
% 1.82/2.07      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))
% 1.82/2.07        | ~ (v1_funct_1 @ sk_D_3)
% 1.82/2.07        | ~ (v1_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('sup-', [status(thm)], ['7', '9'])).
% 1.82/2.07  thf('11', plain, ((v1_funct_1 @ sk_D_3)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('12', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(cc1_relset_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.07       ( v1_relat_1 @ C ) ))).
% 1.82/2.07  thf('13', plain,
% 1.82/2.07      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.82/2.07         ((v1_relat_1 @ X25)
% 1.82/2.07          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.82/2.07      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.82/2.07  thf('14', plain, ((v1_relat_1 @ sk_D_3)),
% 1.82/2.07      inference('sup-', [status(thm)], ['12', '13'])).
% 1.82/2.07  thf('15', plain,
% 1.82/2.07      ((r2_hidden @ (sk_D_2 @ sk_A @ sk_D_3) @ (k1_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('demod', [status(thm)], ['10', '11', '14'])).
% 1.82/2.07  thf(t172_funct_1, axiom,
% 1.82/2.07    (![A:$i,B:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.82/2.07       ( ![C:$i]:
% 1.82/2.07         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.82/2.07           ( r2_hidden @ ( k1_funct_1 @ B @ C ) @ A ) ) ) ))).
% 1.82/2.07  thf('16', plain,
% 1.82/2.07      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.82/2.07         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 1.82/2.07          | (r2_hidden @ (k1_funct_1 @ X18 @ X17) @ X19)
% 1.82/2.07          | ~ (v1_funct_1 @ X18)
% 1.82/2.07          | ~ (v5_relat_1 @ X18 @ X19)
% 1.82/2.07          | ~ (v1_relat_1 @ X18))),
% 1.82/2.07      inference('cnf', [status(esa)], [t172_funct_1])).
% 1.82/2.07  thf('17', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ sk_D_3)
% 1.82/2.07          | ~ (v5_relat_1 @ sk_D_3 @ X0)
% 1.82/2.07          | ~ (v1_funct_1 @ sk_D_3)
% 1.82/2.07          | (r2_hidden @ (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3)) @ X0))),
% 1.82/2.07      inference('sup-', [status(thm)], ['15', '16'])).
% 1.82/2.07  thf('18', plain, ((v1_relat_1 @ sk_D_3)),
% 1.82/2.07      inference('sup-', [status(thm)], ['12', '13'])).
% 1.82/2.07  thf('19', plain, ((v1_funct_1 @ sk_D_3)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('20', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('demod', [status(thm)], ['3', '6'])).
% 1.82/2.07  thf('21', plain,
% 1.82/2.07      (![X11 : $i, X13 : $i, X14 : $i]:
% 1.82/2.07         (((X13) != (k2_relat_1 @ X11))
% 1.82/2.07          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_2 @ X14 @ X11)))
% 1.82/2.07          | ~ (r2_hidden @ X14 @ X13)
% 1.82/2.07          | ~ (v1_funct_1 @ X11)
% 1.82/2.07          | ~ (v1_relat_1 @ X11))),
% 1.82/2.07      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.82/2.07  thf('22', plain,
% 1.82/2.07      (![X11 : $i, X14 : $i]:
% 1.82/2.07         (~ (v1_relat_1 @ X11)
% 1.82/2.07          | ~ (v1_funct_1 @ X11)
% 1.82/2.07          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 1.82/2.07          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_2 @ X14 @ X11))))),
% 1.82/2.07      inference('simplify', [status(thm)], ['21'])).
% 1.82/2.07  thf('23', plain,
% 1.82/2.07      ((((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3)))
% 1.82/2.07        | ~ (v1_funct_1 @ sk_D_3)
% 1.82/2.07        | ~ (v1_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('sup-', [status(thm)], ['20', '22'])).
% 1.82/2.07  thf('24', plain, ((v1_funct_1 @ sk_D_3)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('25', plain, ((v1_relat_1 @ sk_D_3)),
% 1.82/2.07      inference('sup-', [status(thm)], ['12', '13'])).
% 1.82/2.07  thf('26', plain,
% 1.82/2.07      (((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_A @ sk_D_3)))),
% 1.82/2.07      inference('demod', [status(thm)], ['23', '24', '25'])).
% 1.82/2.07  thf('27', plain,
% 1.82/2.07      (![X0 : $i]: (~ (v5_relat_1 @ sk_D_3 @ X0) | (r2_hidden @ sk_A @ X0))),
% 1.82/2.07      inference('demod', [status(thm)], ['17', '18', '19', '26'])).
% 1.82/2.07  thf('28', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 1.82/2.07      inference('sup-', [status(thm)], ['2', '27'])).
% 1.82/2.07  thf(d1_xboole_0, axiom,
% 1.82/2.07    (![A:$i]:
% 1.82/2.07     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.82/2.07  thf('29', plain,
% 1.82/2.07      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.82/2.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.82/2.07  thf('30', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 1.82/2.07      inference('sup-', [status(thm)], ['28', '29'])).
% 1.82/2.07  thf('31', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('demod', [status(thm)], ['3', '6'])).
% 1.82/2.07  thf('32', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(t48_funct_2, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.82/2.07         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.82/2.07       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.82/2.07         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 1.82/2.07  thf('33', plain,
% 1.82/2.07      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.82/2.07         (((X43) = (k1_xboole_0))
% 1.82/2.07          | ~ (v1_funct_1 @ X42)
% 1.82/2.07          | ~ (v1_funct_2 @ X42 @ X41 @ X43)
% 1.82/2.07          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X43)))
% 1.82/2.07          | ((k8_relset_1 @ X41 @ X43 @ X42 @ X43) = (X41)))),
% 1.82/2.07      inference('cnf', [status(esa)], [t48_funct_2])).
% 1.82/2.07  thf('34', plain,
% 1.82/2.07      ((((k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ sk_C_1) = (sk_B_1))
% 1.82/2.07        | ~ (v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1)
% 1.82/2.07        | ~ (v1_funct_1 @ sk_D_3)
% 1.82/2.07        | ((sk_C_1) = (k1_xboole_0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['32', '33'])).
% 1.82/2.07  thf('35', plain, ((v1_funct_2 @ sk_D_3 @ sk_B_1 @ sk_C_1)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('36', plain, ((v1_funct_1 @ sk_D_3)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('37', plain,
% 1.82/2.07      ((((k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ sk_C_1) = (sk_B_1))
% 1.82/2.07        | ((sk_C_1) = (k1_xboole_0)))),
% 1.82/2.07      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.82/2.07  thf('38', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(t39_relset_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.82/2.07       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 1.82/2.07           ( k2_relset_1 @ B @ A @ C ) ) & 
% 1.82/2.07         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 1.82/2.07           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 1.82/2.07  thf('39', plain,
% 1.82/2.07      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.82/2.07         (((k7_relset_1 @ X38 @ X39 @ X40 @ 
% 1.82/2.07            (k8_relset_1 @ X38 @ X39 @ X40 @ X39))
% 1.82/2.07            = (k2_relset_1 @ X38 @ X39 @ X40))
% 1.82/2.07          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 1.82/2.07      inference('cnf', [status(esa)], [t39_relset_1])).
% 1.82/2.07  thf('40', plain,
% 1.82/2.07      (((k7_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ 
% 1.82/2.07         (k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ sk_C_1))
% 1.82/2.07         = (k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3))),
% 1.82/2.07      inference('sup-', [status(thm)], ['38', '39'])).
% 1.82/2.07  thf('41', plain,
% 1.82/2.07      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf(redefinition_k7_relset_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i,D:$i]:
% 1.82/2.07     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.82/2.07       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 1.82/2.07  thf('42', plain,
% 1.82/2.07      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.82/2.07         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.82/2.07          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 1.82/2.07      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 1.82/2.07  thf('43', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         ((k7_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ X0)
% 1.82/2.07           = (k9_relat_1 @ sk_D_3 @ X0))),
% 1.82/2.07      inference('sup-', [status(thm)], ['41', '42'])).
% 1.82/2.07  thf('44', plain,
% 1.82/2.07      (((k2_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3) = (k2_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('sup-', [status(thm)], ['4', '5'])).
% 1.82/2.07  thf('45', plain,
% 1.82/2.07      (((k9_relat_1 @ sk_D_3 @ 
% 1.82/2.07         (k8_relset_1 @ sk_B_1 @ sk_C_1 @ sk_D_3 @ sk_C_1))
% 1.82/2.07         = (k2_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('demod', [status(thm)], ['40', '43', '44'])).
% 1.82/2.07  thf('46', plain,
% 1.82/2.07      ((((k9_relat_1 @ sk_D_3 @ sk_B_1) = (k2_relat_1 @ sk_D_3))
% 1.82/2.07        | ((sk_C_1) = (k1_xboole_0)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['37', '45'])).
% 1.82/2.07  thf(t143_relat_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( v1_relat_1 @ C ) =>
% 1.82/2.07       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 1.82/2.07         ( ?[D:$i]:
% 1.82/2.07           ( ( r2_hidden @ D @ B ) & 
% 1.82/2.07             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 1.82/2.07             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 1.82/2.07  thf('47', plain,
% 1.82/2.07      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.82/2.07         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 1.82/2.07          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ X8) @ X9)
% 1.82/2.07          | ~ (v1_relat_1 @ X9))),
% 1.82/2.07      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.82/2.07  thf('48', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3))
% 1.82/2.07          | ((sk_C_1) = (k1_xboole_0))
% 1.82/2.07          | ~ (v1_relat_1 @ sk_D_3)
% 1.82/2.07          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_B_1 @ X0) @ X0) @ 
% 1.82/2.07             sk_D_3))),
% 1.82/2.07      inference('sup-', [status(thm)], ['46', '47'])).
% 1.82/2.07  thf('49', plain, ((v1_relat_1 @ sk_D_3)),
% 1.82/2.07      inference('sup-', [status(thm)], ['12', '13'])).
% 1.82/2.07  thf('50', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3))
% 1.82/2.07          | ((sk_C_1) = (k1_xboole_0))
% 1.82/2.07          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_B_1 @ X0) @ X0) @ 
% 1.82/2.07             sk_D_3))),
% 1.82/2.07      inference('demod', [status(thm)], ['48', '49'])).
% 1.82/2.07  thf('51', plain,
% 1.82/2.07      (((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_B_1 @ sk_A) @ sk_A) @ 
% 1.82/2.07         sk_D_3)
% 1.82/2.07        | ((sk_C_1) = (k1_xboole_0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['31', '50'])).
% 1.82/2.07  thf(t8_funct_1, axiom,
% 1.82/2.07    (![A:$i,B:$i,C:$i]:
% 1.82/2.07     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.82/2.07       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 1.82/2.07         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 1.82/2.07           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.82/2.07  thf('52', plain,
% 1.82/2.07      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.82/2.07         (~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ X21)
% 1.82/2.07          | ((X22) = (k1_funct_1 @ X21 @ X20))
% 1.82/2.07          | ~ (v1_funct_1 @ X21)
% 1.82/2.07          | ~ (v1_relat_1 @ X21))),
% 1.82/2.07      inference('cnf', [status(esa)], [t8_funct_1])).
% 1.82/2.07  thf('53', plain,
% 1.82/2.07      ((((sk_C_1) = (k1_xboole_0))
% 1.82/2.07        | ~ (v1_relat_1 @ sk_D_3)
% 1.82/2.07        | ~ (v1_funct_1 @ sk_D_3)
% 1.82/2.07        | ((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_B_1 @ sk_A))))),
% 1.82/2.07      inference('sup-', [status(thm)], ['51', '52'])).
% 1.82/2.07  thf('54', plain, ((v1_relat_1 @ sk_D_3)),
% 1.82/2.07      inference('sup-', [status(thm)], ['12', '13'])).
% 1.82/2.07  thf('55', plain, ((v1_funct_1 @ sk_D_3)),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('56', plain,
% 1.82/2.07      ((((sk_C_1) = (k1_xboole_0))
% 1.82/2.07        | ((sk_A) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_B_1 @ sk_A))))),
% 1.82/2.07      inference('demod', [status(thm)], ['53', '54', '55'])).
% 1.82/2.07  thf('57', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_3))),
% 1.82/2.07      inference('demod', [status(thm)], ['3', '6'])).
% 1.82/2.07  thf('58', plain,
% 1.82/2.07      ((((k9_relat_1 @ sk_D_3 @ sk_B_1) = (k2_relat_1 @ sk_D_3))
% 1.82/2.07        | ((sk_C_1) = (k1_xboole_0)))),
% 1.82/2.07      inference('sup+', [status(thm)], ['37', '45'])).
% 1.82/2.07  thf('59', plain,
% 1.82/2.07      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.82/2.07         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 1.82/2.07          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 1.82/2.07          | ~ (v1_relat_1 @ X9))),
% 1.82/2.07      inference('cnf', [status(esa)], [t143_relat_1])).
% 1.82/2.07  thf('60', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3))
% 1.82/2.07          | ((sk_C_1) = (k1_xboole_0))
% 1.82/2.07          | ~ (v1_relat_1 @ sk_D_3)
% 1.82/2.07          | (r2_hidden @ (sk_D @ sk_D_3 @ sk_B_1 @ X0) @ sk_B_1))),
% 1.82/2.07      inference('sup-', [status(thm)], ['58', '59'])).
% 1.82/2.07  thf('61', plain, ((v1_relat_1 @ sk_D_3)),
% 1.82/2.07      inference('sup-', [status(thm)], ['12', '13'])).
% 1.82/2.07  thf('62', plain,
% 1.82/2.07      (![X0 : $i]:
% 1.82/2.07         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_3))
% 1.82/2.07          | ((sk_C_1) = (k1_xboole_0))
% 1.82/2.07          | (r2_hidden @ (sk_D @ sk_D_3 @ sk_B_1 @ X0) @ sk_B_1))),
% 1.82/2.07      inference('demod', [status(thm)], ['60', '61'])).
% 1.82/2.07  thf('63', plain,
% 1.82/2.07      (((r2_hidden @ (sk_D @ sk_D_3 @ sk_B_1 @ sk_A) @ sk_B_1)
% 1.82/2.07        | ((sk_C_1) = (k1_xboole_0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['57', '62'])).
% 1.82/2.07  thf(t1_subset, axiom,
% 1.82/2.07    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.82/2.07  thf('64', plain,
% 1.82/2.07      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 1.82/2.07      inference('cnf', [status(esa)], [t1_subset])).
% 1.82/2.07  thf('65', plain,
% 1.82/2.07      ((((sk_C_1) = (k1_xboole_0))
% 1.82/2.07        | (m1_subset_1 @ (sk_D @ sk_D_3 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 1.82/2.07      inference('sup-', [status(thm)], ['63', '64'])).
% 1.82/2.07  thf('66', plain,
% 1.82/2.07      (![X44 : $i]:
% 1.82/2.07         (((sk_A) != (k1_funct_1 @ sk_D_3 @ X44))
% 1.82/2.07          | ~ (m1_subset_1 @ X44 @ sk_B_1))),
% 1.82/2.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.82/2.07  thf('67', plain,
% 1.82/2.07      ((((sk_C_1) = (k1_xboole_0))
% 1.82/2.07        | ((sk_A) != (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_B_1 @ sk_A))))),
% 1.82/2.07      inference('sup-', [status(thm)], ['65', '66'])).
% 1.82/2.07  thf('68', plain, (((sk_C_1) = (k1_xboole_0))),
% 1.82/2.07      inference('clc', [status(thm)], ['56', '67'])).
% 1.82/2.07  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.82/2.07  thf('69', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.82/2.07      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.82/2.07  thf('70', plain,
% 1.82/2.07      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 1.82/2.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.82/2.07  thf(t7_ordinal1, axiom,
% 1.82/2.07    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.82/2.07  thf('71', plain,
% 1.82/2.07      (![X23 : $i, X24 : $i]:
% 1.82/2.07         (~ (r2_hidden @ X23 @ X24) | ~ (r1_tarski @ X24 @ X23))),
% 1.82/2.07      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.82/2.07  thf('72', plain,
% 1.82/2.07      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.82/2.07      inference('sup-', [status(thm)], ['70', '71'])).
% 1.82/2.07  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.82/2.07      inference('sup-', [status(thm)], ['69', '72'])).
% 1.82/2.07  thf('74', plain, ($false),
% 1.82/2.07      inference('demod', [status(thm)], ['30', '68', '73'])).
% 1.82/2.07  
% 1.82/2.07  % SZS output end Refutation
% 1.82/2.07  
% 1.82/2.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
