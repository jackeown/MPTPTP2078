%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SoudF9Bvyj

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:45 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 323 expanded)
%              Number of leaves         :   37 ( 110 expanded)
%              Depth                    :   15
%              Number of atoms          : 1377 (4593 expanded)
%              Number of equality atoms :   20 ( 117 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('7',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('8',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['5','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) )
    | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('14',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( X21
       != ( k1_funct_1 @ X20 @ X19 ) )
      | ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( k1_funct_1 @ X20 @ X19 ) ) @ X20 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X17 ) @ X18 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X18 ) )
      | ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) ) @ ( k9_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_B @ ( k1_relat_1 @ sk_D_1 ) ) ) @ ( k9_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('25',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_B @ ( k1_relat_1 @ sk_D_1 ) ) ) @ ( k9_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_B @ ( k1_relat_1 @ sk_D_1 ) ) ) @ ( k9_relat_1 @ sk_D_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('36',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_B @ ( k1_relat_1 @ sk_D_1 ) ) ) @ ( k9_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(clc,[status(thm)],['27','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('43',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t52_relset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) )
                      <=> ? [F: $i] :
                            ( ( r2_hidden @ F @ B )
                            & ( r2_hidden @ ( k4_tarski @ F @ E ) @ D )
                            & ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X41 ) @ X37 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X0 ) @ sk_D_1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_E ) @ sk_D_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','52'])).

thf('54',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_E ) @ sk_D_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['53','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ( X21
        = ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('61',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('63',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('66',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( m1_subset_1 @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X38 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['65','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['28','31'])).

thf('75',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X41: $i] :
      ( ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( r2_hidden @ X41 @ ( k7_relset_1 @ X38 @ X39 @ X37 @ X36 ) )
      | ( r2_hidden @ ( sk_F @ X41 @ X37 @ X38 @ X36 ) @ X36 )
      | ~ ( m1_subset_1 @ X41 @ X39 )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t52_relset_1])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( sk_F @ X0 @ sk_D_1 @ sk_A @ X1 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ ( k9_relat_1 @ sk_D_1 @ X1 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_E @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ sk_B_1 ),
    inference('sup-',[status(thm)],['54','57'])).

thf('82',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X42: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X42 ) )
      | ~ ( r2_hidden @ X42 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X42 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','84'])).

thf('86',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_E != sk_E )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('91',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_1 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['88','93'])).

thf('95',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('96',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('104',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('107',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['94','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','108'])).

thf('110',plain,(
    $false ),
    inference('sup-',[status(thm)],['39','109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SoudF9Bvyj
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:28:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.83  % Solved by: fo/fo7.sh
% 0.62/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.83  % done 742 iterations in 0.415s
% 0.62/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.83  % SZS output start Refutation
% 0.62/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.62/0.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.62/0.83  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.62/0.83  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.62/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.83  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.62/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.62/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.83  thf(sk_F_type, type, sk_F: $i > $i > $i > $i > $i).
% 0.62/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.83  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.62/0.83  thf(sk_E_type, type, sk_E: $i).
% 0.62/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.83  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.62/0.83  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.62/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.62/0.83  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.62/0.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.62/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.62/0.83  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.62/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.83  thf(d1_xboole_0, axiom,
% 0.62/0.83    (![A:$i]:
% 0.62/0.83     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.83  thf('0', plain,
% 0.62/0.83      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.62/0.83      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.83  thf(t116_funct_2, conjecture,
% 0.62/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.83     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.62/0.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.62/0.83       ( ![E:$i]:
% 0.62/0.83         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.62/0.83              ( ![F:$i]:
% 0.62/0.83                ( ( m1_subset_1 @ F @ A ) =>
% 0.62/0.83                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.62/0.83                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.62/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.83        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.62/0.83            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.62/0.83          ( ![E:$i]:
% 0.62/0.83            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.62/0.83                 ( ![F:$i]:
% 0.62/0.83                   ( ( m1_subset_1 @ F @ A ) =>
% 0.62/0.83                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.62/0.83                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.62/0.83    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.62/0.83  thf('1', plain,
% 0.62/0.83      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(cc2_relset_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.62/0.83  thf('2', plain,
% 0.62/0.84      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.62/0.84         ((v4_relat_1 @ X25 @ X26)
% 0.62/0.84          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.62/0.84  thf('3', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.62/0.84      inference('sup-', [status(thm)], ['1', '2'])).
% 0.62/0.84  thf(d18_relat_1, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( v1_relat_1 @ B ) =>
% 0.62/0.84       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.62/0.84  thf('4', plain,
% 0.62/0.84      (![X13 : $i, X14 : $i]:
% 0.62/0.84         (~ (v4_relat_1 @ X13 @ X14)
% 0.62/0.84          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 0.62/0.84          | ~ (v1_relat_1 @ X13))),
% 0.62/0.84      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.62/0.84  thf('5', plain,
% 0.62/0.84      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['3', '4'])).
% 0.62/0.84  thf('6', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(cc1_relset_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84       ( v1_relat_1 @ C ) ))).
% 0.62/0.84  thf('7', plain,
% 0.62/0.84      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.62/0.84         ((v1_relat_1 @ X22)
% 0.62/0.84          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.62/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.62/0.84  thf('8', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.84  thf('9', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.62/0.84      inference('demod', [status(thm)], ['5', '8'])).
% 0.62/0.84  thf(d3_tarski, axiom,
% 0.62/0.84    (![A:$i,B:$i]:
% 0.62/0.84     ( ( r1_tarski @ A @ B ) <=>
% 0.62/0.84       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.62/0.84  thf('10', plain,
% 0.62/0.84      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.62/0.84         (~ (r2_hidden @ X3 @ X4)
% 0.62/0.84          | (r2_hidden @ X3 @ X5)
% 0.62/0.84          | ~ (r1_tarski @ X4 @ X5))),
% 0.62/0.84      inference('cnf', [status(esa)], [d3_tarski])).
% 0.62/0.84  thf('11', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.84  thf('12', plain,
% 0.62/0.84      (((v1_xboole_0 @ (k1_relat_1 @ sk_D_1))
% 0.62/0.84        | (r2_hidden @ (sk_B @ (k1_relat_1 @ sk_D_1)) @ sk_A))),
% 0.62/0.84      inference('sup-', [status(thm)], ['0', '11'])).
% 0.62/0.84  thf('13', plain,
% 0.62/0.84      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf('14', plain,
% 0.62/0.84      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf(t8_funct_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.62/0.84       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.62/0.84         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.62/0.84           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.62/0.84  thf('15', plain,
% 0.62/0.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.84         (~ (r2_hidden @ X19 @ (k1_relat_1 @ X20))
% 0.62/0.84          | ((X21) != (k1_funct_1 @ X20 @ X19))
% 0.62/0.84          | (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.62/0.84          | ~ (v1_funct_1 @ X20)
% 0.62/0.84          | ~ (v1_relat_1 @ X20))),
% 0.62/0.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.62/0.84  thf('16', plain,
% 0.62/0.84      (![X19 : $i, X20 : $i]:
% 0.62/0.84         (~ (v1_relat_1 @ X20)
% 0.62/0.84          | ~ (v1_funct_1 @ X20)
% 0.62/0.84          | (r2_hidden @ (k4_tarski @ X19 @ (k1_funct_1 @ X20 @ X19)) @ X20)
% 0.62/0.84          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X20)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['15'])).
% 0.62/0.84  thf('17', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.62/0.84          | (r2_hidden @ 
% 0.62/0.84             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.62/0.84              (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0)))) @ 
% 0.62/0.84             X0)
% 0.62/0.84          | ~ (v1_funct_1 @ X0)
% 0.62/0.84          | ~ (v1_relat_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['14', '16'])).
% 0.62/0.84  thf(t143_relat_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( v1_relat_1 @ C ) =>
% 0.62/0.84       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.62/0.84         ( ?[D:$i]:
% 0.62/0.84           ( ( r2_hidden @ D @ B ) & 
% 0.62/0.84             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.62/0.84             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.62/0.84  thf('18', plain,
% 0.62/0.84      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.62/0.84         (~ (r2_hidden @ X15 @ X16)
% 0.62/0.84          | ~ (r2_hidden @ (k4_tarski @ X15 @ X17) @ X18)
% 0.62/0.84          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X18))
% 0.62/0.84          | (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.62/0.84          | ~ (v1_relat_1 @ X18))),
% 0.62/0.84      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.62/0.84  thf('19', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         (~ (v1_relat_1 @ X0)
% 0.62/0.84          | ~ (v1_funct_1 @ X0)
% 0.62/0.84          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.62/0.84          | ~ (v1_relat_1 @ X0)
% 0.62/0.84          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 0.62/0.84             (k9_relat_1 @ X0 @ X1))
% 0.62/0.84          | ~ (r2_hidden @ (sk_B @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.62/0.84          | ~ (r2_hidden @ (sk_B @ (k1_relat_1 @ X0)) @ X1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['17', '18'])).
% 0.62/0.84  thf('20', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         (~ (r2_hidden @ (sk_B @ (k1_relat_1 @ X0)) @ X1)
% 0.62/0.84          | ~ (r2_hidden @ (sk_B @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.62/0.84          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 0.62/0.84             (k9_relat_1 @ X0 @ X1))
% 0.62/0.84          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.62/0.84          | ~ (v1_funct_1 @ X0)
% 0.62/0.84          | ~ (v1_relat_1 @ X0))),
% 0.62/0.84      inference('simplify', [status(thm)], ['19'])).
% 0.62/0.84  thf('21', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.62/0.84          | ~ (v1_relat_1 @ X0)
% 0.62/0.84          | ~ (v1_funct_1 @ X0)
% 0.62/0.84          | (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.62/0.84          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 0.62/0.84             (k9_relat_1 @ X0 @ X1))
% 0.62/0.84          | ~ (r2_hidden @ (sk_B @ (k1_relat_1 @ X0)) @ X1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['13', '20'])).
% 0.62/0.84  thf('22', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         (~ (r2_hidden @ (sk_B @ (k1_relat_1 @ X0)) @ X1)
% 0.62/0.84          | (r2_hidden @ (k1_funct_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) @ 
% 0.62/0.84             (k9_relat_1 @ X0 @ X1))
% 0.62/0.84          | ~ (v1_funct_1 @ X0)
% 0.62/0.84          | ~ (v1_relat_1 @ X0)
% 0.62/0.84          | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['21'])).
% 0.62/0.84  thf('23', plain,
% 0.62/0.84      (((v1_xboole_0 @ (k1_relat_1 @ sk_D_1))
% 0.62/0.84        | (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))
% 0.62/0.84        | ~ (v1_relat_1 @ sk_D_1)
% 0.62/0.84        | ~ (v1_funct_1 @ sk_D_1)
% 0.62/0.84        | (r2_hidden @ 
% 0.62/0.84           (k1_funct_1 @ sk_D_1 @ (sk_B @ (k1_relat_1 @ sk_D_1))) @ 
% 0.62/0.84           (k9_relat_1 @ sk_D_1 @ sk_A)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['12', '22'])).
% 0.62/0.84  thf('24', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.84  thf('25', plain, ((v1_funct_1 @ sk_D_1)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('26', plain,
% 0.62/0.84      (((v1_xboole_0 @ (k1_relat_1 @ sk_D_1))
% 0.62/0.84        | (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))
% 0.62/0.84        | (r2_hidden @ 
% 0.62/0.84           (k1_funct_1 @ sk_D_1 @ (sk_B @ (k1_relat_1 @ sk_D_1))) @ 
% 0.62/0.84           (k9_relat_1 @ sk_D_1 @ sk_A)))),
% 0.62/0.84      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.62/0.84  thf('27', plain,
% 0.62/0.84      (((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_B @ (k1_relat_1 @ sk_D_1))) @ 
% 0.62/0.84         (k9_relat_1 @ sk_D_1 @ sk_A))
% 0.62/0.84        | (v1_xboole_0 @ (k1_relat_1 @ sk_D_1)))),
% 0.62/0.84      inference('simplify', [status(thm)], ['26'])).
% 0.62/0.84  thf('28', plain,
% 0.62/0.84      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('29', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(redefinition_k7_relset_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.62/0.84  thf('30', plain,
% 0.62/0.84      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.62/0.84          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.62/0.84      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.62/0.84  thf('31', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.62/0.84           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.84  thf('32', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['28', '31'])).
% 0.62/0.84  thf('33', plain,
% 0.62/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.62/0.84         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.62/0.84          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ (k1_relat_1 @ X18))
% 0.62/0.84          | ~ (v1_relat_1 @ X18))),
% 0.62/0.84      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.62/0.84  thf('34', plain,
% 0.62/0.84      ((~ (v1_relat_1 @ sk_D_1)
% 0.62/0.84        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['32', '33'])).
% 0.62/0.84  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.84  thf('36', plain,
% 0.62/0.84      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['34', '35'])).
% 0.62/0.84  thf('37', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf('38', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['36', '37'])).
% 0.62/0.84  thf('39', plain,
% 0.62/0.84      ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_B @ (k1_relat_1 @ sk_D_1))) @ 
% 0.62/0.84        (k9_relat_1 @ sk_D_1 @ sk_A))),
% 0.62/0.84      inference('clc', [status(thm)], ['27', '38'])).
% 0.62/0.84  thf('40', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(dt_k7_relset_1, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.62/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.84       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.62/0.84  thf('41', plain,
% 0.62/0.84      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.62/0.84         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.62/0.84          | (m1_subset_1 @ (k7_relset_1 @ X29 @ X30 @ X28 @ X31) @ 
% 0.62/0.84             (k1_zfmisc_1 @ X30)))),
% 0.62/0.84      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.62/0.84  thf('42', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 0.62/0.84          (k1_zfmisc_1 @ sk_B_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.62/0.84  thf(t5_subset, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.62/0.84          ( v1_xboole_0 @ C ) ) ))).
% 0.62/0.84  thf('43', plain,
% 0.62/0.84      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.62/0.84         (~ (r2_hidden @ X10 @ X11)
% 0.62/0.84          | ~ (v1_xboole_0 @ X12)
% 0.62/0.84          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.62/0.84      inference('cnf', [status(esa)], [t5_subset])).
% 0.62/0.84  thf('44', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         (~ (v1_xboole_0 @ sk_B_1)
% 0.62/0.84          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['42', '43'])).
% 0.62/0.84  thf('45', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.62/0.84           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.84  thf('46', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         (~ (v1_xboole_0 @ sk_B_1)
% 0.62/0.84          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.62/0.84      inference('demod', [status(thm)], ['44', '45'])).
% 0.62/0.84  thf('47', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['28', '31'])).
% 0.62/0.84  thf('48', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf(t52_relset_1, axiom,
% 0.62/0.84    (![A:$i]:
% 0.62/0.84     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.62/0.84       ( ![B:$i]:
% 0.62/0.84         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.62/0.84           ( ![C:$i]:
% 0.62/0.84             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.62/0.84               ( ![D:$i]:
% 0.62/0.84                 ( ( m1_subset_1 @
% 0.62/0.84                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 0.62/0.84                   ( ![E:$i]:
% 0.62/0.84                     ( ( m1_subset_1 @ E @ A ) =>
% 0.62/0.84                       ( ( r2_hidden @ E @ ( k7_relset_1 @ C @ A @ D @ B ) ) <=>
% 0.62/0.84                         ( ?[F:$i]:
% 0.62/0.84                           ( ( r2_hidden @ F @ B ) & 
% 0.62/0.84                             ( r2_hidden @ ( k4_tarski @ F @ E ) @ D ) & 
% 0.62/0.84                             ( m1_subset_1 @ F @ C ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.62/0.84  thf('49', plain,
% 0.62/0.84      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ X36)
% 0.62/0.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.62/0.84          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.62/0.84          | (r2_hidden @ (k4_tarski @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X41) @ 
% 0.62/0.84             X37)
% 0.62/0.84          | ~ (m1_subset_1 @ X41 @ X39)
% 0.62/0.84          | (v1_xboole_0 @ X38)
% 0.62/0.84          | (v1_xboole_0 @ X39))),
% 0.62/0.84      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.62/0.84  thf('50', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ sk_B_1)
% 0.62/0.84          | (v1_xboole_0 @ sk_A)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.62/0.84          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.62/0.84             sk_D_1)
% 0.62/0.84          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.62/0.84          | (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['48', '49'])).
% 0.62/0.84  thf('51', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.62/0.84           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.84  thf('52', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ sk_B_1)
% 0.62/0.84          | (v1_xboole_0 @ sk_A)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.62/0.84          | (r2_hidden @ (k4_tarski @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X0) @ 
% 0.62/0.84             sk_D_1)
% 0.62/0.84          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.62/0.84          | (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('demod', [status(thm)], ['50', '51'])).
% 0.62/0.84  thf('53', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (r2_hidden @ 
% 0.62/0.84           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 0.62/0.84        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['47', '52'])).
% 0.62/0.84  thf('54', plain,
% 0.62/0.84      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('55', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 0.62/0.84          (k1_zfmisc_1 @ sk_B_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.62/0.84  thf(t4_subset, axiom,
% 0.62/0.84    (![A:$i,B:$i,C:$i]:
% 0.62/0.84     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.62/0.84       ( m1_subset_1 @ A @ C ) ))).
% 0.62/0.84  thf('56', plain,
% 0.62/0.84      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.62/0.84         (~ (r2_hidden @ X7 @ X8)
% 0.62/0.84          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.62/0.84          | (m1_subset_1 @ X7 @ X9))),
% 0.62/0.84      inference('cnf', [status(esa)], [t4_subset])).
% 0.62/0.84  thf('57', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((m1_subset_1 @ X1 @ sk_B_1)
% 0.62/0.84          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['55', '56'])).
% 0.62/0.84  thf('58', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.62/0.84      inference('sup-', [status(thm)], ['54', '57'])).
% 0.62/0.84  thf('59', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (r2_hidden @ 
% 0.62/0.84           (k4_tarski @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_E) @ sk_D_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['53', '58'])).
% 0.62/0.84  thf('60', plain,
% 0.62/0.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.84         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.62/0.84          | ((X21) = (k1_funct_1 @ X20 @ X19))
% 0.62/0.84          | ~ (v1_funct_1 @ X20)
% 0.62/0.84          | ~ (v1_relat_1 @ X20))),
% 0.62/0.84      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.62/0.84  thf('61', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | ~ (v1_relat_1 @ sk_D_1)
% 0.62/0.84        | ~ (v1_funct_1 @ sk_D_1)
% 0.62/0.84        | ((sk_E)
% 0.62/0.84            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.62/0.84  thf('62', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.84  thf('63', plain, ((v1_funct_1 @ sk_D_1)),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('64', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | ((sk_E)
% 0.62/0.84            = (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 0.62/0.84      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.62/0.84  thf('65', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['28', '31'])).
% 0.62/0.84  thf('66', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('67', plain,
% 0.62/0.84      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ X36)
% 0.62/0.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.62/0.84          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.62/0.84          | (m1_subset_1 @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X38)
% 0.62/0.84          | ~ (m1_subset_1 @ X41 @ X39)
% 0.62/0.84          | (v1_xboole_0 @ X38)
% 0.62/0.84          | (v1_xboole_0 @ X39))),
% 0.62/0.84      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.62/0.84  thf('68', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ sk_B_1)
% 0.62/0.84          | (v1_xboole_0 @ sk_A)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.62/0.84          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.62/0.84          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.62/0.84          | (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['66', '67'])).
% 0.62/0.84  thf('69', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.62/0.84           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.84  thf('70', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ sk_B_1)
% 0.62/0.84          | (v1_xboole_0 @ sk_A)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.62/0.84          | (m1_subset_1 @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ sk_A)
% 0.62/0.84          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.62/0.84          | (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('demod', [status(thm)], ['68', '69'])).
% 0.62/0.84  thf('71', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.62/0.84        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['65', '70'])).
% 0.62/0.84  thf('72', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.62/0.84      inference('sup-', [status(thm)], ['54', '57'])).
% 0.62/0.84  thf('73', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['71', '72'])).
% 0.62/0.84  thf('74', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['28', '31'])).
% 0.62/0.84  thf('75', plain,
% 0.62/0.84      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('76', plain,
% 0.62/0.84      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X41 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ X36)
% 0.62/0.84          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.62/0.84          | ~ (r2_hidden @ X41 @ (k7_relset_1 @ X38 @ X39 @ X37 @ X36))
% 0.62/0.84          | (r2_hidden @ (sk_F @ X41 @ X37 @ X38 @ X36) @ X36)
% 0.62/0.84          | ~ (m1_subset_1 @ X41 @ X39)
% 0.62/0.84          | (v1_xboole_0 @ X38)
% 0.62/0.84          | (v1_xboole_0 @ X39))),
% 0.62/0.84      inference('cnf', [status(esa)], [t52_relset_1])).
% 0.62/0.84  thf('77', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ sk_B_1)
% 0.62/0.84          | (v1_xboole_0 @ sk_A)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.62/0.84          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.62/0.84          | ~ (r2_hidden @ X0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X1))
% 0.62/0.84          | (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['75', '76'])).
% 0.62/0.84  thf('78', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.62/0.84           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.84  thf('79', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ sk_B_1)
% 0.62/0.84          | (v1_xboole_0 @ sk_A)
% 0.62/0.84          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 0.62/0.84          | (r2_hidden @ (sk_F @ X0 @ sk_D_1 @ sk_A @ X1) @ X1)
% 0.62/0.84          | ~ (r2_hidden @ X0 @ (k9_relat_1 @ sk_D_1 @ X1))
% 0.62/0.84          | (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('demod', [status(thm)], ['77', '78'])).
% 0.62/0.84  thf('80', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.62/0.84        | ~ (m1_subset_1 @ sk_E @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['74', '79'])).
% 0.62/0.84  thf('81', plain, ((m1_subset_1 @ sk_E @ sk_B_1)),
% 0.62/0.84      inference('sup-', [status(thm)], ['54', '57'])).
% 0.62/0.84  thf('82', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (r2_hidden @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_C_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['80', '81'])).
% 0.62/0.84  thf('83', plain,
% 0.62/0.84      (![X42 : $i]:
% 0.62/0.84         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X42))
% 0.62/0.84          | ~ (r2_hidden @ X42 @ sk_C_1)
% 0.62/0.84          | ~ (m1_subset_1 @ X42 @ sk_A))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('84', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | ~ (m1_subset_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1) @ sk_A)
% 0.62/0.84        | ((sk_E)
% 0.62/0.84            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1))))),
% 0.62/0.84      inference('sup-', [status(thm)], ['82', '83'])).
% 0.62/0.84  thf('85', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | ((sk_E)
% 0.62/0.84            != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 0.62/0.84        | (v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['73', '84'])).
% 0.62/0.84  thf('86', plain,
% 0.62/0.84      ((((sk_E)
% 0.62/0.84          != (k1_funct_1 @ sk_D_1 @ (sk_F @ sk_E @ sk_D_1 @ sk_A @ sk_C_1)))
% 0.62/0.84        | (v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('simplify', [status(thm)], ['85'])).
% 0.62/0.84  thf('87', plain,
% 0.62/0.84      ((((sk_E) != (sk_E))
% 0.62/0.84        | (v1_xboole_0 @ sk_C_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_B_1)
% 0.62/0.84        | (v1_xboole_0 @ sk_A)
% 0.62/0.84        | (v1_xboole_0 @ sk_C_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['64', '86'])).
% 0.62/0.84  thf('88', plain,
% 0.62/0.84      (((v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 0.62/0.84      inference('simplify', [status(thm)], ['87'])).
% 0.62/0.84  thf('89', plain,
% 0.62/0.84      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['34', '35'])).
% 0.62/0.84  thf('90', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.62/0.84      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.84  thf('91', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_1 @ sk_E) @ sk_A)),
% 0.62/0.84      inference('sup-', [status(thm)], ['89', '90'])).
% 0.62/0.84  thf('92', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf('93', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.62/0.84      inference('sup-', [status(thm)], ['91', '92'])).
% 0.62/0.84  thf('94', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1))),
% 0.62/0.84      inference('clc', [status(thm)], ['88', '93'])).
% 0.62/0.84  thf('95', plain,
% 0.62/0.84      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf('96', plain,
% 0.62/0.84      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.62/0.84         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.62/0.84          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 0.62/0.84          | ~ (v1_relat_1 @ X18))),
% 0.62/0.84      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.62/0.84  thf('97', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.62/0.84          | ~ (v1_relat_1 @ X1)
% 0.62/0.84          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.62/0.84             X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['95', '96'])).
% 0.62/0.84  thf('98', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf('99', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]:
% 0.62/0.84         (~ (v1_relat_1 @ X1)
% 0.62/0.84          | (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.62/0.84          | ~ (v1_xboole_0 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['97', '98'])).
% 0.62/0.84  thf('100', plain,
% 0.62/0.84      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.84  thf('101', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.84      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.84  thf('102', plain,
% 0.62/0.84      (~ (v1_xboole_0 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['100', '101'])).
% 0.62/0.84  thf('103', plain,
% 0.62/0.84      (![X0 : $i]:
% 0.62/0.84         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.62/0.84           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.62/0.84      inference('sup-', [status(thm)], ['29', '30'])).
% 0.62/0.84  thf('104', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.62/0.84      inference('demod', [status(thm)], ['102', '103'])).
% 0.62/0.84  thf('105', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_relat_1 @ sk_D_1))),
% 0.62/0.84      inference('sup-', [status(thm)], ['99', '104'])).
% 0.62/0.84  thf('106', plain, ((v1_relat_1 @ sk_D_1)),
% 0.62/0.84      inference('sup-', [status(thm)], ['6', '7'])).
% 0.62/0.84  thf('107', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.62/0.84      inference('demod', [status(thm)], ['105', '106'])).
% 0.62/0.84  thf('108', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.62/0.84      inference('clc', [status(thm)], ['94', '107'])).
% 0.62/0.84  thf('109', plain,
% 0.62/0.84      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0))),
% 0.62/0.84      inference('demod', [status(thm)], ['46', '108'])).
% 0.62/0.84  thf('110', plain, ($false), inference('sup-', [status(thm)], ['39', '109'])).
% 0.62/0.84  
% 0.62/0.84  % SZS output end Refutation
% 0.62/0.84  
% 0.62/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
