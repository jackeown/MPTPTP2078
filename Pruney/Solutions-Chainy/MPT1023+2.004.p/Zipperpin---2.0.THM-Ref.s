%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y8DTDTrIDv

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:29 EST 2020

% Result     : Theorem 3.50s
% Output     : Refutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :  270 (7313 expanded)
%              Number of leaves         :   48 (2365 expanded)
%              Depth                    :   43
%              Number of atoms          : 1957 (56041 expanded)
%              Number of equality atoms :  107 (1517 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf('10',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( sk_F @ X32 @ X33 @ X34 ) @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D )
      | ( r2_hidden @ ( sk_F @ sk_B_1 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( r2_hidden @ ( sk_F @ sk_B_1 @ sk_A @ ( sk_B @ sk_D ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v4_relat_1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('34',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v4_relat_1 @ ( k1_relat_1 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v4_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('45',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_relat_1 @ ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['41','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relat_1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(condensation,[status(thm)],['50'])).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v4_relat_1 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v4_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k1_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('61',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['23','26'])).

thf('65',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( X0
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','67'])).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('73',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('85',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['83','86'])).

thf('88',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38
       != ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( zip_tseitin_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 @ X1 )
      | ( v1_funct_2 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('92',plain,(
    ! [X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 )
      | ( X37 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('93',plain,(
    ! [X36: $i] :
      ( zip_tseitin_0 @ X36 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('95',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['90','91','97'])).

thf('99',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ X0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('103',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','103'])).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('110',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('112',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('117',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('122',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','122'])).

thf('124',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('125',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( sk_F @ X32 @ X33 @ X34 ) @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ ( sk_F @ sk_B_1 @ sk_A @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_F @ sk_B_1 @ sk_A @ ( sk_B @ sk_C_2 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['124','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['13','117'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C_2 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('132',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('134',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('136',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relset_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k1_relset_1 @ X2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['137','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['134','145'])).

thf('147',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('148',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( r2_hidden @ ( sk_E @ X32 @ X33 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t6_relset_1])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ ( sk_E @ sk_B_1 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r2_hidden @ ( sk_E @ sk_B_1 @ sk_A @ ( sk_B @ sk_C_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference(clc,[status(thm)],['146','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','31'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['159'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('161',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('162',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['160','162'])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference('sup+',[status(thm)],['156','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['155','165'])).

thf('167',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ~ ( v1_xboole_0 @ sk_C_2 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['154','168'])).

thf('170',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['123','169'])).

thf('171',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','170'])).

thf('172',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_2 @ X40 @ X38 @ X39 )
      | ( X38
        = ( k1_relset_1 @ X38 @ X39 @ X40 ) )
      | ~ ( zip_tseitin_1 @ X40 @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('174',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('177',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['174','177'])).

thf('179',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_D )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','118'])).

thf('180',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( zip_tseitin_0 @ X41 @ X42 )
      | ( zip_tseitin_1 @ X43 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('182',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['179','182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['154','168'])).

thf('185',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['183','184'])).

thf('186',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['178','185'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('187',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X18 ) @ ( k1_relat_1 @ X18 ) )
      | ( ( k1_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('188',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( k1_relat_1 @ sk_C_2 ) )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('191',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['178','185'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A )
      | ( sk_C_2 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['188','191','192','193'])).

thf('195',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['171','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('198',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_2 = sk_D )
    | ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['195','198','199'])).

thf('201',plain,
    ( ( r2_hidden @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(simplify,[status(thm)],['200'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('202',plain,(
    ! [X10: $i,X11: $i] :
      ( ( m1_subset_1 @ X10 @ X11 )
      | ~ ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('203',plain,
    ( ( sk_C_2 = sk_D )
    | ( m1_subset_1 @ ( sk_C_1 @ sk_D @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    ! [X44: $i] :
      ( ( ( k1_funct_1 @ sk_C_2 @ X44 )
        = ( k1_funct_1 @ sk_D @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( sk_C_2 = sk_D )
    | ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) ),
    inference(condensation,[status(thm)],['205'])).

thf('207',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ( X18 = X17 )
      | ( ( k1_funct_1 @ X18 @ ( sk_C_1 @ X17 @ X18 ) )
       != ( k1_funct_1 @ X17 @ ( sk_C_1 @ X17 @ X18 ) ) )
      | ( ( k1_relat_1 @ X18 )
       != ( k1_relat_1 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('208',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ( ( k1_relat_1 @ sk_C_2 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_2 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['189','190'])).

thf('210',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['178','185'])).

thf('212',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','170'])).

thf('213',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['196','197'])).

thf('215',plain,
    ( ( ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) )
     != ( k1_funct_1 @ sk_C_2 @ ( sk_C_1 @ sk_D @ sk_C_2 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_2 = sk_D ) ),
    inference(demod,[status(thm)],['208','209','210','211','212','213','214'])).

thf('216',plain,(
    sk_C_2 = sk_D ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('219',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2 ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    $false ),
    inference(demod,[status(thm)],['0','216','219'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y8DTDTrIDv
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:03:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 3.50/3.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.50/3.70  % Solved by: fo/fo7.sh
% 3.50/3.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.50/3.70  % done 3983 iterations in 3.247s
% 3.50/3.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.50/3.70  % SZS output start Refutation
% 3.50/3.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.50/3.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.50/3.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.50/3.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.50/3.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.50/3.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.50/3.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.50/3.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.50/3.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.50/3.70  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.50/3.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.50/3.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.50/3.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.50/3.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.50/3.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.50/3.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.50/3.70  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.50/3.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.50/3.70  thf(sk_D_type, type, sk_D: $i).
% 3.50/3.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.50/3.70  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 3.50/3.70  thf(sk_B_type, type, sk_B: $i > $i).
% 3.50/3.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.50/3.70  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 3.50/3.70  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.50/3.70  thf(sk_A_type, type, sk_A: $i).
% 3.50/3.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.50/3.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 3.50/3.70  thf(t113_funct_2, conjecture,
% 3.50/3.70    (![A:$i,B:$i,C:$i]:
% 3.50/3.70     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.50/3.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.70       ( ![D:$i]:
% 3.50/3.70         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.50/3.70             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.70           ( ( ![E:$i]:
% 3.50/3.70               ( ( m1_subset_1 @ E @ A ) =>
% 3.50/3.70                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.50/3.70             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 3.50/3.70  thf(zf_stmt_0, negated_conjecture,
% 3.50/3.70    (~( ![A:$i,B:$i,C:$i]:
% 3.50/3.70        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.50/3.70            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.70          ( ![D:$i]:
% 3.50/3.70            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.50/3.70                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.70              ( ( ![E:$i]:
% 3.50/3.70                  ( ( m1_subset_1 @ E @ A ) =>
% 3.50/3.70                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 3.50/3.70                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 3.50/3.70    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 3.50/3.70  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.70  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.70  thf(d1_funct_2, axiom,
% 3.50/3.70    (![A:$i,B:$i,C:$i]:
% 3.50/3.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.50/3.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.50/3.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.50/3.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.50/3.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.50/3.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.50/3.70  thf(zf_stmt_1, axiom,
% 3.50/3.70    (![C:$i,B:$i,A:$i]:
% 3.50/3.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.50/3.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.50/3.70  thf('2', plain,
% 3.50/3.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.50/3.70         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 3.50/3.70          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 3.50/3.70          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.50/3.70  thf('3', plain,
% 3.50/3.70      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['1', '2'])).
% 3.50/3.70  thf('4', plain,
% 3.50/3.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.70  thf(redefinition_k1_relset_1, axiom,
% 3.50/3.70    (![A:$i,B:$i,C:$i]:
% 3.50/3.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.50/3.70  thf('5', plain,
% 3.50/3.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.50/3.70         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 3.50/3.70          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.50/3.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.50/3.70  thf('6', plain,
% 3.50/3.70      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 3.50/3.70      inference('sup-', [status(thm)], ['4', '5'])).
% 3.50/3.70  thf('7', plain,
% 3.50/3.70      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.70        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.50/3.70      inference('demod', [status(thm)], ['3', '6'])).
% 3.50/3.70  thf(d1_xboole_0, axiom,
% 3.50/3.70    (![A:$i]:
% 3.50/3.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.50/3.70  thf('8', plain,
% 3.50/3.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.50/3.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.70  thf('9', plain,
% 3.50/3.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.70  thf(t6_relset_1, axiom,
% 3.50/3.70    (![A:$i,B:$i,C:$i,D:$i]:
% 3.50/3.70     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 3.50/3.70       ( ~( ( r2_hidden @ A @ D ) & 
% 3.50/3.70            ( ![E:$i,F:$i]:
% 3.50/3.70              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 3.50/3.70                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 3.50/3.70  thf('10', plain,
% 3.50/3.70      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.50/3.70         ((r2_hidden @ (sk_F @ X32 @ X33 @ X34) @ X32)
% 3.50/3.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.50/3.70          | ~ (r2_hidden @ X34 @ X35))),
% 3.50/3.70      inference('cnf', [status(esa)], [t6_relset_1])).
% 3.50/3.70  thf('11', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X0 @ sk_D)
% 3.50/3.70          | (r2_hidden @ (sk_F @ sk_B_1 @ sk_A @ X0) @ sk_B_1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['9', '10'])).
% 3.50/3.70  thf('12', plain,
% 3.50/3.70      (((v1_xboole_0 @ sk_D)
% 3.50/3.70        | (r2_hidden @ (sk_F @ sk_B_1 @ sk_A @ (sk_B @ sk_D)) @ sk_B_1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['8', '11'])).
% 3.50/3.70  thf(zf_stmt_2, axiom,
% 3.50/3.70    (![B:$i,A:$i]:
% 3.50/3.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.50/3.70       ( zip_tseitin_0 @ B @ A ) ))).
% 3.50/3.70  thf('13', plain,
% 3.50/3.70      (![X36 : $i, X37 : $i]:
% 3.50/3.70         ((zip_tseitin_0 @ X36 @ X37) | ((X36) = (k1_xboole_0)))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.50/3.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.50/3.70  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.70  thf(d3_tarski, axiom,
% 3.50/3.70    (![A:$i,B:$i]:
% 3.50/3.70     ( ( r1_tarski @ A @ B ) <=>
% 3.50/3.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 3.50/3.70  thf('15', plain,
% 3.50/3.70      (![X4 : $i, X6 : $i]:
% 3.50/3.70         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 3.50/3.70      inference('cnf', [status(esa)], [d3_tarski])).
% 3.50/3.70  thf('16', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.70  thf('17', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['15', '16'])).
% 3.50/3.70  thf(t3_subset, axiom,
% 3.50/3.70    (![A:$i,B:$i]:
% 3.50/3.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.50/3.70  thf('18', plain,
% 3.50/3.70      (![X12 : $i, X14 : $i]:
% 3.50/3.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 3.50/3.70      inference('cnf', [status(esa)], [t3_subset])).
% 3.50/3.70  thf('19', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['17', '18'])).
% 3.50/3.70  thf(cc2_relset_1, axiom,
% 3.50/3.70    (![A:$i,B:$i,C:$i]:
% 3.50/3.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.50/3.70  thf('20', plain,
% 3.50/3.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.50/3.70         ((v4_relat_1 @ X22 @ X23)
% 3.50/3.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.50/3.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.50/3.70  thf('21', plain,
% 3.50/3.70      (![X1 : $i, X2 : $i]: (~ (v1_xboole_0 @ X2) | (v4_relat_1 @ X2 @ X1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['19', '20'])).
% 3.50/3.70  thf(d18_relat_1, axiom,
% 3.50/3.70    (![A:$i,B:$i]:
% 3.50/3.70     ( ( v1_relat_1 @ B ) =>
% 3.50/3.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.50/3.70  thf('22', plain,
% 3.50/3.70      (![X15 : $i, X16 : $i]:
% 3.50/3.70         (~ (v4_relat_1 @ X15 @ X16)
% 3.50/3.70          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 3.50/3.70          | ~ (v1_relat_1 @ X15))),
% 3.50/3.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.50/3.70  thf('23', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ~ (v1_relat_1 @ X1)
% 3.50/3.70          | (r1_tarski @ (k1_relat_1 @ X1) @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['21', '22'])).
% 3.50/3.70  thf('24', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['17', '18'])).
% 3.50/3.70  thf(cc1_relset_1, axiom,
% 3.50/3.70    (![A:$i,B:$i,C:$i]:
% 3.50/3.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.70       ( v1_relat_1 @ C ) ))).
% 3.50/3.70  thf('25', plain,
% 3.50/3.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.50/3.70         ((v1_relat_1 @ X19)
% 3.50/3.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.50/3.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.70  thf('26', plain, (![X2 : $i]: (~ (v1_xboole_0 @ X2) | (v1_relat_1 @ X2))),
% 3.50/3.70      inference('sup-', [status(thm)], ['24', '25'])).
% 3.50/3.70  thf('27', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((r1_tarski @ (k1_relat_1 @ X1) @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('clc', [status(thm)], ['23', '26'])).
% 3.50/3.70  thf('28', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['15', '16'])).
% 3.50/3.70  thf(d10_xboole_0, axiom,
% 3.50/3.70    (![A:$i,B:$i]:
% 3.50/3.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.50/3.70  thf('29', plain,
% 3.50/3.70      (![X7 : $i, X9 : $i]:
% 3.50/3.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.50/3.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.50/3.70  thf('30', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['28', '29'])).
% 3.50/3.70  thf('31', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ((k1_relat_1 @ X1) = (X0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['27', '30'])).
% 3.50/3.70  thf('32', plain,
% 3.50/3.70      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['14', '31'])).
% 3.50/3.70  thf('33', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((r1_tarski @ (k1_relat_1 @ X1) @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('clc', [status(thm)], ['23', '26'])).
% 3.50/3.70  thf('34', plain,
% 3.50/3.70      (![X12 : $i, X14 : $i]:
% 3.50/3.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 3.50/3.70      inference('cnf', [status(esa)], [t3_subset])).
% 3.50/3.70  thf('35', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | (m1_subset_1 @ (k1_relat_1 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['33', '34'])).
% 3.50/3.70  thf('36', plain,
% 3.50/3.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.50/3.70         ((v4_relat_1 @ X22 @ X23)
% 3.50/3.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.50/3.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.50/3.70  thf('37', plain,
% 3.50/3.70      (![X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X2) | (v4_relat_1 @ (k1_relat_1 @ X2) @ X1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['35', '36'])).
% 3.50/3.70  thf('38', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((v4_relat_1 @ k1_xboole_0 @ X0)
% 3.50/3.70          | ~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('sup+', [status(thm)], ['32', '37'])).
% 3.50/3.70  thf('39', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1) | (v4_relat_1 @ k1_xboole_0 @ X0))),
% 3.50/3.70      inference('simplify', [status(thm)], ['38'])).
% 3.50/3.70  thf('40', plain,
% 3.50/3.70      (![X15 : $i, X16 : $i]:
% 3.50/3.70         (~ (v4_relat_1 @ X15 @ X16)
% 3.50/3.70          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 3.50/3.70          | ~ (v1_relat_1 @ X15))),
% 3.50/3.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.50/3.70  thf('41', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 3.50/3.70          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['39', '40'])).
% 3.50/3.70  thf('42', plain,
% 3.50/3.70      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['14', '31'])).
% 3.50/3.70  thf('43', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | (m1_subset_1 @ (k1_relat_1 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['33', '34'])).
% 3.50/3.70  thf('44', plain,
% 3.50/3.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.50/3.70         ((v1_relat_1 @ X19)
% 3.50/3.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.50/3.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.70  thf('45', plain,
% 3.50/3.70      (![X2 : $i]: (~ (v1_xboole_0 @ X2) | (v1_relat_1 @ (k1_relat_1 @ X2)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['43', '44'])).
% 3.50/3.70  thf('46', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         ((v1_relat_1 @ k1_xboole_0)
% 3.50/3.70          | ~ (v1_xboole_0 @ X0)
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup+', [status(thm)], ['42', '45'])).
% 3.50/3.70  thf('47', plain,
% 3.50/3.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 3.50/3.70      inference('simplify', [status(thm)], ['46'])).
% 3.50/3.70  thf('48', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('clc', [status(thm)], ['41', '47'])).
% 3.50/3.70  thf('49', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['28', '29'])).
% 3.50/3.70  thf('50', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ((k1_relat_1 @ k1_xboole_0) = (X0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['48', '49'])).
% 3.50/3.70  thf('51', plain,
% 3.50/3.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_relat_1 @ k1_xboole_0) = (X0)))),
% 3.50/3.70      inference('condensation', [status(thm)], ['50'])).
% 3.50/3.70  thf('52', plain,
% 3.50/3.70      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 3.50/3.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.50/3.70  thf('53', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 3.50/3.70      inference('simplify', [status(thm)], ['52'])).
% 3.50/3.70  thf('54', plain,
% 3.50/3.70      (![X12 : $i, X14 : $i]:
% 3.50/3.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 3.50/3.70      inference('cnf', [status(esa)], [t3_subset])).
% 3.50/3.70  thf('55', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['53', '54'])).
% 3.50/3.70  thf('56', plain,
% 3.50/3.70      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.50/3.70         ((v4_relat_1 @ X22 @ X23)
% 3.50/3.70          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 3.50/3.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.50/3.70  thf('57', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 3.50/3.70      inference('sup-', [status(thm)], ['55', '56'])).
% 3.50/3.70  thf('58', plain,
% 3.50/3.70      (![X15 : $i, X16 : $i]:
% 3.50/3.70         (~ (v4_relat_1 @ X15 @ X16)
% 3.50/3.70          | (r1_tarski @ (k1_relat_1 @ X15) @ X16)
% 3.50/3.70          | ~ (v1_relat_1 @ X15))),
% 3.50/3.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.50/3.70  thf('59', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 3.50/3.70          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['57', '58'])).
% 3.50/3.70  thf('60', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['53', '54'])).
% 3.50/3.70  thf('61', plain,
% 3.50/3.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.50/3.70         ((v1_relat_1 @ X19)
% 3.50/3.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.50/3.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.70  thf('62', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['60', '61'])).
% 3.50/3.70  thf('63', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 3.50/3.70      inference('demod', [status(thm)], ['59', '62'])).
% 3.50/3.70  thf('64', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((r1_tarski @ (k1_relat_1 @ X1) @ X0) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('clc', [status(thm)], ['23', '26'])).
% 3.50/3.70  thf('65', plain,
% 3.50/3.70      (![X7 : $i, X9 : $i]:
% 3.50/3.70         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 3.50/3.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.50/3.70  thf('66', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ~ (r1_tarski @ X0 @ (k1_relat_1 @ X1))
% 3.50/3.70          | ((X0) = (k1_relat_1 @ X1)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['64', '65'])).
% 3.50/3.70  thf('67', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (((k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1))
% 3.50/3.70            = (k1_relat_1 @ X0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['63', '66'])).
% 3.50/3.70  thf('68', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k1_relat_1 @ k1_xboole_0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0)
% 3.50/3.70          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.50/3.70      inference('sup+', [status(thm)], ['51', '67'])).
% 3.50/3.70  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.70  thf('70', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k1_relat_1 @ k1_xboole_0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('demod', [status(thm)], ['68', '69'])).
% 3.50/3.70  thf('71', plain,
% 3.50/3.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.50/3.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.70  thf('72', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 3.50/3.70      inference('demod', [status(thm)], ['59', '62'])).
% 3.50/3.70  thf('73', plain,
% 3.50/3.70      (![X3 : $i, X4 : $i, X5 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X3 @ X4)
% 3.50/3.70          | (r2_hidden @ X3 @ X5)
% 3.50/3.70          | ~ (r1_tarski @ X4 @ X5))),
% 3.50/3.70      inference('cnf', [status(esa)], [d3_tarski])).
% 3.50/3.70  thf('74', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         ((r2_hidden @ X2 @ X0)
% 3.50/3.70          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 3.50/3.70      inference('sup-', [status(thm)], ['72', '73'])).
% 3.50/3.70  thf('75', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((v1_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))
% 3.50/3.70          | (r2_hidden @ (sk_B @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))) @ X1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['71', '74'])).
% 3.50/3.70  thf('76', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.70  thf('77', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((v1_xboole_0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['75', '76'])).
% 3.50/3.70  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.70  thf('79', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['15', '16'])).
% 3.50/3.70  thf('80', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['28', '29'])).
% 3.50/3.70  thf('81', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['79', '80'])).
% 3.50/3.70  thf('82', plain,
% 3.50/3.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['78', '81'])).
% 3.50/3.70  thf('83', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ((k1_xboole_0) = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.50/3.70      inference('sup-', [status(thm)], ['77', '82'])).
% 3.50/3.70  thf('84', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['53', '54'])).
% 3.50/3.70  thf('85', plain,
% 3.50/3.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.50/3.70         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 3.50/3.70          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.50/3.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.50/3.70  thf('86', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.50/3.70           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['84', '85'])).
% 3.50/3.70  thf('87', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0)) = (k1_xboole_0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('sup+', [status(thm)], ['83', '86'])).
% 3.50/3.70  thf('88', plain,
% 3.50/3.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.50/3.70         (((X38) != (k1_relset_1 @ X38 @ X39 @ X40))
% 3.50/3.70          | (v1_funct_2 @ X40 @ X38 @ X39)
% 3.50/3.70          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.50/3.70  thf('89', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (((X1) != (k1_xboole_0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ~ (zip_tseitin_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0 @ X1)
% 3.50/3.70          | (v1_funct_2 @ (k2_zfmisc_1 @ X1 @ X0) @ X1 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['87', '88'])).
% 3.50/3.70  thf('90', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         ((v1_funct_2 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ X0)
% 3.50/3.70          | ~ (zip_tseitin_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ X0 @ 
% 3.50/3.70               k1_xboole_0)
% 3.50/3.70          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.50/3.70      inference('simplify', [status(thm)], ['89'])).
% 3.50/3.70  thf('91', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.70  thf('92', plain,
% 3.50/3.70      (![X36 : $i, X37 : $i]:
% 3.50/3.70         ((zip_tseitin_0 @ X36 @ X37) | ((X37) != (k1_xboole_0)))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.50/3.70  thf('93', plain, (![X36 : $i]: (zip_tseitin_0 @ X36 @ k1_xboole_0)),
% 3.50/3.70      inference('simplify', [status(thm)], ['92'])).
% 3.50/3.70  thf('94', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['53', '54'])).
% 3.50/3.70  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.50/3.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.50/3.70  thf(zf_stmt_5, axiom,
% 3.50/3.70    (![A:$i,B:$i,C:$i]:
% 3.50/3.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.50/3.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.50/3.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.50/3.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.50/3.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.50/3.70  thf('95', plain,
% 3.50/3.70      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.50/3.70         (~ (zip_tseitin_0 @ X41 @ X42)
% 3.50/3.70          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 3.50/3.70          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.50/3.70  thf('96', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((zip_tseitin_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0 @ X1)
% 3.50/3.70          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['94', '95'])).
% 3.50/3.70  thf('97', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         (zip_tseitin_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ X0 @ k1_xboole_0)),
% 3.50/3.70      inference('sup-', [status(thm)], ['93', '96'])).
% 3.50/3.70  thf('98', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         (v1_funct_2 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ X0)),
% 3.50/3.70      inference('simplify_reflect+', [status(thm)], ['90', '91', '97'])).
% 3.50/3.70  thf('99', plain,
% 3.50/3.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.50/3.70         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 3.50/3.70          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 3.50/3.70          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.50/3.70  thf('100', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         (~ (zip_tseitin_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ X0 @ 
% 3.50/3.70             k1_xboole_0)
% 3.50/3.70          | ((k1_xboole_0)
% 3.50/3.70              = (k1_relset_1 @ k1_xboole_0 @ X0 @ 
% 3.50/3.70                 (k2_zfmisc_1 @ k1_xboole_0 @ X0))))),
% 3.50/3.70      inference('sup-', [status(thm)], ['98', '99'])).
% 3.50/3.70  thf('101', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         (zip_tseitin_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0) @ X0 @ k1_xboole_0)),
% 3.50/3.70      inference('sup-', [status(thm)], ['93', '96'])).
% 3.50/3.70  thf('102', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((k1_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0))
% 3.50/3.70           = (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['84', '85'])).
% 3.50/3.70  thf('103', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         ((k1_xboole_0) = (k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)))),
% 3.50/3.70      inference('demod', [status(thm)], ['100', '101', '102'])).
% 3.50/3.70  thf('104', plain,
% 3.50/3.70      ((((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 3.50/3.70        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.50/3.70      inference('sup+', [status(thm)], ['70', '103'])).
% 3.50/3.70  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.70  thf('106', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 3.50/3.70      inference('demod', [status(thm)], ['104', '105'])).
% 3.50/3.70  thf('107', plain,
% 3.50/3.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['78', '81'])).
% 3.50/3.70  thf('108', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (((k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) = (k1_relat_1 @ k1_xboole_0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('demod', [status(thm)], ['68', '69'])).
% 3.50/3.70  thf('109', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         ((r2_hidden @ X2 @ X0)
% 3.50/3.70          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 3.50/3.70      inference('sup-', [status(thm)], ['72', '73'])).
% 3.50/3.70  thf('110', plain,
% 3.50/3.70      (![X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X2 @ (k1_relat_1 @ k1_xboole_0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X1)
% 3.50/3.70          | (r2_hidden @ X2 @ X1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['108', '109'])).
% 3.50/3.70  thf('111', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.70  thf('112', plain,
% 3.50/3.70      (![X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ k1_xboole_0)))),
% 3.50/3.70      inference('clc', [status(thm)], ['110', '111'])).
% 3.50/3.70  thf('113', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0)
% 3.50/3.70          | ~ (v1_xboole_0 @ X2))),
% 3.50/3.70      inference('sup-', [status(thm)], ['107', '112'])).
% 3.50/3.70  thf('114', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('condensation', [status(thm)], ['113'])).
% 3.50/3.70  thf('115', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['106', '114'])).
% 3.50/3.70  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.70  thf('117', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.50/3.70      inference('demod', [status(thm)], ['115', '116'])).
% 3.50/3.70  thf('118', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.50/3.70      inference('sup-', [status(thm)], ['13', '117'])).
% 3.50/3.70  thf('119', plain,
% 3.50/3.70      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['12', '118'])).
% 3.50/3.70  thf('120', plain,
% 3.50/3.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.70  thf('121', plain,
% 3.50/3.70      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.50/3.70         (~ (zip_tseitin_0 @ X41 @ X42)
% 3.50/3.70          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 3.50/3.70          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.50/3.70  thf('122', plain,
% 3.50/3.70      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.70        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.50/3.70      inference('sup-', [status(thm)], ['120', '121'])).
% 3.50/3.70  thf('123', plain,
% 3.50/3.70      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.50/3.70      inference('sup-', [status(thm)], ['119', '122'])).
% 3.50/3.70  thf('124', plain,
% 3.50/3.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.50/3.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.70  thf('125', plain,
% 3.50/3.70      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.70  thf('126', plain,
% 3.50/3.70      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.50/3.70         ((r2_hidden @ (sk_F @ X32 @ X33 @ X34) @ X32)
% 3.50/3.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.50/3.70          | ~ (r2_hidden @ X34 @ X35))),
% 3.50/3.70      inference('cnf', [status(esa)], [t6_relset_1])).
% 3.50/3.70  thf('127', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X0 @ sk_C_2)
% 3.50/3.70          | (r2_hidden @ (sk_F @ sk_B_1 @ sk_A @ X0) @ sk_B_1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['125', '126'])).
% 3.50/3.70  thf('128', plain,
% 3.50/3.70      (((v1_xboole_0 @ sk_C_2)
% 3.50/3.70        | (r2_hidden @ (sk_F @ sk_B_1 @ sk_A @ (sk_B @ sk_C_2)) @ sk_B_1))),
% 3.50/3.70      inference('sup-', [status(thm)], ['124', '127'])).
% 3.50/3.70  thf('129', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 3.50/3.70      inference('sup-', [status(thm)], ['13', '117'])).
% 3.50/3.70  thf('130', plain,
% 3.50/3.70      (![X0 : $i]: ((v1_xboole_0 @ sk_C_2) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['128', '129'])).
% 3.50/3.70  thf('131', plain,
% 3.50/3.70      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.70        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.50/3.70      inference('sup-', [status(thm)], ['120', '121'])).
% 3.50/3.70  thf('132', plain,
% 3.50/3.70      (((v1_xboole_0 @ sk_C_2) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 3.50/3.70      inference('sup-', [status(thm)], ['130', '131'])).
% 3.50/3.70  thf('133', plain,
% 3.50/3.70      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 3.50/3.70        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.50/3.70      inference('demod', [status(thm)], ['3', '6'])).
% 3.50/3.70  thf('134', plain,
% 3.50/3.70      (((v1_xboole_0 @ sk_C_2) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['132', '133'])).
% 3.50/3.70  thf('135', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['17', '18'])).
% 3.50/3.70  thf('136', plain,
% 3.50/3.70      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.50/3.70         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 3.50/3.70          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.50/3.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.50/3.70  thf('137', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X2)
% 3.50/3.70          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['135', '136'])).
% 3.50/3.70  thf('138', plain,
% 3.50/3.70      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['14', '31'])).
% 3.50/3.70  thf('139', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X2)
% 3.50/3.70          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['135', '136'])).
% 3.50/3.70  thf('140', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         (((k1_relset_1 @ X2 @ X1 @ X0) = (k1_xboole_0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0)
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup+', [status(thm)], ['138', '139'])).
% 3.50/3.70  thf('141', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X0) | ((k1_relset_1 @ X2 @ X1 @ X0) = (k1_xboole_0)))),
% 3.50/3.70      inference('simplify', [status(thm)], ['140'])).
% 3.50/3.70  thf('142', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.50/3.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.50/3.70  thf('143', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.70         ((v1_xboole_0 @ (k1_relset_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup+', [status(thm)], ['141', '142'])).
% 3.50/3.70  thf('144', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X0)
% 3.50/3.70          | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup+', [status(thm)], ['137', '143'])).
% 3.50/3.70  thf('145', plain,
% 3.50/3.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 3.50/3.70      inference('simplify', [status(thm)], ['144'])).
% 3.50/3.70  thf('146', plain,
% 3.50/3.70      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 3.50/3.70      inference('sup+', [status(thm)], ['134', '145'])).
% 3.50/3.70  thf('147', plain,
% 3.50/3.70      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.50/3.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.70  thf('148', plain,
% 3.50/3.70      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.70  thf('149', plain,
% 3.50/3.70      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 3.50/3.70         ((r2_hidden @ (sk_E @ X32 @ X33 @ X34) @ X33)
% 3.50/3.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 3.50/3.70          | ~ (r2_hidden @ X34 @ X35))),
% 3.50/3.70      inference('cnf', [status(esa)], [t6_relset_1])).
% 3.50/3.70  thf('150', plain,
% 3.50/3.70      (![X0 : $i]:
% 3.50/3.70         (~ (r2_hidden @ X0 @ sk_C_2)
% 3.50/3.70          | (r2_hidden @ (sk_E @ sk_B_1 @ sk_A @ X0) @ sk_A))),
% 3.50/3.70      inference('sup-', [status(thm)], ['148', '149'])).
% 3.50/3.70  thf('151', plain,
% 3.50/3.70      (((v1_xboole_0 @ sk_C_2)
% 3.50/3.70        | (r2_hidden @ (sk_E @ sk_B_1 @ sk_A @ (sk_B @ sk_C_2)) @ sk_A))),
% 3.50/3.70      inference('sup-', [status(thm)], ['147', '150'])).
% 3.50/3.70  thf('152', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.50/3.70  thf('153', plain, (((v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_A))),
% 3.50/3.70      inference('sup-', [status(thm)], ['151', '152'])).
% 3.50/3.70  thf('154', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C_2))),
% 3.50/3.70      inference('clc', [status(thm)], ['146', '153'])).
% 3.50/3.70  thf('155', plain,
% 3.50/3.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['78', '81'])).
% 3.50/3.70  thf('156', plain,
% 3.50/3.70      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['78', '81'])).
% 3.50/3.70  thf('157', plain,
% 3.50/3.70      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.70      inference('sup-', [status(thm)], ['14', '31'])).
% 3.50/3.70  thf('158', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | (m1_subset_1 @ (k1_relat_1 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 3.50/3.70      inference('sup-', [status(thm)], ['33', '34'])).
% 3.50/3.70  thf('159', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.50/3.70          | ~ (v1_xboole_0 @ X1)
% 3.50/3.70          | ~ (v1_xboole_0 @ X1))),
% 3.50/3.70      inference('sup+', [status(thm)], ['157', '158'])).
% 3.50/3.70  thf('160', plain,
% 3.50/3.70      (![X0 : $i, X1 : $i]:
% 3.50/3.70         (~ (v1_xboole_0 @ X1)
% 3.50/3.70          | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0)))),
% 3.50/3.70      inference('simplify', [status(thm)], ['159'])).
% 3.50/3.70  thf(redefinition_r2_relset_1, axiom,
% 3.50/3.70    (![A:$i,B:$i,C:$i,D:$i]:
% 3.50/3.70     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.50/3.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.50/3.70       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.50/3.70  thf('161', plain,
% 3.50/3.70      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.50/3.70         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.50/3.70          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 3.50/3.70          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 3.50/3.70          | ((X28) != (X31)))),
% 3.50/3.70      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.50/3.70  thf('162', plain,
% 3.50/3.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.50/3.70         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 3.50/3.71          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 3.50/3.71      inference('simplify', [status(thm)], ['161'])).
% 3.50/3.71  thf('163', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         (~ (v1_xboole_0 @ X2)
% 3.50/3.71          | (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0))),
% 3.50/3.71      inference('sup-', [status(thm)], ['160', '162'])).
% 3.50/3.71  thf('164', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.50/3.71         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0)
% 3.50/3.71          | ~ (v1_xboole_0 @ X0)
% 3.50/3.71          | ~ (v1_xboole_0 @ X3))),
% 3.50/3.71      inference('sup+', [status(thm)], ['156', '163'])).
% 3.50/3.71  thf('165', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.50/3.71         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 3.50/3.71      inference('condensation', [status(thm)], ['164'])).
% 3.50/3.71  thf('166', plain,
% 3.50/3.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.50/3.71         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 3.50/3.71          | ~ (v1_xboole_0 @ X0)
% 3.50/3.71          | ~ (v1_xboole_0 @ X1))),
% 3.50/3.71      inference('sup+', [status(thm)], ['155', '165'])).
% 3.50/3.71  thf('167', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('168', plain, ((~ (v1_xboole_0 @ sk_C_2) | ~ (v1_xboole_0 @ sk_D))),
% 3.50/3.71      inference('sup-', [status(thm)], ['166', '167'])).
% 3.50/3.71  thf('169', plain, (~ (v1_xboole_0 @ sk_D)),
% 3.50/3.71      inference('clc', [status(thm)], ['154', '168'])).
% 3.50/3.71  thf('170', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 3.50/3.71      inference('clc', [status(thm)], ['123', '169'])).
% 3.50/3.71  thf('171', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.50/3.71      inference('demod', [status(thm)], ['7', '170'])).
% 3.50/3.71  thf('172', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B_1)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('173', plain,
% 3.50/3.71      (![X38 : $i, X39 : $i, X40 : $i]:
% 3.50/3.71         (~ (v1_funct_2 @ X40 @ X38 @ X39)
% 3.50/3.71          | ((X38) = (k1_relset_1 @ X38 @ X39 @ X40))
% 3.50/3.71          | ~ (zip_tseitin_1 @ X40 @ X39 @ X38))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.50/3.71  thf('174', plain,
% 3.50/3.71      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.50/3.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2)))),
% 3.50/3.71      inference('sup-', [status(thm)], ['172', '173'])).
% 3.50/3.71  thf('175', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('176', plain,
% 3.50/3.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 3.50/3.71         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 3.50/3.71          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 3.50/3.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.50/3.71  thf('177', plain,
% 3.50/3.71      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 3.50/3.71      inference('sup-', [status(thm)], ['175', '176'])).
% 3.50/3.71  thf('178', plain,
% 3.50/3.71      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.50/3.71        | ((sk_A) = (k1_relat_1 @ sk_C_2)))),
% 3.50/3.71      inference('demod', [status(thm)], ['174', '177'])).
% 3.50/3.71  thf('179', plain,
% 3.50/3.71      (![X0 : $i]: ((v1_xboole_0 @ sk_D) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 3.50/3.71      inference('sup-', [status(thm)], ['12', '118'])).
% 3.50/3.71  thf('180', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('181', plain,
% 3.50/3.71      (![X41 : $i, X42 : $i, X43 : $i]:
% 3.50/3.71         (~ (zip_tseitin_0 @ X41 @ X42)
% 3.50/3.71          | (zip_tseitin_1 @ X43 @ X41 @ X42)
% 3.50/3.71          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41))))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.50/3.71  thf('182', plain,
% 3.50/3.71      (((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)
% 3.50/3.71        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 3.50/3.71      inference('sup-', [status(thm)], ['180', '181'])).
% 3.50/3.71  thf('183', plain,
% 3.50/3.71      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A))),
% 3.50/3.71      inference('sup-', [status(thm)], ['179', '182'])).
% 3.50/3.71  thf('184', plain, (~ (v1_xboole_0 @ sk_D)),
% 3.50/3.71      inference('clc', [status(thm)], ['154', '168'])).
% 3.50/3.71  thf('185', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B_1 @ sk_A)),
% 3.50/3.71      inference('clc', [status(thm)], ['183', '184'])).
% 3.50/3.71  thf('186', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.50/3.71      inference('demod', [status(thm)], ['178', '185'])).
% 3.50/3.71  thf(t9_funct_1, axiom,
% 3.50/3.71    (![A:$i]:
% 3.50/3.71     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 3.50/3.71       ( ![B:$i]:
% 3.50/3.71         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.50/3.71           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 3.50/3.71               ( ![C:$i]:
% 3.50/3.71                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 3.50/3.71                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 3.50/3.71             ( ( A ) = ( B ) ) ) ) ) ))).
% 3.50/3.71  thf('187', plain,
% 3.50/3.71      (![X17 : $i, X18 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X17)
% 3.50/3.71          | ~ (v1_funct_1 @ X17)
% 3.50/3.71          | ((X18) = (X17))
% 3.50/3.71          | (r2_hidden @ (sk_C_1 @ X17 @ X18) @ (k1_relat_1 @ X18))
% 3.50/3.71          | ((k1_relat_1 @ X18) != (k1_relat_1 @ X17))
% 3.50/3.71          | ~ (v1_funct_1 @ X18)
% 3.50/3.71          | ~ (v1_relat_1 @ X18))),
% 3.50/3.71      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.50/3.71  thf('188', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((sk_A) != (k1_relat_1 @ X0))
% 3.50/3.71          | ~ (v1_relat_1 @ sk_C_2)
% 3.50/3.71          | ~ (v1_funct_1 @ sk_C_2)
% 3.50/3.71          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ (k1_relat_1 @ sk_C_2))
% 3.50/3.71          | ((sk_C_2) = (X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('sup-', [status(thm)], ['186', '187'])).
% 3.50/3.71  thf('189', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('190', plain,
% 3.50/3.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.50/3.71         ((v1_relat_1 @ X19)
% 3.50/3.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.50/3.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.71  thf('191', plain, ((v1_relat_1 @ sk_C_2)),
% 3.50/3.71      inference('sup-', [status(thm)], ['189', '190'])).
% 3.50/3.71  thf('192', plain, ((v1_funct_1 @ sk_C_2)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('193', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.50/3.71      inference('demod', [status(thm)], ['178', '185'])).
% 3.50/3.71  thf('194', plain,
% 3.50/3.71      (![X0 : $i]:
% 3.50/3.71         (((sk_A) != (k1_relat_1 @ X0))
% 3.50/3.71          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A)
% 3.50/3.71          | ((sk_C_2) = (X0))
% 3.50/3.71          | ~ (v1_funct_1 @ X0)
% 3.50/3.71          | ~ (v1_relat_1 @ X0))),
% 3.50/3.71      inference('demod', [status(thm)], ['188', '191', '192', '193'])).
% 3.50/3.71  thf('195', plain,
% 3.50/3.71      ((((sk_A) != (sk_A))
% 3.50/3.71        | ~ (v1_relat_1 @ sk_D)
% 3.50/3.71        | ~ (v1_funct_1 @ sk_D)
% 3.50/3.71        | ((sk_C_2) = (sk_D))
% 3.50/3.71        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.50/3.71      inference('sup-', [status(thm)], ['171', '194'])).
% 3.50/3.71  thf('196', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('197', plain,
% 3.50/3.71      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.50/3.71         ((v1_relat_1 @ X19)
% 3.50/3.71          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.50/3.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.50/3.71  thf('198', plain, ((v1_relat_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['196', '197'])).
% 3.50/3.71  thf('199', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('200', plain,
% 3.50/3.71      ((((sk_A) != (sk_A))
% 3.50/3.71        | ((sk_C_2) = (sk_D))
% 3.50/3.71        | (r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.50/3.71      inference('demod', [status(thm)], ['195', '198', '199'])).
% 3.50/3.71  thf('201', plain,
% 3.50/3.71      (((r2_hidden @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A) | ((sk_C_2) = (sk_D)))),
% 3.50/3.71      inference('simplify', [status(thm)], ['200'])).
% 3.50/3.71  thf(t1_subset, axiom,
% 3.50/3.71    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 3.50/3.71  thf('202', plain,
% 3.50/3.71      (![X10 : $i, X11 : $i]:
% 3.50/3.71         ((m1_subset_1 @ X10 @ X11) | ~ (r2_hidden @ X10 @ X11))),
% 3.50/3.71      inference('cnf', [status(esa)], [t1_subset])).
% 3.50/3.71  thf('203', plain,
% 3.50/3.71      ((((sk_C_2) = (sk_D)) | (m1_subset_1 @ (sk_C_1 @ sk_D @ sk_C_2) @ sk_A))),
% 3.50/3.71      inference('sup-', [status(thm)], ['201', '202'])).
% 3.50/3.71  thf('204', plain,
% 3.50/3.71      (![X44 : $i]:
% 3.50/3.71         (((k1_funct_1 @ sk_C_2 @ X44) = (k1_funct_1 @ sk_D @ X44))
% 3.50/3.71          | ~ (m1_subset_1 @ X44 @ sk_A))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('205', plain,
% 3.50/3.71      ((((sk_C_2) = (sk_D))
% 3.50/3.71        | ((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.50/3.71            = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2))))),
% 3.50/3.71      inference('sup-', [status(thm)], ['203', '204'])).
% 3.50/3.71  thf('206', plain,
% 3.50/3.71      (((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.50/3.71         = (k1_funct_1 @ sk_D @ (sk_C_1 @ sk_D @ sk_C_2)))),
% 3.50/3.71      inference('condensation', [status(thm)], ['205'])).
% 3.50/3.71  thf('207', plain,
% 3.50/3.71      (![X17 : $i, X18 : $i]:
% 3.50/3.71         (~ (v1_relat_1 @ X17)
% 3.50/3.71          | ~ (v1_funct_1 @ X17)
% 3.50/3.71          | ((X18) = (X17))
% 3.50/3.71          | ((k1_funct_1 @ X18 @ (sk_C_1 @ X17 @ X18))
% 3.50/3.71              != (k1_funct_1 @ X17 @ (sk_C_1 @ X17 @ X18)))
% 3.50/3.71          | ((k1_relat_1 @ X18) != (k1_relat_1 @ X17))
% 3.50/3.71          | ~ (v1_funct_1 @ X18)
% 3.50/3.71          | ~ (v1_relat_1 @ X18))),
% 3.50/3.71      inference('cnf', [status(esa)], [t9_funct_1])).
% 3.50/3.71  thf('208', plain,
% 3.50/3.71      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.50/3.71          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.50/3.71        | ~ (v1_relat_1 @ sk_C_2)
% 3.50/3.71        | ~ (v1_funct_1 @ sk_C_2)
% 3.50/3.71        | ((k1_relat_1 @ sk_C_2) != (k1_relat_1 @ sk_D))
% 3.50/3.71        | ((sk_C_2) = (sk_D))
% 3.50/3.71        | ~ (v1_funct_1 @ sk_D)
% 3.50/3.71        | ~ (v1_relat_1 @ sk_D))),
% 3.50/3.71      inference('sup-', [status(thm)], ['206', '207'])).
% 3.50/3.71  thf('209', plain, ((v1_relat_1 @ sk_C_2)),
% 3.50/3.71      inference('sup-', [status(thm)], ['189', '190'])).
% 3.50/3.71  thf('210', plain, ((v1_funct_1 @ sk_C_2)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('211', plain, (((sk_A) = (k1_relat_1 @ sk_C_2))),
% 3.50/3.71      inference('demod', [status(thm)], ['178', '185'])).
% 3.50/3.71  thf('212', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 3.50/3.71      inference('demod', [status(thm)], ['7', '170'])).
% 3.50/3.71  thf('213', plain, ((v1_funct_1 @ sk_D)),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('214', plain, ((v1_relat_1 @ sk_D)),
% 3.50/3.71      inference('sup-', [status(thm)], ['196', '197'])).
% 3.50/3.71  thf('215', plain,
% 3.50/3.71      ((((k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2))
% 3.50/3.71          != (k1_funct_1 @ sk_C_2 @ (sk_C_1 @ sk_D @ sk_C_2)))
% 3.50/3.71        | ((sk_A) != (sk_A))
% 3.50/3.71        | ((sk_C_2) = (sk_D)))),
% 3.50/3.71      inference('demod', [status(thm)],
% 3.50/3.71                ['208', '209', '210', '211', '212', '213', '214'])).
% 3.50/3.71  thf('216', plain, (((sk_C_2) = (sk_D))),
% 3.50/3.71      inference('simplify', [status(thm)], ['215'])).
% 3.50/3.71  thf('217', plain,
% 3.50/3.71      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.50/3.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.50/3.71  thf('218', plain,
% 3.50/3.71      (![X29 : $i, X30 : $i, X31 : $i]:
% 3.50/3.71         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 3.50/3.71          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 3.50/3.71      inference('simplify', [status(thm)], ['161'])).
% 3.50/3.71  thf('219', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_C_2)),
% 3.50/3.71      inference('sup-', [status(thm)], ['217', '218'])).
% 3.50/3.71  thf('220', plain, ($false),
% 3.50/3.71      inference('demod', [status(thm)], ['0', '216', '219'])).
% 3.50/3.71  
% 3.50/3.71  % SZS output end Refutation
% 3.50/3.71  
% 3.50/3.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
