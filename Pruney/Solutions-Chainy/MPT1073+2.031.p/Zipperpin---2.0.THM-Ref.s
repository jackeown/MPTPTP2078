%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.awxEttpksh

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:18 EST 2020

% Result     : Theorem 0.78s
% Output     : Refutation 0.78s
% Verified   : 
% Statistics : Number of formulae       :  139 (1211 expanded)
%              Number of leaves         :   40 ( 365 expanded)
%              Depth                    :   21
%              Number of atoms          :  930 (15832 expanded)
%              Number of equality atoms :   70 ( 795 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X6 @ X7 ) @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
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

thf('17',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('21',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('29',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('32',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X30: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ ( k1_relat_1 @ X9 ) )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('38',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k9_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X8 @ X6 @ X7 ) @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('43',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['41','42'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('47',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['35','48'])).

thf('50',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['22','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 != k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('56',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('60',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','66'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('68',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('69',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('70',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('72',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['51','70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('74',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('75',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('77',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('79',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('80',plain,(
    ! [X22: $i] :
      ( zip_tseitin_0 @ X22 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['78','80'])).

thf('82',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( sk_B_1
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['87','90'])).

thf('92',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('93',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['77','93'])).

thf('95',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['72','94'])).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,(
    $false ),
    inference(demod,[status(thm)],['15','95','96'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.awxEttpksh
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:34:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.78/0.98  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.78/0.98  % Solved by: fo/fo7.sh
% 0.78/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.78/0.98  % done 611 iterations in 0.536s
% 0.78/0.98  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.78/0.98  % SZS output start Refutation
% 0.78/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.78/0.98  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.78/0.98  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.78/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.78/0.98  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.78/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.78/0.98  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.78/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.78/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.78/0.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.78/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.78/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.78/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.78/0.98  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.78/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.78/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.78/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.78/0.98  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.78/0.98  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.78/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.78/0.98  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.78/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.78/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.78/0.98  thf(t190_funct_2, conjecture,
% 0.78/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.98     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.78/0.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.78/0.98       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.78/0.98            ( ![E:$i]:
% 0.78/0.98              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.78/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.78/0.98    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.78/0.98        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.78/0.98            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.78/0.98          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.78/0.98               ( ![E:$i]:
% 0.78/0.98                 ( ( m1_subset_1 @ E @ B ) =>
% 0.78/0.98                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.78/0.98    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.78/0.98  thf('0', plain,
% 0.78/0.98      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('1', plain,
% 0.78/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(redefinition_k2_relset_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.98       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.78/0.98  thf('2', plain,
% 0.78/0.98      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.78/0.98         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.78/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.78/0.98      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.78/0.98  thf('3', plain,
% 0.78/0.98      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.78/0.98  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['0', '3'])).
% 0.78/0.98  thf(t146_relat_1, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ( v1_relat_1 @ A ) =>
% 0.78/0.98       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.78/0.98  thf('5', plain,
% 0.78/0.98      (![X9 : $i]:
% 0.78/0.98         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 0.78/0.98          | ~ (v1_relat_1 @ X9))),
% 0.78/0.98      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.78/0.98  thf(t143_relat_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( v1_relat_1 @ C ) =>
% 0.78/0.98       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.78/0.98         ( ?[D:$i]:
% 0.78/0.98           ( ( r2_hidden @ D @ B ) & 
% 0.78/0.98             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.78/0.98             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.78/0.98  thf('6', plain,
% 0.78/0.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.78/0.98          | (r2_hidden @ (sk_D @ X8 @ X6 @ X7) @ (k1_relat_1 @ X8))
% 0.78/0.98          | ~ (v1_relat_1 @ X8))),
% 0.78/0.98      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.78/0.98  thf('7', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.78/0.98          | ~ (v1_relat_1 @ X0)
% 0.78/0.98          | ~ (v1_relat_1 @ X0)
% 0.78/0.98          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.78/0.98             (k1_relat_1 @ X0)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['5', '6'])).
% 0.78/0.98  thf('8', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.78/0.98          | ~ (v1_relat_1 @ X0)
% 0.78/0.98          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.78/0.98      inference('simplify', [status(thm)], ['7'])).
% 0.78/0.98  thf('9', plain,
% 0.78/0.98      ((~ (v1_relat_1 @ sk_D_1)
% 0.78/0.98        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.78/0.98           (k1_relat_1 @ sk_D_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['4', '8'])).
% 0.78/0.98  thf('10', plain,
% 0.78/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(cc1_relset_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.98       ( v1_relat_1 @ C ) ))).
% 0.78/0.98  thf('11', plain,
% 0.78/0.98      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.78/0.98         ((v1_relat_1 @ X13)
% 0.78/0.98          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.78/0.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.78/0.98  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.78/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.78/0.98  thf('13', plain,
% 0.78/0.98      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.78/0.98        (k1_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['9', '12'])).
% 0.78/0.98  thf(d1_xboole_0, axiom,
% 0.78/0.98    (![A:$i]:
% 0.78/0.98     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.78/0.98  thf('14', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.78/0.98  thf('15', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.78/0.98  thf('16', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(d1_funct_2, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.98       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.78/0.98           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.78/0.98             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.78/0.98         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.78/0.98           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.78/0.98             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.78/0.98  thf(zf_stmt_1, axiom,
% 0.78/0.98    (![C:$i,B:$i,A:$i]:
% 0.78/0.98     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.78/0.98       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.78/0.98  thf('17', plain,
% 0.78/0.98      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.78/0.98         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.78/0.98          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.78/0.98          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.78/0.98  thf('18', plain,
% 0.78/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.78/0.98        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['16', '17'])).
% 0.78/0.98  thf('19', plain,
% 0.78/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(redefinition_k1_relset_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.98       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.78/0.98  thf('20', plain,
% 0.78/0.98      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.78/0.98         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.78/0.98          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.78/0.98      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.78/0.98  thf('21', plain,
% 0.78/0.98      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['19', '20'])).
% 0.78/0.98  thf('22', plain,
% 0.78/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.78/0.98        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.78/0.98      inference('demod', [status(thm)], ['18', '21'])).
% 0.78/0.98  thf(zf_stmt_2, axiom,
% 0.78/0.98    (![B:$i,A:$i]:
% 0.78/0.98     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.78/0.98       ( zip_tseitin_0 @ B @ A ) ))).
% 0.78/0.98  thf('23', plain,
% 0.78/0.98      (![X22 : $i, X23 : $i]:
% 0.78/0.98         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.78/0.98  thf('24', plain,
% 0.78/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.78/0.98  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.78/0.98  thf(zf_stmt_5, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.78/0.98       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.78/0.98         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.78/0.98           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.78/0.98             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.78/0.98  thf('25', plain,
% 0.78/0.98      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.78/0.98         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.78/0.98          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.78/0.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.78/0.98  thf('26', plain,
% 0.78/0.98      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.78/0.98        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['24', '25'])).
% 0.78/0.98  thf('27', plain,
% 0.78/0.98      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['23', '26'])).
% 0.78/0.98  thf('28', plain,
% 0.78/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.78/0.98        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.78/0.98      inference('demod', [status(thm)], ['18', '21'])).
% 0.78/0.98  thf('29', plain,
% 0.78/0.98      ((((sk_C) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['27', '28'])).
% 0.78/0.98  thf('30', plain,
% 0.78/0.98      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.78/0.98        (k1_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['9', '12'])).
% 0.78/0.98  thf(t1_subset, axiom,
% 0.78/0.98    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.78/0.98  thf('31', plain,
% 0.78/0.98      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.78/0.98      inference('cnf', [status(esa)], [t1_subset])).
% 0.78/0.98  thf('32', plain,
% 0.78/0.98      ((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.78/0.98        (k1_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['30', '31'])).
% 0.78/0.98  thf('33', plain,
% 0.78/0.98      (((m1_subset_1 @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_B_1)
% 0.78/0.98        | ((sk_C) = (k1_xboole_0)))),
% 0.78/0.98      inference('sup+', [status(thm)], ['29', '32'])).
% 0.78/0.98  thf('34', plain,
% 0.78/0.98      (![X30 : $i]:
% 0.78/0.98         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X30))
% 0.78/0.98          | ~ (m1_subset_1 @ X30 @ sk_B_1))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('35', plain,
% 0.78/0.98      ((((sk_C) = (k1_xboole_0))
% 0.78/0.98        | ((sk_A)
% 0.78/0.98            != (k1_funct_1 @ sk_D_1 @ 
% 0.78/0.98                (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.78/0.98      inference('sup-', [status(thm)], ['33', '34'])).
% 0.78/0.98  thf('36', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['0', '3'])).
% 0.78/0.98  thf('37', plain,
% 0.78/0.98      (![X9 : $i]:
% 0.78/0.98         (((k9_relat_1 @ X9 @ (k1_relat_1 @ X9)) = (k2_relat_1 @ X9))
% 0.78/0.98          | ~ (v1_relat_1 @ X9))),
% 0.78/0.98      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.78/0.98  thf('38', plain,
% 0.78/0.98      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X7 @ (k9_relat_1 @ X8 @ X6))
% 0.78/0.98          | (r2_hidden @ (k4_tarski @ (sk_D @ X8 @ X6 @ X7) @ X7) @ X8)
% 0.78/0.98          | ~ (v1_relat_1 @ X8))),
% 0.78/0.98      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.78/0.98  thf('39', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.78/0.98          | ~ (v1_relat_1 @ X0)
% 0.78/0.98          | ~ (v1_relat_1 @ X0)
% 0.78/0.98          | (r2_hidden @ 
% 0.78/0.98             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.78/0.98      inference('sup-', [status(thm)], ['37', '38'])).
% 0.78/0.98  thf('40', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]:
% 0.78/0.98         ((r2_hidden @ 
% 0.78/0.98           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.78/0.98          | ~ (v1_relat_1 @ X0)
% 0.78/0.98          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.78/0.98      inference('simplify', [status(thm)], ['39'])).
% 0.78/0.98  thf('41', plain,
% 0.78/0.98      ((~ (v1_relat_1 @ sk_D_1)
% 0.78/0.98        | (r2_hidden @ 
% 0.78/0.98           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.78/0.98           sk_D_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['36', '40'])).
% 0.78/0.98  thf('42', plain, ((v1_relat_1 @ sk_D_1)),
% 0.78/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.78/0.98  thf('43', plain,
% 0.78/0.98      ((r2_hidden @ 
% 0.78/0.98        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.78/0.98        sk_D_1)),
% 0.78/0.98      inference('demod', [status(thm)], ['41', '42'])).
% 0.78/0.98  thf(t8_funct_1, axiom,
% 0.78/0.98    (![A:$i,B:$i,C:$i]:
% 0.78/0.98     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.78/0.98       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.78/0.98         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.78/0.98           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.78/0.98  thf('44', plain,
% 0.78/0.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.78/0.98         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.78/0.98          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.78/0.98          | ~ (v1_funct_1 @ X11)
% 0.78/0.98          | ~ (v1_relat_1 @ X11))),
% 0.78/0.98      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.78/0.98  thf('45', plain,
% 0.78/0.98      ((~ (v1_relat_1 @ sk_D_1)
% 0.78/0.98        | ~ (v1_funct_1 @ sk_D_1)
% 0.78/0.98        | ((sk_A)
% 0.78/0.98            = (k1_funct_1 @ sk_D_1 @ 
% 0.78/0.98               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.78/0.98      inference('sup-', [status(thm)], ['43', '44'])).
% 0.78/0.98  thf('46', plain, ((v1_relat_1 @ sk_D_1)),
% 0.78/0.98      inference('sup-', [status(thm)], ['10', '11'])).
% 0.78/0.98  thf('47', plain, ((v1_funct_1 @ sk_D_1)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('48', plain,
% 0.78/0.98      (((sk_A)
% 0.78/0.98         = (k1_funct_1 @ sk_D_1 @ 
% 0.78/0.98            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.78/0.98  thf('49', plain, ((((sk_C) = (k1_xboole_0)) | ((sk_A) != (sk_A)))),
% 0.78/0.98      inference('demod', [status(thm)], ['35', '48'])).
% 0.78/0.98  thf('50', plain, (((sk_C) = (k1_xboole_0))),
% 0.78/0.98      inference('simplify', [status(thm)], ['49'])).
% 0.78/0.98  thf('51', plain,
% 0.78/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_B_1)
% 0.78/0.98        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.78/0.98      inference('demod', [status(thm)], ['22', '50'])).
% 0.78/0.98  thf('52', plain,
% 0.78/0.98      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('53', plain, (((sk_C) = (k1_xboole_0))),
% 0.78/0.98      inference('simplify', [status(thm)], ['49'])).
% 0.78/0.98  thf('54', plain,
% 0.78/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.78/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['52', '53'])).
% 0.78/0.98  thf('55', plain,
% 0.78/0.98      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.78/0.98         (((X27) != (k1_xboole_0))
% 0.78/0.98          | ((X28) = (k1_xboole_0))
% 0.78/0.98          | ((X29) = (k1_xboole_0))
% 0.78/0.98          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.78/0.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.78/0.98  thf('56', plain,
% 0.78/0.98      (![X28 : $i, X29 : $i]:
% 0.78/0.98         (~ (m1_subset_1 @ X29 @ 
% 0.78/0.98             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ k1_xboole_0)))
% 0.78/0.98          | ~ (v1_funct_2 @ X29 @ X28 @ k1_xboole_0)
% 0.78/0.98          | ((X29) = (k1_xboole_0))
% 0.78/0.98          | ((X28) = (k1_xboole_0)))),
% 0.78/0.98      inference('simplify', [status(thm)], ['55'])).
% 0.78/0.98  thf('57', plain,
% 0.78/0.98      ((((sk_B_1) = (k1_xboole_0))
% 0.78/0.98        | ((sk_D_1) = (k1_xboole_0))
% 0.78/0.98        | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0))),
% 0.78/0.98      inference('sup-', [status(thm)], ['54', '56'])).
% 0.78/0.98  thf('58', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('59', plain, (((sk_C) = (k1_xboole_0))),
% 0.78/0.98      inference('simplify', [status(thm)], ['49'])).
% 0.78/0.98  thf('60', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0)),
% 0.78/0.98      inference('demod', [status(thm)], ['58', '59'])).
% 0.78/0.98  thf('61', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['57', '60'])).
% 0.78/0.98  thf('62', plain,
% 0.78/0.98      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.78/0.98  thf('63', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.78/0.98      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.78/0.98  thf('64', plain, (~ (v1_xboole_0 @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['62', '63'])).
% 0.78/0.98  thf('65', plain,
% 0.78/0.98      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['1', '2'])).
% 0.78/0.98  thf('66', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['64', '65'])).
% 0.78/0.98  thf('67', plain,
% 0.78/0.98      ((~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0))
% 0.78/0.98        | ((sk_B_1) = (k1_xboole_0)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['61', '66'])).
% 0.78/0.98  thf(t60_relat_1, axiom,
% 0.78/0.98    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.78/0.98     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.78/0.98  thf('68', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.78/0.98      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.78/0.98  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.78/0.98  thf('69', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.98  thf('70', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.78/0.98      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.78/0.98  thf('71', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.78/0.98      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.78/0.98  thf('72', plain,
% 0.78/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.78/0.98        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))),
% 0.78/0.98      inference('demod', [status(thm)], ['51', '70', '71'])).
% 0.78/0.98  thf('73', plain,
% 0.78/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.78/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['52', '53'])).
% 0.78/0.98  thf('74', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.78/0.98      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.78/0.98  thf('75', plain,
% 0.78/0.98      ((m1_subset_1 @ sk_D_1 @ 
% 0.78/0.98        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.78/0.98      inference('demod', [status(thm)], ['73', '74'])).
% 0.78/0.98  thf('76', plain,
% 0.78/0.98      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.78/0.98         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.78/0.98          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.78/0.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.78/0.98  thf('77', plain,
% 0.78/0.98      (((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.78/0.98        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.78/0.98      inference('sup-', [status(thm)], ['75', '76'])).
% 0.78/0.98  thf('78', plain,
% 0.78/0.98      (![X22 : $i, X23 : $i]:
% 0.78/0.98         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.78/0.98  thf('79', plain,
% 0.78/0.98      (![X22 : $i, X23 : $i]:
% 0.78/0.98         ((zip_tseitin_0 @ X22 @ X23) | ((X23) != (k1_xboole_0)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.78/0.98  thf('80', plain, (![X22 : $i]: (zip_tseitin_0 @ X22 @ k1_xboole_0)),
% 0.78/0.98      inference('simplify', [status(thm)], ['79'])).
% 0.78/0.98  thf('81', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.78/0.98         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.78/0.98      inference('sup+', [status(thm)], ['78', '80'])).
% 0.78/0.98  thf('82', plain,
% 0.78/0.98      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.78/0.98        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['24', '25'])).
% 0.78/0.98  thf('83', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 0.78/0.98          | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['81', '82'])).
% 0.78/0.98  thf('84', plain,
% 0.78/0.98      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.78/0.98        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.78/0.98      inference('demod', [status(thm)], ['18', '21'])).
% 0.78/0.98  thf('85', plain,
% 0.78/0.98      (![X0 : $i]:
% 0.78/0.98         ((zip_tseitin_0 @ sk_B_1 @ X0) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.78/0.98      inference('sup-', [status(thm)], ['83', '84'])).
% 0.78/0.98  thf('86', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('sup-', [status(thm)], ['13', '14'])).
% 0.78/0.98  thf('87', plain,
% 0.78/0.98      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 0.78/0.98      inference('sup-', [status(thm)], ['85', '86'])).
% 0.78/0.98  thf('88', plain,
% 0.78/0.98      (![X22 : $i, X23 : $i]:
% 0.78/0.98         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.78/0.98      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.78/0.98  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.98  thf('90', plain,
% 0.78/0.98      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.78/0.98      inference('sup+', [status(thm)], ['88', '89'])).
% 0.78/0.98  thf('91', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.78/0.98      inference('clc', [status(thm)], ['87', '90'])).
% 0.78/0.98  thf('92', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.78/0.98      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.78/0.98  thf('93', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 0.78/0.98      inference('demod', [status(thm)], ['91', '92'])).
% 0.78/0.98  thf('94', plain, ((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.78/0.98      inference('demod', [status(thm)], ['77', '93'])).
% 0.78/0.98  thf('95', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.78/0.98      inference('demod', [status(thm)], ['72', '94'])).
% 0.78/0.98  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.78/0.98      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.78/0.98  thf('97', plain, ($false),
% 0.78/0.98      inference('demod', [status(thm)], ['15', '95', '96'])).
% 0.78/0.98  
% 0.78/0.98  % SZS output end Refutation
% 0.78/0.98  
% 0.78/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
