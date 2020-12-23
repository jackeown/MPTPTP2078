%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5HwJ5XCWVW

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:17 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  147 (2179 expanded)
%              Number of leaves         :   39 ( 647 expanded)
%              Depth                    :   25
%              Number of atoms          : 1030 (29212 expanded)
%              Number of equality atoms :   71 (1309 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
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
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
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

thf('31',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( ( k9_relat_1 @ X12 @ ( k1_relat_1 @ X12 ) )
        = ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('33',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X11 @ X9 @ X10 ) @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ ( k1_relat_1 @ X0 ) @ X1 ) @ X1 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('38',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X11 )
      | ~ ( r2_hidden @ X8 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('42',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_A @ ( k9_relat_1 @ sk_D_1 @ sk_B_1 ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['29','44'])).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k9_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('49',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ X7 )
      | ~ ( r2_hidden @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('51',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X41: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_A
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('56',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X14 )
      | ( X15
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('57',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('59',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_B_1 @ sk_A ) ) )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','60'])).

thf('62',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['53','61'])).

thf('63',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['22','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['53','61'])).

thf('66',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X38 != k1_xboole_0 )
      | ( X39 = k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('68',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ k1_xboole_0 )
      | ( X40 = k1_xboole_0 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','68'])).

thf('70',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_C = k1_xboole_0 ),
    inference(clc,[status(thm)],['53','61'])).

thf('72',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) @ sk_A ) @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['73','76'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('81',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['63','79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('83',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('84',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('86',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('89',plain,(
    ! [X33: $i] :
      ( zip_tseitin_0 @ X33 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['87','89'])).

thf('91',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['18','21'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( sk_B_1
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ( zip_tseitin_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['96','99'])).

thf('101',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('102',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['86','102'])).

thf('104',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['81','103'])).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['15','104','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5HwJ5XCWVW
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:43:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.69  % Solved by: fo/fo7.sh
% 0.45/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.69  % done 253 iterations in 0.252s
% 0.45/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.69  % SZS output start Refutation
% 0.45/0.69  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.69  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.45/0.69  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.69  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.69  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.69  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.69  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.69  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.69  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.69  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.69  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.69  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.69  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.69  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.45/0.69  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.69  thf(t190_funct_2, conjecture,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.45/0.69         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.69       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.45/0.69            ( ![E:$i]:
% 0.45/0.69              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.45/0.69            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.45/0.69          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.45/0.69               ( ![E:$i]:
% 0.45/0.69                 ( ( m1_subset_1 @ E @ B ) =>
% 0.45/0.69                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.45/0.69  thf('0', plain,
% 0.45/0.69      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('1', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.69       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.69  thf('2', plain,
% 0.45/0.69      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.45/0.69         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.45/0.69          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.45/0.69      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.69  thf('3', plain,
% 0.45/0.69      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.69  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.45/0.69      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.69  thf(t146_relat_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ A ) =>
% 0.45/0.69       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.45/0.69  thf('5', plain,
% 0.45/0.69      (![X12 : $i]:
% 0.45/0.69         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 0.45/0.69          | ~ (v1_relat_1 @ X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.45/0.69  thf(t143_relat_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( v1_relat_1 @ C ) =>
% 0.45/0.69       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.45/0.69         ( ?[D:$i]:
% 0.45/0.69           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.69             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.45/0.69             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.69  thf('6', plain,
% 0.45/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.45/0.69          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ (k1_relat_1 @ X11))
% 0.45/0.69          | ~ (v1_relat_1 @ X11))),
% 0.45/0.69      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.69  thf('7', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | (r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ 
% 0.45/0.69             (k1_relat_1 @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.69  thf('8', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r2_hidden @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ (k1_relat_1 @ X0))
% 0.45/0.69          | ~ (v1_relat_1 @ X0)
% 0.45/0.69          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['7'])).
% 0.45/0.69  thf('9', plain,
% 0.45/0.69      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.69        | (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.45/0.69           (k1_relat_1 @ sk_D_1)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['4', '8'])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(cc1_relset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( v1_relat_1 @ C ) ))).
% 0.45/0.70  thf('11', plain,
% 0.45/0.70      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.70         ((v1_relat_1 @ X16)
% 0.45/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.45/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.70  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.45/0.70        (k1_relat_1 @ sk_D_1))),
% 0.45/0.70      inference('demod', [status(thm)], ['9', '12'])).
% 0.45/0.70  thf(d1_xboole_0, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.70  thf('14', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.70  thf('15', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.70  thf('16', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(d1_funct_2, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.70  thf(zf_stmt_1, axiom,
% 0.45/0.70    (![C:$i,B:$i,A:$i]:
% 0.45/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.45/0.70         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 0.45/0.70          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 0.45/0.70          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.70        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.70         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.45/0.70          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.45/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.45/0.70  thf('22', plain,
% 0.45/0.70      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.70        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['18', '21'])).
% 0.45/0.70  thf(zf_stmt_2, axiom,
% 0.45/0.70    (![B:$i,A:$i]:
% 0.45/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.70  thf('23', plain,
% 0.45/0.70      (![X33 : $i, X34 : $i]:
% 0.45/0.70         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.70  thf('24', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.70  thf(zf_stmt_5, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.70  thf('25', plain,
% 0.45/0.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.70         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.45/0.70          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.45/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.70  thf('26', plain,
% 0.45/0.70      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.70        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.70  thf('27', plain,
% 0.45/0.70      ((((sk_C) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['23', '26'])).
% 0.45/0.70  thf('28', plain,
% 0.45/0.70      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.70        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['18', '21'])).
% 0.45/0.70  thf('29', plain,
% 0.45/0.70      ((((sk_C) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.70  thf('30', plain,
% 0.45/0.70      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.45/0.70        (k1_relat_1 @ sk_D_1))),
% 0.45/0.70      inference('demod', [status(thm)], ['9', '12'])).
% 0.45/0.70  thf('31', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_1))),
% 0.45/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      (![X12 : $i]:
% 0.45/0.70         (((k9_relat_1 @ X12 @ (k1_relat_1 @ X12)) = (k2_relat_1 @ X12))
% 0.45/0.70          | ~ (v1_relat_1 @ X12))),
% 0.45/0.70      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.45/0.70  thf('33', plain,
% 0.45/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.45/0.70          | (r2_hidden @ (k4_tarski @ (sk_D @ X11 @ X9 @ X10) @ X10) @ X11)
% 0.45/0.70          | ~ (v1_relat_1 @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.70  thf('34', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.45/0.70          | ~ (v1_relat_1 @ X0)
% 0.45/0.70          | ~ (v1_relat_1 @ X0)
% 0.45/0.70          | (r2_hidden @ 
% 0.45/0.70             (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.70  thf('35', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((r2_hidden @ 
% 0.45/0.70           (k4_tarski @ (sk_D @ X0 @ (k1_relat_1 @ X0) @ X1) @ X1) @ X0)
% 0.45/0.70          | ~ (v1_relat_1 @ X0)
% 0.45/0.70          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.45/0.70  thf('36', plain,
% 0.45/0.70      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.70        | (r2_hidden @ 
% 0.45/0.70           (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.45/0.70           sk_D_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['31', '35'])).
% 0.45/0.70  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.70  thf('38', plain,
% 0.45/0.70      ((r2_hidden @ 
% 0.45/0.70        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.45/0.70        sk_D_1)),
% 0.45/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.70  thf('39', plain,
% 0.45/0.70      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X8 @ X9)
% 0.45/0.70          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X11)
% 0.45/0.70          | ~ (r2_hidden @ X8 @ (k1_relat_1 @ X11))
% 0.45/0.70          | (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.45/0.70          | ~ (v1_relat_1 @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.70  thf('40', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v1_relat_1 @ sk_D_1)
% 0.45/0.70          | (r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.45/0.70          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.45/0.70               (k1_relat_1 @ sk_D_1))
% 0.45/0.70          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.70  thf('41', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.70  thf('42', plain,
% 0.45/0.70      ((r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ 
% 0.45/0.70        (k1_relat_1 @ sk_D_1))),
% 0.45/0.70      inference('demod', [status(thm)], ['9', '12'])).
% 0.45/0.70  thf('43', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ X0))
% 0.45/0.70          | ~ (r2_hidden @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ X0))),
% 0.45/0.70      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.45/0.70  thf('44', plain,
% 0.45/0.70      ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['30', '43'])).
% 0.45/0.70  thf('45', plain,
% 0.45/0.70      (((r2_hidden @ sk_A @ (k9_relat_1 @ sk_D_1 @ sk_B_1))
% 0.45/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['29', '44'])).
% 0.45/0.70  thf('46', plain,
% 0.45/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X10 @ (k9_relat_1 @ X11 @ X9))
% 0.45/0.70          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 0.45/0.70          | ~ (v1_relat_1 @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.70  thf('47', plain,
% 0.45/0.70      ((((sk_C) = (k1_xboole_0))
% 0.45/0.70        | ~ (v1_relat_1 @ sk_D_1)
% 0.45/0.70        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.70  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.70  thf('49', plain,
% 0.45/0.70      ((((sk_C) = (k1_xboole_0))
% 0.45/0.70        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.45/0.70      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.70  thf(t1_subset, axiom,
% 0.45/0.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.45/0.70  thf('50', plain,
% 0.45/0.70      (![X6 : $i, X7 : $i]: ((m1_subset_1 @ X6 @ X7) | ~ (r2_hidden @ X6 @ X7))),
% 0.45/0.70      inference('cnf', [status(esa)], [t1_subset])).
% 0.45/0.70  thf('51', plain,
% 0.45/0.70      ((((sk_C) = (k1_xboole_0))
% 0.45/0.70        | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.70  thf('52', plain,
% 0.45/0.70      (![X41 : $i]:
% 0.45/0.70         (((sk_A) != (k1_funct_1 @ sk_D_1 @ X41))
% 0.45/0.70          | ~ (m1_subset_1 @ X41 @ sk_B_1))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('53', plain,
% 0.45/0.70      ((((sk_C) = (k1_xboole_0))
% 0.45/0.70        | ((sk_A) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.70  thf('54', plain,
% 0.45/0.70      ((((sk_C) = (k1_xboole_0)) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.45/0.70  thf('55', plain,
% 0.45/0.70      ((r2_hidden @ 
% 0.45/0.70        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.45/0.70        sk_D_1)),
% 0.45/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.70  thf(t8_funct_1, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.70       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.45/0.70         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.70           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.70  thf('56', plain,
% 0.45/0.70      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.70         (~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X14)
% 0.45/0.70          | ((X15) = (k1_funct_1 @ X14 @ X13))
% 0.45/0.70          | ~ (v1_funct_1 @ X14)
% 0.45/0.70          | ~ (v1_relat_1 @ X14))),
% 0.45/0.70      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.45/0.70  thf('57', plain,
% 0.45/0.70      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.70        | ((sk_A)
% 0.45/0.70            = (k1_funct_1 @ sk_D_1 @ 
% 0.45/0.70               (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.70  thf('58', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.70  thf('59', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('60', plain,
% 0.45/0.70      (((sk_A)
% 0.45/0.70         = (k1_funct_1 @ sk_D_1 @ 
% 0.45/0.70            (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A)))),
% 0.45/0.70      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.45/0.70  thf('61', plain,
% 0.45/0.70      ((((sk_A) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_B_1 @ sk_A)))
% 0.45/0.70        | ((sk_C) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['54', '60'])).
% 0.45/0.70  thf('62', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.70      inference('clc', [status(thm)], ['53', '61'])).
% 0.45/0.70  thf('63', plain,
% 0.45/0.70      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_B_1)
% 0.45/0.70        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['22', '62'])).
% 0.45/0.70  thf('64', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('65', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.70      inference('clc', [status(thm)], ['53', '61'])).
% 0.45/0.70  thf('66', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 0.45/0.70      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.70  thf('67', plain,
% 0.45/0.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.70         (((X38) != (k1_xboole_0))
% 0.45/0.70          | ((X39) = (k1_xboole_0))
% 0.45/0.70          | ((X40) = (k1_xboole_0))
% 0.45/0.70          | ~ (v1_funct_2 @ X40 @ X39 @ X38)
% 0.45/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.70  thf('68', plain,
% 0.45/0.70      (![X39 : $i, X40 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X40 @ 
% 0.45/0.70             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ k1_xboole_0)))
% 0.45/0.70          | ~ (v1_funct_2 @ X40 @ X39 @ k1_xboole_0)
% 0.45/0.70          | ((X40) = (k1_xboole_0))
% 0.45/0.70          | ((X39) = (k1_xboole_0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['67'])).
% 0.45/0.70  thf('69', plain,
% 0.45/0.70      ((((sk_B_1) = (k1_xboole_0))
% 0.45/0.70        | ((sk_D_1) = (k1_xboole_0))
% 0.45/0.70        | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['66', '68'])).
% 0.45/0.70  thf('70', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('71', plain, (((sk_C) = (k1_xboole_0))),
% 0.45/0.70      inference('clc', [status(thm)], ['53', '61'])).
% 0.45/0.70  thf('72', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ k1_xboole_0)),
% 0.45/0.70      inference('demod', [status(thm)], ['70', '71'])).
% 0.45/0.70  thf('73', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.45/0.70      inference('demod', [status(thm)], ['69', '72'])).
% 0.45/0.70  thf('74', plain,
% 0.45/0.70      ((r2_hidden @ 
% 0.45/0.70        (k4_tarski @ (sk_D @ sk_D_1 @ (k1_relat_1 @ sk_D_1) @ sk_A) @ sk_A) @ 
% 0.45/0.70        sk_D_1)),
% 0.45/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.45/0.70  thf('75', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.70      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.70  thf('76', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.45/0.70      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.70  thf('77', plain,
% 0.45/0.70      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_B_1) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['73', '76'])).
% 0.45/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.70  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.70  thf('79', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.70  thf('80', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.70  thf('81', plain,
% 0.45/0.70      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.70        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['63', '79', '80'])).
% 0.45/0.70  thf('82', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ k1_xboole_0)))),
% 0.45/0.70      inference('demod', [status(thm)], ['64', '65'])).
% 0.45/0.70  thf('83', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.70  thf('84', plain,
% 0.45/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.45/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.45/0.70      inference('demod', [status(thm)], ['82', '83'])).
% 0.45/0.70  thf('85', plain,
% 0.45/0.70      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.45/0.70         (~ (zip_tseitin_0 @ X38 @ X39)
% 0.45/0.70          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 0.45/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.70  thf('86', plain,
% 0.45/0.70      (((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.45/0.70        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['84', '85'])).
% 0.45/0.70  thf('87', plain,
% 0.45/0.70      (![X33 : $i, X34 : $i]:
% 0.45/0.70         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.70  thf('88', plain,
% 0.45/0.70      (![X33 : $i, X34 : $i]:
% 0.45/0.70         ((zip_tseitin_0 @ X33 @ X34) | ((X34) != (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.70  thf('89', plain, (![X33 : $i]: (zip_tseitin_0 @ X33 @ k1_xboole_0)),
% 0.45/0.70      inference('simplify', [status(thm)], ['88'])).
% 0.45/0.70  thf('90', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.45/0.70      inference('sup+', [status(thm)], ['87', '89'])).
% 0.45/0.70  thf('91', plain,
% 0.45/0.70      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.70        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.70  thf('92', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 0.45/0.70          | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['90', '91'])).
% 0.45/0.70  thf('93', plain,
% 0.45/0.70      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 0.45/0.70        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('demod', [status(thm)], ['18', '21'])).
% 0.45/0.70  thf('94', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((zip_tseitin_0 @ sk_B_1 @ X0) | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['92', '93'])).
% 0.45/0.70  thf('95', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.45/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.45/0.70  thf('96', plain,
% 0.45/0.70      (![X0 : $i]: (~ (v1_xboole_0 @ sk_B_1) | (zip_tseitin_0 @ sk_B_1 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['94', '95'])).
% 0.45/0.70  thf('97', plain,
% 0.45/0.70      (![X33 : $i, X34 : $i]:
% 0.45/0.70         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.70  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.70  thf('99', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.45/0.70      inference('sup+', [status(thm)], ['97', '98'])).
% 0.45/0.70  thf('100', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.45/0.70      inference('clc', [status(thm)], ['96', '99'])).
% 0.45/0.70  thf('101', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.45/0.70      inference('demod', [status(thm)], ['77', '78'])).
% 0.45/0.70  thf('102', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 0.45/0.70      inference('demod', [status(thm)], ['100', '101'])).
% 0.45/0.70  thf('103', plain, ((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.70      inference('demod', [status(thm)], ['86', '102'])).
% 0.45/0.70  thf('104', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.45/0.70      inference('demod', [status(thm)], ['81', '103'])).
% 0.45/0.70  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.70  thf('106', plain, ($false),
% 0.45/0.70      inference('demod', [status(thm)], ['15', '104', '105'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.45/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
