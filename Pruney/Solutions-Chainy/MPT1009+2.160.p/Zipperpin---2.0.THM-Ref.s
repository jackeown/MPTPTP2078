%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.exG08XdrJR

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:12 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 248 expanded)
%              Number of leaves         :   38 (  92 expanded)
%              Depth                    :   12
%              Number of atoms          :  647 (3347 expanded)
%              Number of equality atoms :   47 ( 183 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('6',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != ( k1_tarski @ X12 ) )
      | ( ( k2_relat_1 @ X13 )
        = ( k1_tarski @ ( k1_funct_1 @ X13 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['21','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k7_relset_1 @ X24 @ X25 @ X26 @ X24 )
        = ( k2_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('36',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('39',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('40',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('42',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['36','37','42'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('44',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X10 @ X11 ) @ ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['29','30'])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['33','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.exG08XdrJR
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:58:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.37/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.59  % Solved by: fo/fo7.sh
% 0.37/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.59  % done 77 iterations in 0.145s
% 0.37/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.59  % SZS output start Refutation
% 0.37/0.59  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.59  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.59  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.37/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.59  thf(t64_funct_2, conjecture,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.59         ( m1_subset_1 @
% 0.37/0.59           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.59         ( r1_tarski @
% 0.37/0.59           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.37/0.59           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.37/0.59            ( m1_subset_1 @
% 0.37/0.59              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.37/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.37/0.59            ( r1_tarski @
% 0.37/0.59              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.37/0.59              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.37/0.59    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.37/0.59  thf('0', plain,
% 0.37/0.59      (~ (r1_tarski @ 
% 0.37/0.59          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.37/0.59          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('1', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(d1_funct_2, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.59  thf(zf_stmt_1, axiom,
% 0.37/0.59    (![C:$i,B:$i,A:$i]:
% 0.37/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.59  thf('2', plain,
% 0.37/0.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.37/0.59         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.37/0.59          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 0.37/0.59          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.59  thf('3', plain,
% 0.37/0.59      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.37/0.59        | ((k1_tarski @ sk_A)
% 0.37/0.59            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.59  thf(zf_stmt_2, axiom,
% 0.37/0.59    (![B:$i,A:$i]:
% 0.37/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.59  thf('4', plain,
% 0.37/0.59      (![X27 : $i, X28 : $i]:
% 0.37/0.59         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.59  thf('5', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.59  thf(zf_stmt_5, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.59  thf('6', plain,
% 0.37/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.37/0.59         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.37/0.59          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.37/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.59  thf('7', plain,
% 0.37/0.59      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.37/0.59        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.37/0.59  thf('8', plain,
% 0.37/0.59      ((((sk_B) = (k1_xboole_0))
% 0.37/0.59        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.37/0.59      inference('sup-', [status(thm)], ['4', '7'])).
% 0.37/0.59  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('10', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.37/0.59      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.37/0.59  thf('11', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.59  thf('12', plain,
% 0.37/0.59      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.37/0.59         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.37/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.59  thf('13', plain,
% 0.37/0.59      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.59  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.37/0.59  thf('15', plain,
% 0.37/0.59      (~ (r1_tarski @ 
% 0.37/0.59          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C) @ 
% 0.37/0.59          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['0', '14'])).
% 0.37/0.59  thf('16', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.37/0.59  thf('18', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf(redefinition_k7_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.37/0.59  thf('19', plain,
% 0.37/0.59      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.37/0.59          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.37/0.59  thf('20', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.37/0.59           = (k9_relat_1 @ sk_D @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.59  thf('21', plain,
% 0.37/0.59      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.37/0.59          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['15', '20'])).
% 0.37/0.59  thf('22', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.37/0.59  thf(t14_funct_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]:
% 0.37/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.59       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.37/0.59         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.37/0.59  thf('23', plain,
% 0.37/0.59      (![X12 : $i, X13 : $i]:
% 0.37/0.59         (((k1_relat_1 @ X13) != (k1_tarski @ X12))
% 0.37/0.59          | ((k2_relat_1 @ X13) = (k1_tarski @ (k1_funct_1 @ X13 @ X12)))
% 0.37/0.59          | ~ (v1_funct_1 @ X13)
% 0.37/0.59          | ~ (v1_relat_1 @ X13))),
% 0.37/0.59      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.37/0.59  thf('24', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.37/0.59          | ~ (v1_relat_1 @ X0)
% 0.37/0.59          | ~ (v1_funct_1 @ X0)
% 0.37/0.59          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.37/0.59      inference('sup-', [status(thm)], ['22', '23'])).
% 0.37/0.59  thf('25', plain,
% 0.37/0.59      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.37/0.59        | ~ (v1_funct_1 @ sk_D)
% 0.37/0.59        | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.59      inference('eq_res', [status(thm)], ['24'])).
% 0.37/0.59  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf('27', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(cc2_relat_1, axiom,
% 0.37/0.59    (![A:$i]:
% 0.37/0.59     ( ( v1_relat_1 @ A ) =>
% 0.37/0.59       ( ![B:$i]:
% 0.37/0.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.37/0.59  thf('28', plain,
% 0.37/0.59      (![X6 : $i, X7 : $i]:
% 0.37/0.59         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.37/0.59          | (v1_relat_1 @ X6)
% 0.37/0.59          | ~ (v1_relat_1 @ X7))),
% 0.37/0.59      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.37/0.59  thf('29', plain,
% 0.37/0.59      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.37/0.59        | (v1_relat_1 @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.59  thf(fc6_relat_1, axiom,
% 0.37/0.59    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.37/0.59  thf('30', plain,
% 0.37/0.59      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.37/0.59      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.37/0.59  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.59      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.59  thf('32', plain,
% 0.37/0.59      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.37/0.59      inference('demod', [status(thm)], ['25', '26', '31'])).
% 0.37/0.59  thf('33', plain,
% 0.37/0.59      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))),
% 0.37/0.59      inference('demod', [status(thm)], ['21', '32'])).
% 0.37/0.59  thf('34', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.37/0.59      inference('demod', [status(thm)], ['16', '17'])).
% 0.37/0.59  thf(t38_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.37/0.59         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.59  thf('35', plain,
% 0.37/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.37/0.59         (((k7_relset_1 @ X24 @ X25 @ X26 @ X24)
% 0.37/0.59            = (k2_relset_1 @ X24 @ X25 @ X26))
% 0.37/0.59          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.37/0.59      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.37/0.59  thf('36', plain,
% 0.37/0.59      (((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ (k1_relat_1 @ sk_D))
% 0.37/0.59         = (k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D))),
% 0.37/0.59      inference('sup-', [status(thm)], ['34', '35'])).
% 0.37/0.59  thf('37', plain,
% 0.37/0.59      (![X0 : $i]:
% 0.37/0.59         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.37/0.59           = (k9_relat_1 @ sk_D @ X0))),
% 0.37/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.59  thf('38', plain,
% 0.37/0.59      ((m1_subset_1 @ sk_D @ 
% 0.37/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.37/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.37/0.59    (![A:$i,B:$i,C:$i]:
% 0.37/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.37/0.59  thf('39', plain,
% 0.37/0.59      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.59         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.37/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.37/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.37/0.59  thf('40', plain,
% 0.37/0.59      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.37/0.60      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.60  thf('41', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.60      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.37/0.60  thf('42', plain,
% 0.37/0.60      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.37/0.60      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.60  thf('43', plain,
% 0.37/0.60      (((k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)) = (k2_relat_1 @ sk_D))),
% 0.37/0.60      inference('demod', [status(thm)], ['36', '37', '42'])).
% 0.37/0.60  thf(t147_relat_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( v1_relat_1 @ B ) =>
% 0.37/0.60       ( r1_tarski @
% 0.37/0.60         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.37/0.60  thf('44', plain,
% 0.37/0.60      (![X10 : $i, X11 : $i]:
% 0.37/0.60         ((r1_tarski @ (k9_relat_1 @ X10 @ X11) @ 
% 0.37/0.60           (k9_relat_1 @ X10 @ (k1_relat_1 @ X10)))
% 0.37/0.60          | ~ (v1_relat_1 @ X10))),
% 0.37/0.60      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.37/0.60  thf('45', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         ((r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))
% 0.37/0.60          | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.60      inference('sup+', [status(thm)], ['43', '44'])).
% 0.37/0.60  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.37/0.60  thf('47', plain,
% 0.37/0.60      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 0.37/0.60      inference('demod', [status(thm)], ['45', '46'])).
% 0.37/0.60  thf('48', plain, ($false), inference('demod', [status(thm)], ['33', '47'])).
% 0.37/0.60  
% 0.37/0.60  % SZS output end Refutation
% 0.37/0.60  
% 0.37/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
