%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FNZbDHFi15

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:45 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 408 expanded)
%              Number of leaves         :   42 ( 141 expanded)
%              Depth                    :   13
%              Number of atoms          :  849 (5293 expanded)
%              Number of equality atoms :   78 ( 413 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('7',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf(t39_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) )
          = ( k2_relset_1 @ B @ A @ C ) )
        & ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) )
          = ( k1_relset_1 @ B @ A @ C ) ) ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k7_relset_1 @ X27 @ X28 @ X29 @ ( k8_relset_1 @ X27 @ X28 @ X29 @ X28 ) )
        = ( k2_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[t39_relset_1])).

thf('17',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ ( k8_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ sk_B ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k9_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k8_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ sk_B ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','14'])).

thf(t48_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k8_relset_1 @ A @ B @ C @ B )
          = A ) ) ) )).

thf('23',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( X40 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X40 ) ) )
      | ( ( k8_relset_1 @ X38 @ X40 @ X39 @ X40 )
        = X38 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_2])).

thf('24',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ sk_B )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('27',plain,(
    v1_funct_2 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ sk_B )
      = ( k1_relat_1 @ sk_C_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','27','28'])).

thf('30',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k8_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ sk_B )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['21','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('34',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('41',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k11_relat_1 @ X13 @ X14 )
        = ( k9_relat_1 @ X13 @ ( k1_tarski @ X14 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['33','44'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X17: $i] :
      ( ( ( k9_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('47',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['33','44'])).

thf('48',plain,
    ( ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('50',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['45','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','51'])).

thf('53',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('55',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('58',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['56','58'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('60',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k11_relat_1 @ X19 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('63',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 )
 != ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['55','66'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['52','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FNZbDHFi15
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:12:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 145 iterations in 0.206s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.65  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.44/0.65  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.44/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.44/0.65  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.65  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.44/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.65  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.44/0.65  thf(t62_funct_2, conjecture,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.65         ( m1_subset_1 @
% 0.44/0.65           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.65       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.65         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.44/0.65           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.44/0.65            ( m1_subset_1 @
% 0.44/0.65              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.44/0.65          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.44/0.65            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.44/0.65              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.44/0.65  thf('0', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('1', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(d1_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_1, axiom,
% 0.44/0.65    (![C:$i,B:$i,A:$i]:
% 0.44/0.65     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.65       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.44/0.65         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.44/0.65          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.44/0.65          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.44/0.65        | ((k1_tarski @ sk_A)
% 0.44/0.65            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.65  thf(zf_stmt_2, axiom,
% 0.44/0.65    (![B:$i,A:$i]:
% 0.44/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (![X30 : $i, X31 : $i]:
% 0.44/0.65         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.65  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.65  thf(zf_stmt_5, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.65         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.65           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.65             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.65  thf('6', plain,
% 0.44/0.65      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.44/0.65         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.44/0.65          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.44/0.65          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.65  thf('7', plain,
% 0.44/0.65      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.44/0.65        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      ((((sk_B) = (k1_xboole_0))
% 0.44/0.65        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['4', '7'])).
% 0.44/0.65  thf('9', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('10', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.44/0.65      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.65         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.44/0.65          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.44/0.65         = (k1_relat_1 @ sk_C_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.65  thf('14', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.44/0.65      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '14'])).
% 0.44/0.65  thf(t39_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.44/0.65       ( ( ( k7_relset_1 @ B @ A @ C @ ( k8_relset_1 @ B @ A @ C @ A ) ) =
% 0.44/0.65           ( k2_relset_1 @ B @ A @ C ) ) & 
% 0.44/0.65         ( ( k8_relset_1 @ B @ A @ C @ ( k7_relset_1 @ B @ A @ C @ B ) ) =
% 0.44/0.65           ( k1_relset_1 @ B @ A @ C ) ) ) ))).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.44/0.65         (((k7_relset_1 @ X27 @ X28 @ X29 @ 
% 0.44/0.65            (k8_relset_1 @ X27 @ X28 @ X29 @ X28))
% 0.44/0.65            = (k2_relset_1 @ X27 @ X28 @ X29))
% 0.44/0.65          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.44/0.65      inference('cnf', [status(esa)], [t39_relset_1])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      (((k7_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ 
% 0.44/0.65         (k8_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ sk_B))
% 0.44/0.65         = (k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '14'])).
% 0.44/0.65  thf(redefinition_k7_relset_1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.65       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.65         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.44/0.65          | ((k7_relset_1 @ X24 @ X25 @ X23 @ X26) = (k9_relat_1 @ X23 @ X26)))),
% 0.44/0.65      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((k7_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ X0)
% 0.44/0.65           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain,
% 0.44/0.65      (((k9_relat_1 @ sk_C_1 @ 
% 0.44/0.65         (k8_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ sk_B))
% 0.44/0.65         = (k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1))),
% 0.44/0.65      inference('demod', [status(thm)], ['17', '20'])).
% 0.44/0.65  thf('22', plain,
% 0.44/0.65      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.65        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 0.44/0.65      inference('demod', [status(thm)], ['0', '14'])).
% 0.44/0.65  thf(t48_funct_2, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i]:
% 0.44/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.65         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( A ) ) ) ))).
% 0.44/0.65  thf('23', plain,
% 0.44/0.65      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.44/0.65         (((X40) = (k1_xboole_0))
% 0.44/0.65          | ~ (v1_funct_1 @ X39)
% 0.44/0.65          | ~ (v1_funct_2 @ X39 @ X38 @ X40)
% 0.44/0.65          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X40)))
% 0.44/0.65          | ((k8_relset_1 @ X38 @ X40 @ X39 @ X40) = (X38)))),
% 0.44/0.65      inference('cnf', [status(esa)], [t48_funct_2])).
% 0.44/0.65  thf('24', plain,
% 0.44/0.65      ((((k8_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ sk_B)
% 0.44/0.65          = (k1_relat_1 @ sk_C_1))
% 0.44/0.65        | ~ (v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)
% 0.44/0.65        | ~ (v1_funct_1 @ sk_C_1)
% 0.44/0.65        | ((sk_B) = (k1_xboole_0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['22', '23'])).
% 0.44/0.65  thf('25', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('26', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.44/0.65      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.44/0.65  thf('27', plain, ((v1_funct_2 @ sk_C_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)),
% 0.44/0.65      inference('demod', [status(thm)], ['25', '26'])).
% 0.44/0.65  thf('28', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('29', plain,
% 0.44/0.66      ((((k8_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ sk_B)
% 0.44/0.66          = (k1_relat_1 @ sk_C_1))
% 0.44/0.66        | ((sk_B) = (k1_xboole_0)))),
% 0.44/0.66      inference('demod', [status(thm)], ['24', '27', '28'])).
% 0.44/0.66  thf('30', plain, (((sk_B) != (k1_xboole_0))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('31', plain,
% 0.44/0.66      (((k8_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ sk_B)
% 0.44/0.66         = (k1_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.44/0.66  thf('32', plain,
% 0.44/0.66      (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1))
% 0.44/0.66         = (k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['21', '31'])).
% 0.44/0.66  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.44/0.66  thf(t69_enumset1, axiom,
% 0.44/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.66  thf('34', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.44/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.66  thf('35', plain,
% 0.44/0.66      ((m1_subset_1 @ sk_C_1 @ 
% 0.44/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf(cc2_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.44/0.66  thf('36', plain,
% 0.44/0.66      (![X11 : $i, X12 : $i]:
% 0.44/0.66         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.44/0.66          | (v1_relat_1 @ X11)
% 0.44/0.66          | ~ (v1_relat_1 @ X12))),
% 0.44/0.66      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.44/0.66  thf('37', plain,
% 0.44/0.66      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.44/0.66        | (v1_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.66  thf(fc6_relat_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.44/0.66  thf('38', plain,
% 0.44/0.66      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 0.44/0.66      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.44/0.66  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.44/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.66  thf('40', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.44/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.66  thf(d16_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ![B:$i]:
% 0.44/0.66         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.44/0.66  thf('41', plain,
% 0.44/0.66      (![X13 : $i, X14 : $i]:
% 0.44/0.66         (((k11_relat_1 @ X13 @ X14) = (k9_relat_1 @ X13 @ (k1_tarski @ X14)))
% 0.44/0.66          | ~ (v1_relat_1 @ X13))),
% 0.44/0.66      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.44/0.66  thf('42', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i]:
% 0.44/0.66         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.44/0.66          | ~ (v1_relat_1 @ X1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['40', '41'])).
% 0.44/0.66  thf('43', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k11_relat_1 @ sk_C_1 @ X0)
% 0.44/0.66           = (k9_relat_1 @ sk_C_1 @ (k2_tarski @ X0 @ X0)))),
% 0.44/0.66      inference('sup-', [status(thm)], ['39', '42'])).
% 0.44/0.66  thf('44', plain,
% 0.44/0.66      (![X0 : $i]:
% 0.44/0.66         ((k11_relat_1 @ sk_C_1 @ X0)
% 0.44/0.66           = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ X0)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['34', '43'])).
% 0.44/0.66  thf('45', plain,
% 0.44/0.66      (((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.44/0.66         = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['33', '44'])).
% 0.44/0.66  thf(t146_relat_1, axiom,
% 0.44/0.66    (![A:$i]:
% 0.44/0.66     ( ( v1_relat_1 @ A ) =>
% 0.44/0.66       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.44/0.66  thf('46', plain,
% 0.44/0.66      (![X17 : $i]:
% 0.44/0.66         (((k9_relat_1 @ X17 @ (k1_relat_1 @ X17)) = (k2_relat_1 @ X17))
% 0.44/0.66          | ~ (v1_relat_1 @ X17))),
% 0.44/0.66      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.44/0.66  thf('47', plain,
% 0.44/0.66      (((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.44/0.66         = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.44/0.66      inference('sup+', [status(thm)], ['33', '44'])).
% 0.44/0.66  thf('48', plain,
% 0.44/0.66      ((((k11_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 0.44/0.66        | ~ (v1_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['46', '47'])).
% 0.44/0.66  thf('49', plain, ((v1_relat_1 @ sk_C_1)),
% 0.44/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.66  thf('50', plain, (((k11_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['48', '49'])).
% 0.44/0.66  thf('51', plain,
% 0.44/0.66      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.44/0.66      inference('demod', [status(thm)], ['45', '50'])).
% 0.44/0.66  thf('52', plain,
% 0.44/0.66      (((k2_relat_1 @ sk_C_1)
% 0.44/0.66         = (k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['32', '51'])).
% 0.44/0.66  thf('53', plain,
% 0.44/0.66      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.44/0.66         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('54', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.44/0.66  thf('55', plain,
% 0.44/0.66      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1)
% 0.44/0.66         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.44/0.66      inference('demod', [status(thm)], ['53', '54'])).
% 0.44/0.66  thf('56', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.44/0.66  thf(d1_tarski, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.44/0.66       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.44/0.66  thf('57', plain,
% 0.44/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.66         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.44/0.66      inference('cnf', [status(esa)], [d1_tarski])).
% 0.44/0.66  thf('58', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.66      inference('simplify', [status(thm)], ['57'])).
% 0.44/0.66  thf('59', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('sup+', [status(thm)], ['56', '58'])).
% 0.44/0.66  thf(t117_funct_1, axiom,
% 0.44/0.66    (![A:$i,B:$i]:
% 0.44/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.44/0.66       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.44/0.66         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.44/0.66  thf('60', plain,
% 0.44/0.66      (![X18 : $i, X19 : $i]:
% 0.44/0.66         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.44/0.66          | ((k11_relat_1 @ X19 @ X18) = (k1_tarski @ (k1_funct_1 @ X19 @ X18)))
% 0.44/0.66          | ~ (v1_funct_1 @ X19)
% 0.44/0.66          | ~ (v1_relat_1 @ X19))),
% 0.44/0.66      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.44/0.66  thf('61', plain,
% 0.44/0.66      ((~ (v1_relat_1 @ sk_C_1)
% 0.44/0.66        | ~ (v1_funct_1 @ sk_C_1)
% 0.44/0.66        | ((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.44/0.66            = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A))))),
% 0.44/0.66      inference('sup-', [status(thm)], ['59', '60'])).
% 0.44/0.66  thf('62', plain, ((v1_relat_1 @ sk_C_1)),
% 0.44/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.66  thf('63', plain, ((v1_funct_1 @ sk_C_1)),
% 0.44/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.66  thf('64', plain,
% 0.44/0.66      (((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.44/0.66         = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.44/0.66      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.44/0.66  thf('65', plain, (((k11_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['48', '49'])).
% 0.44/0.66  thf('66', plain,
% 0.44/0.66      (((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.44/0.66      inference('demod', [status(thm)], ['64', '65'])).
% 0.44/0.66  thf('67', plain,
% 0.44/0.66      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1)
% 0.44/0.66         != (k2_relat_1 @ sk_C_1))),
% 0.44/0.66      inference('demod', [status(thm)], ['55', '66'])).
% 0.44/0.66  thf('68', plain, ($false),
% 0.44/0.66      inference('simplify_reflect-', [status(thm)], ['52', '67'])).
% 0.44/0.66  
% 0.44/0.66  % SZS output end Refutation
% 0.44/0.66  
% 0.44/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
