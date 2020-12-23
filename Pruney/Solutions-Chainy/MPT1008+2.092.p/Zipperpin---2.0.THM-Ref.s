%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Alxcng4L6c

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:44 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 190 expanded)
%              Number of leaves         :   43 (  77 expanded)
%              Depth                    :   12
%              Number of atoms          :  651 (2143 expanded)
%              Number of equality atoms :   59 ( 164 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('17',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X19 ) )
      | ( ( k11_relat_1 @ X19 @ X18 )
        = ( k1_tarski @ ( k1_funct_1 @ X19 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('27',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('28',plain,(
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

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k11_relat_1 @ X10 @ X11 )
        = ( k9_relat_1 @ X10 @ ( k1_tarski @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('35',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('36',plain,(
    v4_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X16
        = ( k7_relat_1 @ X16 @ X17 ) )
      | ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( sk_C_1
      = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('40',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('42',plain,
    ( sk_C_1
    = ( k7_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('43',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('44',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['21','22'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k11_relat_1 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['33','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','23','24','47'])).

thf('49',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['48','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Alxcng4L6c
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:44:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 87 iterations in 0.092s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.36/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(t62_funct_2, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.54         ( m1_subset_1 @
% 0.36/0.54           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.54         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.36/0.54           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.36/0.54            ( m1_subset_1 @
% 0.36/0.54              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.36/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.36/0.54            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.36/0.54              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.36/0.54  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d1_funct_2, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_1, axiom,
% 0.36/0.54    (![C:$i,B:$i,A:$i]:
% 0.36/0.54     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.36/0.54         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.36/0.54          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.36/0.54          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.36/0.54        | ((k1_tarski @ sk_A)
% 0.36/0.54            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf(zf_stmt_2, axiom,
% 0.36/0.54    (![B:$i,A:$i]:
% 0.36/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.54       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X29 : $i, X30 : $i]:
% 0.36/0.54         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.54  thf(zf_stmt_5, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.36/0.54         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.36/0.54          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.36/0.54          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.36/0.54        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((((sk_B) = (k1_xboole_0))
% 0.36/0.54        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['3', '6'])).
% 0.36/0.54  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('9', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.54  thf('11', plain,
% 0.36/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.54         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.36/0.54          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.36/0.54         = (k1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.54  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.36/0.54  thf(d1_tarski, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.54         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.54  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.36/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.54  thf('16', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['13', '15'])).
% 0.36/0.54  thf(t117_funct_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.36/0.54         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X18 : $i, X19 : $i]:
% 0.36/0.54         (~ (r2_hidden @ X18 @ (k1_relat_1 @ X19))
% 0.36/0.54          | ((k11_relat_1 @ X19 @ X18) = (k1_tarski @ (k1_funct_1 @ X19 @ X18)))
% 0.36/0.54          | ~ (v1_funct_1 @ X19)
% 0.36/0.54          | ~ (v1_relat_1 @ X19))),
% 0.36/0.54      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_C_1)
% 0.36/0.54        | ~ (v1_funct_1 @ sk_C_1)
% 0.36/0.54        | ((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.36/0.54            = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc2_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X8 : $i, X9 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.36/0.54          | (v1_relat_1 @ X8)
% 0.36/0.54          | ~ (v1_relat_1 @ X9))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.36/0.54        | (v1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf(fc6_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X12 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.54  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('24', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('25', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.36/0.54  thf(t69_enumset1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.54  thf('26', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf('27', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('28', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.54  thf(d16_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X10 : $i, X11 : $i]:
% 0.36/0.54         (((k11_relat_1 @ X10 @ X11) = (k9_relat_1 @ X10 @ (k1_tarski @ X11)))
% 0.36/0.54          | ~ (v1_relat_1 @ X10))),
% 0.36/0.54      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.36/0.54  thf('30', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.36/0.54          | ~ (v1_relat_1 @ X1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k11_relat_1 @ sk_C_1 @ X0)
% 0.36/0.54           = (k9_relat_1 @ sk_C_1 @ (k2_tarski @ X0 @ X0)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['27', '30'])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k11_relat_1 @ sk_C_1 @ X0)
% 0.36/0.54           = (k9_relat_1 @ sk_C_1 @ (k1_tarski @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['26', '31'])).
% 0.36/0.54  thf('33', plain,
% 0.36/0.54      (((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.36/0.54         = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['25', '32'])).
% 0.36/0.54  thf('34', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc2_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.36/0.54  thf('35', plain,
% 0.36/0.54      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.54         ((v4_relat_1 @ X20 @ X21)
% 0.36/0.54          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.36/0.54  thf('36', plain, ((v4_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.54  thf(t209_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.36/0.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.36/0.54  thf('37', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i]:
% 0.36/0.54         (((X16) = (k7_relat_1 @ X16 @ X17))
% 0.36/0.54          | ~ (v4_relat_1 @ X16 @ X17)
% 0.36/0.54          | ~ (v1_relat_1 @ X16))),
% 0.36/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.36/0.54  thf('38', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_C_1)
% 0.36/0.54        | ((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A))))),
% 0.36/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.36/0.54  thf('39', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('40', plain, (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_tarski @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['38', '39'])).
% 0.36/0.54  thf('41', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.36/0.54  thf('42', plain,
% 0.36/0.54      (((sk_C_1) = (k7_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.54  thf(t148_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ B ) =>
% 0.36/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.36/0.54  thf('43', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i]:
% 0.36/0.54         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.36/0.54          | ~ (v1_relat_1 @ X14))),
% 0.36/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.36/0.54  thf('44', plain,
% 0.36/0.54      ((((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup+', [status(thm)], ['42', '43'])).
% 0.36/0.54  thf('45', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.36/0.54  thf('46', plain,
% 0.36/0.54      (((k2_relat_1 @ sk_C_1) = (k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)))),
% 0.36/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.36/0.54  thf('47', plain, (((k2_relat_1 @ sk_C_1) = (k11_relat_1 @ sk_C_1 @ sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['33', '46'])).
% 0.36/0.54  thf('48', plain,
% 0.36/0.54      (((k2_relat_1 @ sk_C_1) = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['18', '23', '24', '47'])).
% 0.36/0.54  thf('49', plain,
% 0.36/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.36/0.54         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('50', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_C_1 @ 
% 0.36/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.54  thf('51', plain,
% 0.36/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.36/0.54         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.36/0.54          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.54  thf('52', plain,
% 0.36/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.36/0.54         = (k2_relat_1 @ sk_C_1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.36/0.54  thf('53', plain,
% 0.36/0.54      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.36/0.54      inference('demod', [status(thm)], ['49', '52'])).
% 0.36/0.54  thf('54', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['48', '53'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
