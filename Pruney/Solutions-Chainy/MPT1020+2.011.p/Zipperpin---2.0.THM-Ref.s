%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cGIXH9I6e0

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:02 EST 2020

% Result     : Theorem 26.08s
% Output     : Refutation 26.08s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 251 expanded)
%              Number of leaves         :   40 (  91 expanded)
%              Depth                    :   15
%              Number of atoms          : 1392 (5068 expanded)
%              Number of equality atoms :   62 (  76 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X4 ) )
      = ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_funct_1 @ X0 )
        = ( k6_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X0 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('20',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('22',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k2_funct_2 @ X37 @ X36 )
        = ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( v3_funct_2 @ X36 @ X37 @ X37 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('23',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B_1 )
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B_1 )
    = ( k2_funct_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('29',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B_1 ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','37'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('40',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('41',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('55',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( X43
        = ( k2_funct_1 @ X46 ) )
      | ~ ( r2_relset_1 @ X45 @ X45 @ ( k1_partfun1 @ X45 @ X44 @ X44 @ X45 @ X46 @ X43 ) @ ( k6_partfun1 @ X45 ) )
      | ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('58',plain,(
    ! [X38: $i] :
      ( ( k6_partfun1 @ X38 )
      = ( k6_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( X43
        = ( k2_funct_1 @ X46 ) )
      | ~ ( r2_relset_1 @ X45 @ X45 @ ( k1_partfun1 @ X45 @ X44 @ X44 @ X45 @ X46 @ X43 ) @ ( k6_relat_1 @ X45 ) )
      | ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X46 )
      | ( ( k2_relset_1 @ X45 @ X44 @ X46 )
       != X44 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X45 @ X44 )
      | ~ ( v1_funct_1 @ X46 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B_1 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('67',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('72',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k2_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('74',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( v3_funct_2 @ X25 @ X26 @ X27 )
      | ( v2_funct_2 @ X25 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('75',plain,
    ( ( v2_funct_2 @ sk_B_1 @ sk_A )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_funct_2 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('79',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v2_funct_2 @ X29 @ X28 )
      | ( ( k2_relat_1 @ X29 )
        = X28 )
      | ~ ( v5_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v5_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('82',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('83',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('85',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    v5_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['80','83','86'])).

thf('88',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['72','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_1 @ X25 )
      | ~ ( v3_funct_2 @ X25 @ X26 @ X27 )
      | ( v2_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('91',plain,
    ( ( v2_funct_1 @ sk_B_1 )
    | ~ ( v3_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    v3_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','88','94'])).

thf('96',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B_1 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['20','27'])).

thf('98',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('101',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['98','101'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('103',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('104',plain,(
    $false ),
    inference(demod,[status(thm)],['38','102','103'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cGIXH9I6e0
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:59:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 26.08/26.32  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 26.08/26.32  % Solved by: fo/fo7.sh
% 26.08/26.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.08/26.32  % done 7163 iterations in 25.853s
% 26.08/26.32  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 26.08/26.32  % SZS output start Refutation
% 26.08/26.32  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 26.08/26.32  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 26.08/26.32  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 26.08/26.32  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 26.08/26.32  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 26.08/26.32  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 26.08/26.32  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 26.08/26.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 26.08/26.32  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 26.08/26.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 26.08/26.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.08/26.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 26.08/26.32  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 26.08/26.32  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 26.08/26.32  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 26.08/26.32  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 26.08/26.32  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 26.08/26.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 26.08/26.32  thf(sk_C_type, type, sk_C: $i).
% 26.08/26.32  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 26.08/26.32  thf(sk_B_1_type, type, sk_B_1: $i).
% 26.08/26.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 26.08/26.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 26.08/26.32  thf(sk_A_type, type, sk_A: $i).
% 26.08/26.32  thf(t29_relset_1, axiom,
% 26.08/26.32    (![A:$i]:
% 26.08/26.32     ( m1_subset_1 @
% 26.08/26.32       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 26.08/26.32  thf('0', plain,
% 26.08/26.32      (![X24 : $i]:
% 26.08/26.32         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 26.08/26.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 26.08/26.32      inference('cnf', [status(esa)], [t29_relset_1])).
% 26.08/26.32  thf(cc3_relset_1, axiom,
% 26.08/26.32    (![A:$i,B:$i]:
% 26.08/26.32     ( ( v1_xboole_0 @ A ) =>
% 26.08/26.32       ( ![C:$i]:
% 26.08/26.32         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.08/26.32           ( v1_xboole_0 @ C ) ) ) ))).
% 26.08/26.32  thf('1', plain,
% 26.08/26.32      (![X11 : $i, X12 : $i, X13 : $i]:
% 26.08/26.32         (~ (v1_xboole_0 @ X11)
% 26.08/26.32          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 26.08/26.32          | (v1_xboole_0 @ X12))),
% 26.08/26.32      inference('cnf', [status(esa)], [cc3_relset_1])).
% 26.08/26.32  thf('2', plain,
% 26.08/26.32      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 26.08/26.32      inference('sup-', [status(thm)], ['0', '1'])).
% 26.08/26.32  thf(t8_boole, axiom,
% 26.08/26.32    (![A:$i,B:$i]:
% 26.08/26.32     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 26.08/26.32  thf('3', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i]:
% 26.08/26.32         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 26.08/26.32      inference('cnf', [status(esa)], [t8_boole])).
% 26.08/26.32  thf('4', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i]:
% 26.08/26.32         (~ (v1_xboole_0 @ X0)
% 26.08/26.32          | ((k6_relat_1 @ X0) = (X1))
% 26.08/26.32          | ~ (v1_xboole_0 @ X1))),
% 26.08/26.32      inference('sup-', [status(thm)], ['2', '3'])).
% 26.08/26.32  thf(t67_funct_1, axiom,
% 26.08/26.32    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 26.08/26.32  thf('5', plain,
% 26.08/26.32      (![X4 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X4)) = (k6_relat_1 @ X4))),
% 26.08/26.32      inference('cnf', [status(esa)], [t67_funct_1])).
% 26.08/26.32  thf('6', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i]:
% 26.08/26.32         (((k2_funct_1 @ X0) = (k6_relat_1 @ X1))
% 26.08/26.32          | ~ (v1_xboole_0 @ X0)
% 26.08/26.32          | ~ (v1_xboole_0 @ X1))),
% 26.08/26.32      inference('sup+', [status(thm)], ['4', '5'])).
% 26.08/26.32  thf('7', plain,
% 26.08/26.32      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 26.08/26.32      inference('sup-', [status(thm)], ['0', '1'])).
% 26.08/26.32  thf('8', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i]:
% 26.08/26.32         ((v1_xboole_0 @ (k2_funct_1 @ X0))
% 26.08/26.32          | ~ (v1_xboole_0 @ X1)
% 26.08/26.32          | ~ (v1_xboole_0 @ X0)
% 26.08/26.32          | ~ (v1_xboole_0 @ X1))),
% 26.08/26.32      inference('sup+', [status(thm)], ['6', '7'])).
% 26.08/26.32  thf('9', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i]:
% 26.08/26.32         (~ (v1_xboole_0 @ X0)
% 26.08/26.32          | ~ (v1_xboole_0 @ X1)
% 26.08/26.32          | (v1_xboole_0 @ (k2_funct_1 @ X0)))),
% 26.08/26.32      inference('simplify', [status(thm)], ['8'])).
% 26.08/26.32  thf('10', plain,
% 26.08/26.32      (![X0 : $i]: ((v1_xboole_0 @ (k2_funct_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 26.08/26.32      inference('condensation', [status(thm)], ['9'])).
% 26.08/26.32  thf('11', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i]:
% 26.08/26.32         (~ (v1_xboole_0 @ X0)
% 26.08/26.32          | ((k6_relat_1 @ X0) = (X1))
% 26.08/26.32          | ~ (v1_xboole_0 @ X1))),
% 26.08/26.32      inference('sup-', [status(thm)], ['2', '3'])).
% 26.08/26.32  thf('12', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i]:
% 26.08/26.32         (~ (v1_xboole_0 @ X0)
% 26.08/26.32          | ((k6_relat_1 @ X0) = (X1))
% 26.08/26.32          | ~ (v1_xboole_0 @ X1))),
% 26.08/26.32      inference('sup-', [status(thm)], ['2', '3'])).
% 26.08/26.32  thf('13', plain,
% 26.08/26.32      (![X24 : $i]:
% 26.08/26.32         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 26.08/26.32          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 26.08/26.32      inference('cnf', [status(esa)], [t29_relset_1])).
% 26.08/26.32  thf(redefinition_r2_relset_1, axiom,
% 26.08/26.32    (![A:$i,B:$i,C:$i,D:$i]:
% 26.08/26.32     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.08/26.32         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.08/26.32       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 26.08/26.32  thf('14', plain,
% 26.08/26.32      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 26.08/26.32         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 26.08/26.32          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 26.08/26.32          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 26.08/26.32          | ((X20) != (X23)))),
% 26.08/26.32      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 26.08/26.32  thf('15', plain,
% 26.08/26.32      (![X21 : $i, X22 : $i, X23 : $i]:
% 26.08/26.32         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 26.08/26.32          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 26.08/26.32      inference('simplify', [status(thm)], ['14'])).
% 26.08/26.32  thf('16', plain,
% 26.08/26.32      (![X0 : $i]:
% 26.08/26.32         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 26.08/26.32      inference('sup-', [status(thm)], ['13', '15'])).
% 26.08/26.32  thf('17', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i]:
% 26.08/26.32         ((r2_relset_1 @ X1 @ X1 @ X0 @ (k6_relat_1 @ X1))
% 26.08/26.32          | ~ (v1_xboole_0 @ X0)
% 26.08/26.32          | ~ (v1_xboole_0 @ X1))),
% 26.08/26.32      inference('sup+', [status(thm)], ['12', '16'])).
% 26.08/26.32  thf('18', plain,
% 26.08/26.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.08/26.32         ((r2_relset_1 @ X1 @ X1 @ X2 @ X0)
% 26.08/26.32          | ~ (v1_xboole_0 @ X0)
% 26.08/26.32          | ~ (v1_xboole_0 @ X1)
% 26.08/26.32          | ~ (v1_xboole_0 @ X1)
% 26.08/26.32          | ~ (v1_xboole_0 @ X2))),
% 26.08/26.33      inference('sup+', [status(thm)], ['11', '17'])).
% 26.08/26.33  thf('19', plain,
% 26.08/26.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.08/26.33         (~ (v1_xboole_0 @ X2)
% 26.08/26.33          | ~ (v1_xboole_0 @ X1)
% 26.08/26.33          | ~ (v1_xboole_0 @ X0)
% 26.08/26.33          | (r2_relset_1 @ X1 @ X1 @ X2 @ X0))),
% 26.08/26.33      inference('simplify', [status(thm)], ['18'])).
% 26.08/26.33  thf(t87_funct_2, conjecture,
% 26.08/26.33    (![A:$i,B:$i]:
% 26.08/26.33     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 26.08/26.33         ( v3_funct_2 @ B @ A @ A ) & 
% 26.08/26.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 26.08/26.33       ( ![C:$i]:
% 26.08/26.33         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 26.08/26.33             ( v3_funct_2 @ C @ A @ A ) & 
% 26.08/26.33             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 26.08/26.33           ( ( r2_relset_1 @
% 26.08/26.33               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 26.08/26.33               ( k6_partfun1 @ A ) ) =>
% 26.08/26.33             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 26.08/26.33  thf(zf_stmt_0, negated_conjecture,
% 26.08/26.33    (~( ![A:$i,B:$i]:
% 26.08/26.33        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 26.08/26.33            ( v3_funct_2 @ B @ A @ A ) & 
% 26.08/26.33            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 26.08/26.33          ( ![C:$i]:
% 26.08/26.33            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 26.08/26.33                ( v3_funct_2 @ C @ A @ A ) & 
% 26.08/26.33                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 26.08/26.33              ( ( r2_relset_1 @
% 26.08/26.33                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 26.08/26.33                  ( k6_partfun1 @ A ) ) =>
% 26.08/26.33                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 26.08/26.33    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 26.08/26.33  thf('20', plain,
% 26.08/26.33      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B_1))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('21', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf(redefinition_k2_funct_2, axiom,
% 26.08/26.33    (![A:$i,B:$i]:
% 26.08/26.33     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 26.08/26.33         ( v3_funct_2 @ B @ A @ A ) & 
% 26.08/26.33         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 26.08/26.33       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 26.08/26.33  thf('22', plain,
% 26.08/26.33      (![X36 : $i, X37 : $i]:
% 26.08/26.33         (((k2_funct_2 @ X37 @ X36) = (k2_funct_1 @ X36))
% 26.08/26.33          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))
% 26.08/26.33          | ~ (v3_funct_2 @ X36 @ X37 @ X37)
% 26.08/26.33          | ~ (v1_funct_2 @ X36 @ X37 @ X37)
% 26.08/26.33          | ~ (v1_funct_1 @ X36))),
% 26.08/26.33      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 26.08/26.33  thf('23', plain,
% 26.08/26.33      ((~ (v1_funct_1 @ sk_B_1)
% 26.08/26.33        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 26.08/26.33        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 26.08/26.33        | ((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1)))),
% 26.08/26.33      inference('sup-', [status(thm)], ['21', '22'])).
% 26.08/26.33  thf('24', plain, ((v1_funct_1 @ sk_B_1)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('25', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('26', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('27', plain, (((k2_funct_2 @ sk_A @ sk_B_1) = (k2_funct_1 @ sk_B_1))),
% 26.08/26.33      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 26.08/26.33  thf('28', plain,
% 26.08/26.33      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 26.08/26.33      inference('demod', [status(thm)], ['20', '27'])).
% 26.08/26.33  thf('29', plain,
% 26.08/26.33      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B_1))
% 26.08/26.33        | ~ (v1_xboole_0 @ sk_A)
% 26.08/26.33        | ~ (v1_xboole_0 @ sk_C))),
% 26.08/26.33      inference('sup-', [status(thm)], ['19', '28'])).
% 26.08/26.33  thf('30', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('31', plain,
% 26.08/26.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 26.08/26.33         (~ (v1_xboole_0 @ X11)
% 26.08/26.33          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 26.08/26.33          | (v1_xboole_0 @ X12))),
% 26.08/26.33      inference('cnf', [status(esa)], [cc3_relset_1])).
% 26.08/26.33  thf('32', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 26.08/26.33      inference('sup-', [status(thm)], ['30', '31'])).
% 26.08/26.33  thf('33', plain,
% 26.08/26.33      ((~ (v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B_1)))),
% 26.08/26.33      inference('clc', [status(thm)], ['29', '32'])).
% 26.08/26.33  thf('34', plain, ((~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_A))),
% 26.08/26.33      inference('sup-', [status(thm)], ['10', '33'])).
% 26.08/26.33  thf('35', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('36', plain,
% 26.08/26.33      (![X11 : $i, X12 : $i, X13 : $i]:
% 26.08/26.33         (~ (v1_xboole_0 @ X11)
% 26.08/26.33          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 26.08/26.33          | (v1_xboole_0 @ X12))),
% 26.08/26.33      inference('cnf', [status(esa)], [cc3_relset_1])).
% 26.08/26.33  thf('37', plain, (((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ sk_A))),
% 26.08/26.33      inference('sup-', [status(thm)], ['35', '36'])).
% 26.08/26.33  thf('38', plain, (~ (v1_xboole_0 @ sk_A)),
% 26.08/26.33      inference('clc', [status(thm)], ['34', '37'])).
% 26.08/26.33  thf('39', plain,
% 26.08/26.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 26.08/26.33        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 26.08/26.33        (k6_partfun1 @ sk_A))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf(redefinition_k6_partfun1, axiom,
% 26.08/26.33    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 26.08/26.33  thf('40', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 26.08/26.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 26.08/26.33  thf('41', plain,
% 26.08/26.33      ((r2_relset_1 @ sk_A @ sk_A @ 
% 26.08/26.33        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 26.08/26.33        (k6_relat_1 @ sk_A))),
% 26.08/26.33      inference('demod', [status(thm)], ['39', '40'])).
% 26.08/26.33  thf('42', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('43', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf(dt_k1_partfun1, axiom,
% 26.08/26.33    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 26.08/26.33     ( ( ( v1_funct_1 @ E ) & 
% 26.08/26.33         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 26.08/26.33         ( v1_funct_1 @ F ) & 
% 26.08/26.33         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 26.08/26.33       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 26.08/26.33         ( m1_subset_1 @
% 26.08/26.33           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 26.08/26.33           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 26.08/26.33  thf('44', plain,
% 26.08/26.33      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 26.08/26.33         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 26.08/26.33          | ~ (v1_funct_1 @ X30)
% 26.08/26.33          | ~ (v1_funct_1 @ X33)
% 26.08/26.33          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 26.08/26.33          | (m1_subset_1 @ (k1_partfun1 @ X31 @ X32 @ X34 @ X35 @ X30 @ X33) @ 
% 26.08/26.33             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X35))))),
% 26.08/26.33      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 26.08/26.33  thf('45', plain,
% 26.08/26.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.08/26.33         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1) @ 
% 26.08/26.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 26.08/26.33          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 26.08/26.33          | ~ (v1_funct_1 @ X1)
% 26.08/26.33          | ~ (v1_funct_1 @ sk_B_1))),
% 26.08/26.33      inference('sup-', [status(thm)], ['43', '44'])).
% 26.08/26.33  thf('46', plain, ((v1_funct_1 @ sk_B_1)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('47', plain,
% 26.08/26.33      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.08/26.33         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B_1 @ X1) @ 
% 26.08/26.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 26.08/26.33          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 26.08/26.33          | ~ (v1_funct_1 @ X1))),
% 26.08/26.33      inference('demod', [status(thm)], ['45', '46'])).
% 26.08/26.33  thf('48', plain,
% 26.08/26.33      ((~ (v1_funct_1 @ sk_C)
% 26.08/26.33        | (m1_subset_1 @ 
% 26.08/26.33           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 26.08/26.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 26.08/26.33      inference('sup-', [status(thm)], ['42', '47'])).
% 26.08/26.33  thf('49', plain, ((v1_funct_1 @ sk_C)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('50', plain,
% 26.08/26.33      ((m1_subset_1 @ 
% 26.08/26.33        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ 
% 26.08/26.33        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('demod', [status(thm)], ['48', '49'])).
% 26.08/26.33  thf('51', plain,
% 26.08/26.33      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 26.08/26.33         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 26.08/26.33          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 26.08/26.33          | ((X20) = (X23))
% 26.08/26.33          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 26.08/26.33      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 26.08/26.33  thf('52', plain,
% 26.08/26.33      (![X0 : $i]:
% 26.08/26.33         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 26.08/26.33             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) @ X0)
% 26.08/26.33          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C) = (X0))
% 26.08/26.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 26.08/26.33      inference('sup-', [status(thm)], ['50', '51'])).
% 26.08/26.33  thf('53', plain,
% 26.08/26.33      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 26.08/26.33           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 26.08/26.33        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 26.08/26.33            = (k6_relat_1 @ sk_A)))),
% 26.08/26.33      inference('sup-', [status(thm)], ['41', '52'])).
% 26.08/26.33  thf('54', plain,
% 26.08/26.33      (![X24 : $i]:
% 26.08/26.33         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 26.08/26.33          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 26.08/26.33      inference('cnf', [status(esa)], [t29_relset_1])).
% 26.08/26.33  thf('55', plain,
% 26.08/26.33      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B_1 @ sk_C)
% 26.08/26.33         = (k6_relat_1 @ sk_A))),
% 26.08/26.33      inference('demod', [status(thm)], ['53', '54'])).
% 26.08/26.33  thf('56', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf(t36_funct_2, axiom,
% 26.08/26.33    (![A:$i,B:$i,C:$i]:
% 26.08/26.33     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 26.08/26.33         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 26.08/26.33       ( ![D:$i]:
% 26.08/26.33         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 26.08/26.33             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 26.08/26.33           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 26.08/26.33               ( r2_relset_1 @
% 26.08/26.33                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 26.08/26.33                 ( k6_partfun1 @ A ) ) & 
% 26.08/26.33               ( v2_funct_1 @ C ) ) =>
% 26.08/26.33             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 26.08/26.33               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 26.08/26.33  thf('57', plain,
% 26.08/26.33      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 26.08/26.33         (~ (v1_funct_1 @ X43)
% 26.08/26.33          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 26.08/26.33          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 26.08/26.33          | ((X43) = (k2_funct_1 @ X46))
% 26.08/26.33          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 26.08/26.33               (k1_partfun1 @ X45 @ X44 @ X44 @ X45 @ X46 @ X43) @ 
% 26.08/26.33               (k6_partfun1 @ X45))
% 26.08/26.33          | ((X44) = (k1_xboole_0))
% 26.08/26.33          | ((X45) = (k1_xboole_0))
% 26.08/26.33          | ~ (v2_funct_1 @ X46)
% 26.08/26.33          | ((k2_relset_1 @ X45 @ X44 @ X46) != (X44))
% 26.08/26.33          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 26.08/26.33          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 26.08/26.33          | ~ (v1_funct_1 @ X46))),
% 26.08/26.33      inference('cnf', [status(esa)], [t36_funct_2])).
% 26.08/26.33  thf('58', plain, (![X38 : $i]: ((k6_partfun1 @ X38) = (k6_relat_1 @ X38))),
% 26.08/26.33      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 26.08/26.33  thf('59', plain,
% 26.08/26.33      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 26.08/26.33         (~ (v1_funct_1 @ X43)
% 26.08/26.33          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 26.08/26.33          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 26.08/26.33          | ((X43) = (k2_funct_1 @ X46))
% 26.08/26.33          | ~ (r2_relset_1 @ X45 @ X45 @ 
% 26.08/26.33               (k1_partfun1 @ X45 @ X44 @ X44 @ X45 @ X46 @ X43) @ 
% 26.08/26.33               (k6_relat_1 @ X45))
% 26.08/26.33          | ((X44) = (k1_xboole_0))
% 26.08/26.33          | ((X45) = (k1_xboole_0))
% 26.08/26.33          | ~ (v2_funct_1 @ X46)
% 26.08/26.33          | ((k2_relset_1 @ X45 @ X44 @ X46) != (X44))
% 26.08/26.33          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 26.08/26.33          | ~ (v1_funct_2 @ X46 @ X45 @ X44)
% 26.08/26.33          | ~ (v1_funct_1 @ X46))),
% 26.08/26.33      inference('demod', [status(thm)], ['57', '58'])).
% 26.08/26.33  thf('60', plain,
% 26.08/26.33      (![X0 : $i]:
% 26.08/26.33         (~ (v1_funct_1 @ X0)
% 26.08/26.33          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 26.08/26.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 26.08/26.33          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 26.08/26.33          | ~ (v2_funct_1 @ X0)
% 26.08/26.33          | ((sk_A) = (k1_xboole_0))
% 26.08/26.33          | ((sk_A) = (k1_xboole_0))
% 26.08/26.33          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 26.08/26.33               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 26.08/26.33               (k6_relat_1 @ sk_A))
% 26.08/26.33          | ((sk_C) = (k2_funct_1 @ X0))
% 26.08/26.33          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 26.08/26.33          | ~ (v1_funct_1 @ sk_C))),
% 26.08/26.33      inference('sup-', [status(thm)], ['56', '59'])).
% 26.08/26.33  thf('61', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('63', plain,
% 26.08/26.33      (![X0 : $i]:
% 26.08/26.33         (~ (v1_funct_1 @ X0)
% 26.08/26.33          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 26.08/26.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 26.08/26.33          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 26.08/26.33          | ~ (v2_funct_1 @ X0)
% 26.08/26.33          | ((sk_A) = (k1_xboole_0))
% 26.08/26.33          | ((sk_A) = (k1_xboole_0))
% 26.08/26.33          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 26.08/26.33               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 26.08/26.33               (k6_relat_1 @ sk_A))
% 26.08/26.33          | ((sk_C) = (k2_funct_1 @ X0)))),
% 26.08/26.33      inference('demod', [status(thm)], ['60', '61', '62'])).
% 26.08/26.33  thf('64', plain,
% 26.08/26.33      (![X0 : $i]:
% 26.08/26.33         (((sk_C) = (k2_funct_1 @ X0))
% 26.08/26.33          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 26.08/26.33               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 26.08/26.33               (k6_relat_1 @ sk_A))
% 26.08/26.33          | ((sk_A) = (k1_xboole_0))
% 26.08/26.33          | ~ (v2_funct_1 @ X0)
% 26.08/26.33          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 26.08/26.33          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 26.08/26.33          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 26.08/26.33          | ~ (v1_funct_1 @ X0))),
% 26.08/26.33      inference('simplify', [status(thm)], ['63'])).
% 26.08/26.33  thf('65', plain,
% 26.08/26.33      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 26.08/26.33           (k6_relat_1 @ sk_A))
% 26.08/26.33        | ~ (v1_funct_1 @ sk_B_1)
% 26.08/26.33        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 26.08/26.33        | ~ (m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 26.08/26.33        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) != (sk_A))
% 26.08/26.33        | ~ (v2_funct_1 @ sk_B_1)
% 26.08/26.33        | ((sk_A) = (k1_xboole_0))
% 26.08/26.33        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 26.08/26.33      inference('sup-', [status(thm)], ['55', '64'])).
% 26.08/26.33  thf('66', plain,
% 26.08/26.33      (![X0 : $i]:
% 26.08/26.33         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 26.08/26.33      inference('sup-', [status(thm)], ['13', '15'])).
% 26.08/26.33  thf('67', plain, ((v1_funct_1 @ sk_B_1)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('68', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('69', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('70', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf(redefinition_k2_relset_1, axiom,
% 26.08/26.33    (![A:$i,B:$i,C:$i]:
% 26.08/26.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.08/26.33       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 26.08/26.33  thf('71', plain,
% 26.08/26.33      (![X17 : $i, X18 : $i, X19 : $i]:
% 26.08/26.33         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 26.08/26.33          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 26.08/26.33      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 26.08/26.33  thf('72', plain,
% 26.08/26.33      (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k2_relat_1 @ sk_B_1))),
% 26.08/26.33      inference('sup-', [status(thm)], ['70', '71'])).
% 26.08/26.33  thf('73', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf(cc2_funct_2, axiom,
% 26.08/26.33    (![A:$i,B:$i,C:$i]:
% 26.08/26.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.08/26.33       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 26.08/26.33         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 26.08/26.33  thf('74', plain,
% 26.08/26.33      (![X25 : $i, X26 : $i, X27 : $i]:
% 26.08/26.33         (~ (v1_funct_1 @ X25)
% 26.08/26.33          | ~ (v3_funct_2 @ X25 @ X26 @ X27)
% 26.08/26.33          | (v2_funct_2 @ X25 @ X27)
% 26.08/26.33          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 26.08/26.33      inference('cnf', [status(esa)], [cc2_funct_2])).
% 26.08/26.33  thf('75', plain,
% 26.08/26.33      (((v2_funct_2 @ sk_B_1 @ sk_A)
% 26.08/26.33        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 26.08/26.33        | ~ (v1_funct_1 @ sk_B_1))),
% 26.08/26.33      inference('sup-', [status(thm)], ['73', '74'])).
% 26.08/26.33  thf('76', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('77', plain, ((v1_funct_1 @ sk_B_1)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('78', plain, ((v2_funct_2 @ sk_B_1 @ sk_A)),
% 26.08/26.33      inference('demod', [status(thm)], ['75', '76', '77'])).
% 26.08/26.33  thf(d3_funct_2, axiom,
% 26.08/26.33    (![A:$i,B:$i]:
% 26.08/26.33     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 26.08/26.33       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 26.08/26.33  thf('79', plain,
% 26.08/26.33      (![X28 : $i, X29 : $i]:
% 26.08/26.33         (~ (v2_funct_2 @ X29 @ X28)
% 26.08/26.33          | ((k2_relat_1 @ X29) = (X28))
% 26.08/26.33          | ~ (v5_relat_1 @ X29 @ X28)
% 26.08/26.33          | ~ (v1_relat_1 @ X29))),
% 26.08/26.33      inference('cnf', [status(esa)], [d3_funct_2])).
% 26.08/26.33  thf('80', plain,
% 26.08/26.33      ((~ (v1_relat_1 @ sk_B_1)
% 26.08/26.33        | ~ (v5_relat_1 @ sk_B_1 @ sk_A)
% 26.08/26.33        | ((k2_relat_1 @ sk_B_1) = (sk_A)))),
% 26.08/26.33      inference('sup-', [status(thm)], ['78', '79'])).
% 26.08/26.33  thf('81', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf(cc1_relset_1, axiom,
% 26.08/26.33    (![A:$i,B:$i,C:$i]:
% 26.08/26.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.08/26.33       ( v1_relat_1 @ C ) ))).
% 26.08/26.33  thf('82', plain,
% 26.08/26.33      (![X5 : $i, X6 : $i, X7 : $i]:
% 26.08/26.33         ((v1_relat_1 @ X5)
% 26.08/26.33          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 26.08/26.33      inference('cnf', [status(esa)], [cc1_relset_1])).
% 26.08/26.33  thf('83', plain, ((v1_relat_1 @ sk_B_1)),
% 26.08/26.33      inference('sup-', [status(thm)], ['81', '82'])).
% 26.08/26.33  thf('84', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf(cc2_relset_1, axiom,
% 26.08/26.33    (![A:$i,B:$i,C:$i]:
% 26.08/26.33     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 26.08/26.33       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 26.08/26.33  thf('85', plain,
% 26.08/26.33      (![X8 : $i, X9 : $i, X10 : $i]:
% 26.08/26.33         ((v5_relat_1 @ X8 @ X10)
% 26.08/26.33          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 26.08/26.33      inference('cnf', [status(esa)], [cc2_relset_1])).
% 26.08/26.33  thf('86', plain, ((v5_relat_1 @ sk_B_1 @ sk_A)),
% 26.08/26.33      inference('sup-', [status(thm)], ['84', '85'])).
% 26.08/26.33  thf('87', plain, (((k2_relat_1 @ sk_B_1) = (sk_A))),
% 26.08/26.33      inference('demod', [status(thm)], ['80', '83', '86'])).
% 26.08/26.33  thf('88', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A))),
% 26.08/26.33      inference('demod', [status(thm)], ['72', '87'])).
% 26.08/26.33  thf('89', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('90', plain,
% 26.08/26.33      (![X25 : $i, X26 : $i, X27 : $i]:
% 26.08/26.33         (~ (v1_funct_1 @ X25)
% 26.08/26.33          | ~ (v3_funct_2 @ X25 @ X26 @ X27)
% 26.08/26.33          | (v2_funct_1 @ X25)
% 26.08/26.33          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 26.08/26.33      inference('cnf', [status(esa)], [cc2_funct_2])).
% 26.08/26.33  thf('91', plain,
% 26.08/26.33      (((v2_funct_1 @ sk_B_1)
% 26.08/26.33        | ~ (v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 26.08/26.33        | ~ (v1_funct_1 @ sk_B_1))),
% 26.08/26.33      inference('sup-', [status(thm)], ['89', '90'])).
% 26.08/26.33  thf('92', plain, ((v3_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('93', plain, ((v1_funct_1 @ sk_B_1)),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('94', plain, ((v2_funct_1 @ sk_B_1)),
% 26.08/26.33      inference('demod', [status(thm)], ['91', '92', '93'])).
% 26.08/26.33  thf('95', plain,
% 26.08/26.33      ((((sk_A) != (sk_A))
% 26.08/26.33        | ((sk_A) = (k1_xboole_0))
% 26.08/26.33        | ((sk_C) = (k2_funct_1 @ sk_B_1)))),
% 26.08/26.33      inference('demod', [status(thm)],
% 26.08/26.33                ['65', '66', '67', '68', '69', '88', '94'])).
% 26.08/26.33  thf('96', plain,
% 26.08/26.33      ((((sk_C) = (k2_funct_1 @ sk_B_1)) | ((sk_A) = (k1_xboole_0)))),
% 26.08/26.33      inference('simplify', [status(thm)], ['95'])).
% 26.08/26.33  thf('97', plain,
% 26.08/26.33      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B_1))),
% 26.08/26.33      inference('demod', [status(thm)], ['20', '27'])).
% 26.08/26.33  thf('98', plain,
% 26.08/26.33      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 26.08/26.33      inference('sup-', [status(thm)], ['96', '97'])).
% 26.08/26.33  thf('99', plain,
% 26.08/26.33      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 26.08/26.33      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.08/26.33  thf('100', plain,
% 26.08/26.33      (![X21 : $i, X22 : $i, X23 : $i]:
% 26.08/26.33         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 26.08/26.33          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 26.08/26.33      inference('simplify', [status(thm)], ['14'])).
% 26.08/26.33  thf('101', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 26.08/26.33      inference('sup-', [status(thm)], ['99', '100'])).
% 26.08/26.33  thf('102', plain, (((sk_A) = (k1_xboole_0))),
% 26.08/26.33      inference('demod', [status(thm)], ['98', '101'])).
% 26.08/26.33  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 26.08/26.33  thf('103', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 26.08/26.33      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 26.08/26.33  thf('104', plain, ($false),
% 26.08/26.33      inference('demod', [status(thm)], ['38', '102', '103'])).
% 26.08/26.33  
% 26.08/26.33  % SZS output end Refutation
% 26.08/26.33  
% 26.08/26.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
