%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xiIWSU9nS0

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:41 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  224 (6168 expanded)
%              Number of leaves         :   45 (1917 expanded)
%              Depth                    :   26
%              Number of atoms          : 1429 (99685 expanded)
%              Number of equality atoms :  138 (3594 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('3',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( v1_relat_1 @ X62 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X49: $i] :
      ( ~ ( v2_funct_1 @ X49 )
      | ( ( k2_funct_1 @ X49 )
        = ( k4_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('6',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,
    ( ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X51: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X78: $i,X79: $i] :
      ( ( zip_tseitin_0 @ X78 @ X79 )
      | ( X78 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('22',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('23',plain,(
    ! [X78: $i,X79: $i] :
      ( ( zip_tseitin_0 @ X78 @ X79 )
      | ( X78 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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
    ! [X83: $i,X84: $i,X85: $i] :
      ( ~ ( zip_tseitin_0 @ X83 @ X84 )
      | ( zip_tseitin_1 @ X85 @ X83 @ X84 )
      | ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X83 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('26',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ~ ( v1_funct_2 @ X82 @ X80 @ X81 )
      | ( X80
        = ( k1_relset_1 @ X80 @ X81 @ X82 ) )
      | ~ ( zip_tseitin_1 @ X82 @ X81 @ X80 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('32',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( ( k1_relset_1 @ X66 @ X67 @ X65 )
        = ( k1_relat_1 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('33',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('37',plain,(
    ! [X61: $i] :
      ( ~ ( v2_funct_1 @ X61 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X61 ) )
        = X61 )
      | ~ ( v1_funct_1 @ X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('38',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('40',plain,(
    ! [X51: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('41',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('43',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X49: $i] :
      ( ~ ( v2_funct_1 @ X49 )
      | ( ( k2_funct_1 @ X49 )
        = ( k4_relat_1 @ X49 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('47',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('49',plain,(
    ! [X51: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('50',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('52',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('56',plain,(
    ! [X51: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X51 ) )
      | ~ ( v2_funct_1 @ X51 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('57',plain,
    ( ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','54','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('64',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['38','62','63','64','65'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X46: $i] :
      ( ( ( k1_relat_1 @ X46 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('68',plain,
    ( ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('70',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('72',plain,(
    ! [X68: $i,X69: $i,X70: $i] :
      ( ( ( k2_relset_1 @ X69 @ X70 @ X68 )
        = ( k2_relat_1 @ X68 ) )
      | ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('73',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['70','75'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('77',plain,(
    ! [X102: $i] :
      ( ( v1_funct_2 @ X102 @ ( k1_relat_1 @ X102 ) @ ( k2_relat_1 @ X102 ) )
      | ~ ( v1_funct_1 @ X102 )
      | ~ ( v1_relat_1 @ X102 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('78',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['38','62','63','64','65'])).

thf('80',plain,(
    ! [X46: $i] :
      ( ( ( k2_relat_1 @ X46 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('81',plain,
    ( ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('83',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('85',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('86',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','83','84','85'])).

thf('87',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','86'])).

thf('88',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('89',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('90',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_B = o_0_0_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,
    ( ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ o_0_0_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','91'])).

thf('93',plain,
    ( ( sk_B = o_0_0_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('94',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['38','62','63','64','65'])).

thf('95',plain,(
    ! [X46: $i] :
      ( ( ( k1_relat_1 @ X46 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('96',plain,(
    ! [X47: $i] :
      ( ( ( k2_relat_1 @ X47 )
       != k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('97',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('98',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('99',plain,(
    ! [X47: $i] :
      ( ( ( k2_relat_1 @ X47 )
       != o_0_0_xboole_0 )
      | ( X47 = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( ( k4_relat_1 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
      = o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['94','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf('103',plain,
    ( ( k4_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['38','62','63','64','65'])).

thf('104',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('105',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('106',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['73','74'])).

thf('108',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( sk_C = o_0_0_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['93','108'])).

thf('110',plain,
    ( ( sk_C = o_0_0_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['109'])).

thf(t66_relat_1,axiom,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('111',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t66_relat_1])).

thf('112',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('113',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('114',plain,
    ( ( k4_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['111','112','113'])).

thf(dt_k1_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('115',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X38 ) @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_subset_1])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('116',plain,(
    ! [X37: $i] :
      ( ( k1_subset_1 @ X37 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('117',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('118',plain,(
    ! [X37: $i] :
      ( ( k1_subset_1 @ X37 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( ( k1_relset_1 @ X66 @ X67 @ X65 )
        = ( k1_relat_1 @ X65 ) )
      | ~ ( m1_subset_1 @ X65 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X66 @ X67 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ o_0_0_xboole_0 )
      = ( k1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(t150_relat_1,axiom,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('122',plain,(
    ! [X42: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X42 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t150_relat_1])).

thf('123',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('124',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('125',plain,(
    ! [X42: $i] :
      ( ( k9_relat_1 @ o_0_0_xboole_0 @ X42 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('126',plain,(
    ! [X41: $i] :
      ( ( ( k9_relat_1 @ X41 @ ( k1_relat_1 @ X41 ) )
        = ( k2_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('127',plain,
    ( ( o_0_0_xboole_0
      = ( k2_relat_1 @ o_0_0_xboole_0 ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k4_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('129',plain,(
    ! [X46: $i] :
      ( ( ( k2_relat_1 @ X46 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X46 ) ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('130',plain,
    ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
      = ( k1_relat_1 @ o_0_0_xboole_0 ) )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('132',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ( v1_relat_1 @ X62 )
      | ~ ( m1_subset_1 @ X62 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X64 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('133',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['130','133'])).

thf('135',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['131','132'])).

thf('136',plain,
    ( o_0_0_xboole_0
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['127','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_relset_1 @ X1 @ X0 @ o_0_0_xboole_0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['121','136'])).

thf('138',plain,(
    ! [X80: $i,X81: $i,X82: $i] :
      ( ( X80
       != ( k1_relset_1 @ X80 @ X81 @ X82 ) )
      | ( v1_funct_2 @ X82 @ X80 @ X81 )
      | ~ ( zip_tseitin_1 @ X82 @ X81 @ X80 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 != o_0_0_xboole_0 )
      | ~ ( zip_tseitin_1 @ o_0_0_xboole_0 @ X0 @ X1 )
      | ( v1_funct_2 @ o_0_0_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0 )
      | ~ ( zip_tseitin_1 @ o_0_0_xboole_0 @ X0 @ o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X78: $i,X79: $i] :
      ( ( zip_tseitin_0 @ X78 @ X79 )
      | ( X79 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('142',plain,(
    ! [X78: $i] :
      ( zip_tseitin_0 @ X78 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('144',plain,(
    ! [X78: $i] :
      ( zip_tseitin_0 @ X78 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('146',plain,(
    ! [X83: $i,X84: $i,X85: $i] :
      ( ~ ( zip_tseitin_0 @ X83 @ X84 )
      | ( zip_tseitin_1 @ X85 @ X83 @ X84 )
      | ~ ( m1_subset_1 @ X85 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X83 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ o_0_0_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ o_0_0_xboole_0 @ X0 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['144','147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0 ) ),
    inference('simplify_reflect+',[status(thm)],['140','148'])).

thf('150',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['92','110','114','149'])).

thf('151',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('152',plain,(
    ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sat_resolution*',[status(thm)],['18','150','151'])).

thf('153',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','152'])).

thf('154',plain,
    ( ( sk_B = o_0_0_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('155',plain,
    ( ( k1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_B ),
    inference(demod,[status(thm)],['70','75'])).

thf('156',plain,(
    ! [X102: $i] :
      ( ( m1_subset_1 @ X102 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X102 ) @ ( k2_relat_1 @ X102 ) ) ) )
      | ~ ( v1_funct_1 @ X102 )
      | ~ ( v1_relat_1 @ X102 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('157',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['155','156'])).

thf('158',plain,
    ( ( k2_relat_1 @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('159',plain,(
    v1_relat_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('160',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('161',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['157','158','159','160'])).

thf('162',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['154','161'])).

thf('163',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['10','152'])).

thf('164',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['162','163'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('165',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k2_zfmisc_1 @ X31 @ X32 )
        = k1_xboole_0 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('166',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X32 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('168',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('169',plain,(
    ! [X32: $i] :
      ( ( k2_zfmisc_1 @ o_0_0_xboole_0 @ X32 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['166','167','168'])).

thf('170',plain,(
    ~ ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['153','164','169'])).

thf('171',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( sk_B != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('172',plain,(
    sk_B = o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['162','163'])).

thf('173',plain,
    ( ( sk_C = o_0_0_xboole_0 )
    | ( o_0_0_xboole_0 != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    sk_C = o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( k4_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('176',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['170','174','175','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xiIWSU9nS0
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:10:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 651 iterations in 0.200s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.65  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.65  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.45/0.65  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.65  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.65  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.65  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.45/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.65  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.45/0.65  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.65  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.45/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.65  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.65  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.45/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.65  thf(t31_funct_2, conjecture,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.65         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.65         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.65           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.65           ( m1_subset_1 @
% 0.45/0.65             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.65        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.45/0.65            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.45/0.65          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.45/0.65            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.45/0.65              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.45/0.65              ( m1_subset_1 @
% 0.45/0.65                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.45/0.65        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 0.45/0.65        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.65             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.65               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(cc1_relset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( v1_relat_1 @ C ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.45/0.65         ((v1_relat_1 @ X62)
% 0.45/0.65          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64))))),
% 0.45/0.65      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.65  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(d9_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.65       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X49 : $i]:
% 0.45/0.65         (~ (v2_funct_1 @ X49)
% 0.45/0.65          | ((k2_funct_1 @ X49) = (k4_relat_1 @ X49))
% 0.45/0.65          | ~ (v1_funct_1 @ X49)
% 0.45/0.65          | ~ (v1_relat_1 @ X49))),
% 0.45/0.65      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ sk_C)
% 0.45/0.65        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.45/0.65        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('8', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('9', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      ((~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.65           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 0.45/0.65         <= (~
% 0.45/0.65             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.65               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 0.45/0.65      inference('demod', [status(thm)], ['1', '9'])).
% 0.45/0.65  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.65      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.65  thf(fc6_funct_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.45/0.65       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.65         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.45/0.65         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X51 : $i]:
% 0.45/0.65         ((v1_funct_1 @ (k2_funct_1 @ X51))
% 0.45/0.65          | ~ (v2_funct_1 @ X51)
% 0.45/0.65          | ~ (v1_funct_1 @ X51)
% 0.45/0.65          | ~ (v1_relat_1 @ X51))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.45/0.65         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C) | ~ (v2_funct_1 @ sk_C)))
% 0.45/0.65         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('16', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.45/0.65      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.45/0.65  thf('18', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['11', '17'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.45/0.65         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.65      inference('split', [status(esa)], ['0'])).
% 0.45/0.65  thf('20', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.65  thf(d1_funct_2, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.65       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.65           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.65             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.65         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.65             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_1, axiom,
% 0.45/0.65    (![B:$i,A:$i]:
% 0.45/0.65     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.65       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X78 : $i, X79 : $i]:
% 0.45/0.65         ((zip_tseitin_0 @ X78 @ X79) | ((X78) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.66  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.45/0.66  thf('22', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X78 : $i, X79 : $i]:
% 0.45/0.66         ((zip_tseitin_0 @ X78 @ X79) | ((X78) = (o_0_0_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.66  thf(zf_stmt_3, axiom,
% 0.45/0.66    (![C:$i,B:$i,A:$i]:
% 0.45/0.66     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.66       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.66  thf(zf_stmt_5, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.66         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.66           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.66  thf('25', plain,
% 0.45/0.66      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.45/0.66         (~ (zip_tseitin_0 @ X83 @ X84)
% 0.45/0.66          | (zip_tseitin_1 @ X85 @ X83 @ X84)
% 0.45/0.66          | ~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X83))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.66  thf('26', plain,
% 0.45/0.66      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      ((((sk_B) = (o_0_0_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.45/0.66      inference('sup-', [status(thm)], ['23', '26'])).
% 0.45/0.66  thf('28', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('29', plain,
% 0.45/0.66      (![X80 : $i, X81 : $i, X82 : $i]:
% 0.45/0.66         (~ (v1_funct_2 @ X82 @ X80 @ X81)
% 0.45/0.66          | ((X80) = (k1_relset_1 @ X80 @ X81 @ X82))
% 0.45/0.66          | ~ (zip_tseitin_1 @ X82 @ X81 @ X80))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.66  thf('30', plain,
% 0.45/0.66      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.45/0.66        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.45/0.66         (((k1_relset_1 @ X66 @ X67 @ X65) = (k1_relat_1 @ X65))
% 0.45/0.66          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.66  thf('33', plain,
% 0.45/0.66      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.66  thf('34', plain,
% 0.45/0.66      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.45/0.66      inference('demod', [status(thm)], ['30', '33'])).
% 0.45/0.66  thf('35', plain,
% 0.45/0.66      ((((sk_B) = (o_0_0_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '34'])).
% 0.45/0.66  thf('36', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.66  thf(t65_funct_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.45/0.66  thf('37', plain,
% 0.45/0.66      (![X61 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X61)
% 0.45/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X61)) = (X61))
% 0.45/0.66          | ~ (v1_funct_1 @ X61)
% 0.45/0.66          | ~ (v1_relat_1 @ X61))),
% 0.45/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.45/0.66  thf('38', plain,
% 0.45/0.66      ((((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup+', [status(thm)], ['36', '37'])).
% 0.45/0.66  thf('39', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.66  thf('40', plain,
% 0.45/0.66      (![X51 : $i]:
% 0.45/0.66         ((v1_relat_1 @ (k2_funct_1 @ X51))
% 0.45/0.66          | ~ (v2_funct_1 @ X51)
% 0.45/0.66          | ~ (v1_funct_1 @ X51)
% 0.45/0.66          | ~ (v1_relat_1 @ X51))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.66  thf('41', plain,
% 0.45/0.66      (((v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup+', [status(thm)], ['39', '40'])).
% 0.45/0.66  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf('43', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('44', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('45', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.45/0.66  thf('46', plain,
% 0.45/0.66      (![X49 : $i]:
% 0.45/0.66         (~ (v2_funct_1 @ X49)
% 0.45/0.66          | ((k2_funct_1 @ X49) = (k4_relat_1 @ X49))
% 0.45/0.66          | ~ (v1_funct_1 @ X49)
% 0.45/0.66          | ~ (v1_relat_1 @ X49))),
% 0.45/0.66      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.45/0.66  thf('47', plain,
% 0.45/0.66      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.66        | ((k2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.66            = (k4_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.45/0.66        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.66  thf('48', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.66  thf('49', plain,
% 0.45/0.66      (![X51 : $i]:
% 0.45/0.66         ((v1_funct_1 @ (k2_funct_1 @ X51))
% 0.45/0.66          | ~ (v2_funct_1 @ X51)
% 0.45/0.66          | ~ (v1_funct_1 @ X51)
% 0.45/0.66          | ~ (v1_relat_1 @ X51))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.66  thf('50', plain,
% 0.45/0.66      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup+', [status(thm)], ['48', '49'])).
% 0.45/0.66  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf('52', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('53', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('54', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.45/0.66  thf('55', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.66  thf('56', plain,
% 0.45/0.66      (![X51 : $i]:
% 0.45/0.66         ((v2_funct_1 @ (k2_funct_1 @ X51))
% 0.45/0.66          | ~ (v2_funct_1 @ X51)
% 0.45/0.66          | ~ (v1_funct_1 @ X51)
% 0.45/0.66          | ~ (v1_relat_1 @ X51))),
% 0.45/0.66      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.45/0.66  thf('57', plain,
% 0.45/0.66      (((v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.45/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.45/0.66      inference('sup+', [status(thm)], ['55', '56'])).
% 0.45/0.66  thf('58', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('60', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('61', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.45/0.66  thf('62', plain,
% 0.45/0.66      (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (k4_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.45/0.66      inference('demod', [status(thm)], ['47', '54', '61'])).
% 0.45/0.66  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf('64', plain, ((v1_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('65', plain, ((v2_funct_1 @ sk_C)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('66', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '62', '63', '64', '65'])).
% 0.45/0.66  thf(t37_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.45/0.66         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.45/0.66  thf('67', plain,
% 0.45/0.66      (![X46 : $i]:
% 0.45/0.66         (((k1_relat_1 @ X46) = (k2_relat_1 @ (k4_relat_1 @ X46)))
% 0.45/0.66          | ~ (v1_relat_1 @ X46))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.45/0.66  thf('68', plain,
% 0.45/0.66      ((((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['66', '67'])).
% 0.45/0.66  thf('69', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.45/0.66  thf('70', plain,
% 0.45/0.66      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.66  thf('71', plain,
% 0.45/0.66      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.66  thf('72', plain,
% 0.45/0.66      (![X68 : $i, X69 : $i, X70 : $i]:
% 0.45/0.66         (((k2_relset_1 @ X69 @ X70 @ X68) = (k2_relat_1 @ X68))
% 0.45/0.66          | ~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X70))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.66  thf('73', plain,
% 0.45/0.66      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.45/0.66      inference('sup-', [status(thm)], ['71', '72'])).
% 0.45/0.66  thf('74', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('75', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['73', '74'])).
% 0.45/0.66  thf('76', plain, (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['70', '75'])).
% 0.45/0.66  thf(t3_funct_2, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.66       ( ( v1_funct_1 @ A ) & 
% 0.45/0.66         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.45/0.66         ( m1_subset_1 @
% 0.45/0.66           A @ 
% 0.45/0.66           ( k1_zfmisc_1 @
% 0.45/0.66             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.45/0.66  thf('77', plain,
% 0.45/0.66      (![X102 : $i]:
% 0.45/0.66         ((v1_funct_2 @ X102 @ (k1_relat_1 @ X102) @ (k2_relat_1 @ X102))
% 0.45/0.66          | ~ (v1_funct_1 @ X102)
% 0.45/0.66          | ~ (v1_relat_1 @ X102))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.45/0.66  thf('78', plain,
% 0.45/0.66      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ 
% 0.45/0.66         (k2_relat_1 @ (k4_relat_1 @ sk_C)))
% 0.45/0.66        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.66        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['76', '77'])).
% 0.45/0.66  thf('79', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '62', '63', '64', '65'])).
% 0.45/0.66  thf('80', plain,
% 0.45/0.66      (![X46 : $i]:
% 0.45/0.66         (((k2_relat_1 @ X46) = (k1_relat_1 @ (k4_relat_1 @ X46)))
% 0.45/0.66          | ~ (v1_relat_1 @ X46))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.45/0.66  thf('81', plain,
% 0.45/0.66      ((((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))
% 0.45/0.66        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['79', '80'])).
% 0.45/0.66  thf('82', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.45/0.66  thf('83', plain,
% 0.45/0.66      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.66  thf('84', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.45/0.66  thf('85', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.45/0.66  thf('86', plain,
% 0.45/0.66      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ (k1_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['78', '83', '84', '85'])).
% 0.45/0.66  thf('87', plain,
% 0.45/0.66      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A)
% 0.45/0.66        | ((sk_B) = (o_0_0_xboole_0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['35', '86'])).
% 0.45/0.66  thf('88', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.45/0.66  thf('89', plain,
% 0.45/0.66      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 0.45/0.66         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('90', plain,
% 0.45/0.66      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ sk_B @ sk_A))
% 0.45/0.66         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['88', '89'])).
% 0.45/0.66  thf('91', plain,
% 0.45/0.66      ((((sk_B) = (o_0_0_xboole_0)))
% 0.45/0.66         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['87', '90'])).
% 0.45/0.66  thf('92', plain,
% 0.45/0.66      ((~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ o_0_0_xboole_0 @ sk_A))
% 0.45/0.66         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['19', '20', '91'])).
% 0.45/0.66  thf('93', plain,
% 0.45/0.66      ((((sk_B) = (o_0_0_xboole_0)))
% 0.45/0.66         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['87', '90'])).
% 0.45/0.66  thf('94', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '62', '63', '64', '65'])).
% 0.45/0.66  thf('95', plain,
% 0.45/0.66      (![X46 : $i]:
% 0.45/0.66         (((k1_relat_1 @ X46) = (k2_relat_1 @ (k4_relat_1 @ X46)))
% 0.45/0.66          | ~ (v1_relat_1 @ X46))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.45/0.66  thf(t64_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.66           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.66         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.66  thf('96', plain,
% 0.45/0.66      (![X47 : $i]:
% 0.45/0.66         (((k2_relat_1 @ X47) != (k1_xboole_0))
% 0.45/0.66          | ((X47) = (k1_xboole_0))
% 0.45/0.66          | ~ (v1_relat_1 @ X47))),
% 0.45/0.66      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.45/0.66  thf('97', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('98', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('99', plain,
% 0.45/0.66      (![X47 : $i]:
% 0.45/0.66         (((k2_relat_1 @ X47) != (o_0_0_xboole_0))
% 0.45/0.66          | ((X47) = (o_0_0_xboole_0))
% 0.45/0.66          | ~ (v1_relat_1 @ X47))),
% 0.45/0.66      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.45/0.66  thf('100', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k1_relat_1 @ X0) != (o_0_0_xboole_0))
% 0.45/0.66          | ~ (v1_relat_1 @ X0)
% 0.45/0.66          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.45/0.66          | ((k4_relat_1 @ X0) = (o_0_0_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['95', '99'])).
% 0.45/0.66  thf('101', plain,
% 0.45/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.45/0.66        | ((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (o_0_0_xboole_0))
% 0.45/0.66        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.66        | ((k1_relat_1 @ (k4_relat_1 @ sk_C)) != (o_0_0_xboole_0)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['94', '100'])).
% 0.45/0.66  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.45/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf('103', plain, (((k4_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['38', '62', '63', '64', '65'])).
% 0.45/0.66  thf('104', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.45/0.66  thf('105', plain,
% 0.45/0.66      (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (k2_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.66  thf('106', plain,
% 0.45/0.66      ((((sk_C) = (o_0_0_xboole_0)) | ((k2_relat_1 @ sk_C) != (o_0_0_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.45/0.66  thf('107', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.45/0.66      inference('sup+', [status(thm)], ['73', '74'])).
% 0.45/0.66  thf('108', plain,
% 0.45/0.66      ((((sk_C) = (o_0_0_xboole_0)) | ((sk_B) != (o_0_0_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['106', '107'])).
% 0.45/0.66  thf('109', plain,
% 0.45/0.66      (((((o_0_0_xboole_0) != (o_0_0_xboole_0)) | ((sk_C) = (o_0_0_xboole_0))))
% 0.45/0.66         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['93', '108'])).
% 0.45/0.66  thf('110', plain,
% 0.45/0.66      ((((sk_C) = (o_0_0_xboole_0)))
% 0.45/0.66         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 0.45/0.66      inference('simplify', [status(thm)], ['109'])).
% 0.45/0.66  thf(t66_relat_1, axiom, (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.45/0.66  thf('111', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t66_relat_1])).
% 0.45/0.66  thf('112', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('113', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('114', plain, (((k4_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.45/0.66  thf(dt_k1_subset_1, axiom,
% 0.45/0.66    (![A:$i]: ( m1_subset_1 @ ( k1_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.66  thf('115', plain,
% 0.45/0.66      (![X38 : $i]: (m1_subset_1 @ (k1_subset_1 @ X38) @ (k1_zfmisc_1 @ X38))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k1_subset_1])).
% 0.45/0.66  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('116', plain, (![X37 : $i]: ((k1_subset_1 @ X37) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.45/0.66  thf('117', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('118', plain, (![X37 : $i]: ((k1_subset_1 @ X37) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['116', '117'])).
% 0.45/0.66  thf('119', plain,
% 0.45/0.66      (![X38 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.45/0.66      inference('demod', [status(thm)], ['115', '118'])).
% 0.45/0.66  thf('120', plain,
% 0.45/0.66      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.45/0.66         (((k1_relset_1 @ X66 @ X67 @ X65) = (k1_relat_1 @ X65))
% 0.45/0.66          | ~ (m1_subset_1 @ X65 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X66 @ X67))))),
% 0.45/0.66      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.66  thf('121', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relset_1 @ X1 @ X0 @ o_0_0_xboole_0)
% 0.45/0.66           = (k1_relat_1 @ o_0_0_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['119', '120'])).
% 0.45/0.66  thf(t150_relat_1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('122', plain,
% 0.45/0.66      (![X42 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X42) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t150_relat_1])).
% 0.45/0.66  thf('123', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('124', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('125', plain,
% 0.45/0.66      (![X42 : $i]: ((k9_relat_1 @ o_0_0_xboole_0 @ X42) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['122', '123', '124'])).
% 0.45/0.66  thf(t146_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.45/0.66  thf('126', plain,
% 0.45/0.66      (![X41 : $i]:
% 0.45/0.66         (((k9_relat_1 @ X41 @ (k1_relat_1 @ X41)) = (k2_relat_1 @ X41))
% 0.45/0.66          | ~ (v1_relat_1 @ X41))),
% 0.45/0.66      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.45/0.66  thf('127', plain,
% 0.45/0.66      ((((o_0_0_xboole_0) = (k2_relat_1 @ o_0_0_xboole_0))
% 0.45/0.66        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['125', '126'])).
% 0.45/0.66  thf('128', plain, (((k4_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.45/0.66  thf('129', plain,
% 0.45/0.66      (![X46 : $i]:
% 0.45/0.66         (((k2_relat_1 @ X46) = (k1_relat_1 @ (k4_relat_1 @ X46)))
% 0.45/0.66          | ~ (v1_relat_1 @ X46))),
% 0.45/0.66      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.45/0.66  thf('130', plain,
% 0.45/0.66      ((((k2_relat_1 @ o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))
% 0.45/0.66        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.45/0.66      inference('sup+', [status(thm)], ['128', '129'])).
% 0.45/0.66  thf('131', plain,
% 0.45/0.66      (![X38 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.45/0.66      inference('demod', [status(thm)], ['115', '118'])).
% 0.45/0.66  thf('132', plain,
% 0.45/0.66      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.45/0.66         ((v1_relat_1 @ X62)
% 0.45/0.66          | ~ (m1_subset_1 @ X62 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X64))))),
% 0.45/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.45/0.66  thf('133', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['131', '132'])).
% 0.45/0.66  thf('134', plain,
% 0.45/0.66      (((k2_relat_1 @ o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['130', '133'])).
% 0.45/0.66  thf('135', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['131', '132'])).
% 0.45/0.66  thf('136', plain, (((o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['127', '134', '135'])).
% 0.45/0.66  thf('137', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((k1_relset_1 @ X1 @ X0 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['121', '136'])).
% 0.45/0.66  thf('138', plain,
% 0.45/0.66      (![X80 : $i, X81 : $i, X82 : $i]:
% 0.45/0.66         (((X80) != (k1_relset_1 @ X80 @ X81 @ X82))
% 0.45/0.66          | (v1_funct_2 @ X82 @ X80 @ X81)
% 0.45/0.66          | ~ (zip_tseitin_1 @ X82 @ X81 @ X80))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.66  thf('139', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((X1) != (o_0_0_xboole_0))
% 0.45/0.66          | ~ (zip_tseitin_1 @ o_0_0_xboole_0 @ X0 @ X1)
% 0.45/0.66          | (v1_funct_2 @ o_0_0_xboole_0 @ X1 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['137', '138'])).
% 0.45/0.66  thf('140', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v1_funct_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.45/0.66          | ~ (zip_tseitin_1 @ o_0_0_xboole_0 @ X0 @ o_0_0_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['139'])).
% 0.45/0.66  thf('141', plain,
% 0.45/0.66      (![X78 : $i, X79 : $i]:
% 0.45/0.66         ((zip_tseitin_0 @ X78 @ X79) | ((X79) != (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.66  thf('142', plain, (![X78 : $i]: (zip_tseitin_0 @ X78 @ k1_xboole_0)),
% 0.45/0.66      inference('simplify', [status(thm)], ['141'])).
% 0.45/0.66  thf('143', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('144', plain, (![X78 : $i]: (zip_tseitin_0 @ X78 @ o_0_0_xboole_0)),
% 0.45/0.66      inference('demod', [status(thm)], ['142', '143'])).
% 0.45/0.66  thf('145', plain,
% 0.45/0.66      (![X38 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.45/0.66      inference('demod', [status(thm)], ['115', '118'])).
% 0.45/0.66  thf('146', plain,
% 0.45/0.66      (![X83 : $i, X84 : $i, X85 : $i]:
% 0.45/0.66         (~ (zip_tseitin_0 @ X83 @ X84)
% 0.45/0.66          | (zip_tseitin_1 @ X85 @ X83 @ X84)
% 0.45/0.66          | ~ (m1_subset_1 @ X85 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X83))))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.66  thf('147', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((zip_tseitin_1 @ o_0_0_xboole_0 @ X0 @ X1)
% 0.45/0.66          | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.45/0.66      inference('sup-', [status(thm)], ['145', '146'])).
% 0.45/0.66  thf('148', plain,
% 0.45/0.66      (![X0 : $i]: (zip_tseitin_1 @ o_0_0_xboole_0 @ X0 @ o_0_0_xboole_0)),
% 0.45/0.66      inference('sup-', [status(thm)], ['144', '147'])).
% 0.45/0.66  thf('149', plain,
% 0.45/0.66      (![X0 : $i]: (v1_funct_2 @ o_0_0_xboole_0 @ o_0_0_xboole_0 @ X0)),
% 0.45/0.66      inference('simplify_reflect+', [status(thm)], ['140', '148'])).
% 0.45/0.66  thf('150', plain, (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 0.45/0.66      inference('demod', [status(thm)], ['92', '110', '114', '149'])).
% 0.45/0.66  thf('151', plain,
% 0.45/0.66      (~
% 0.45/0.66       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 0.45/0.66       ~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 0.45/0.66       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.45/0.66      inference('split', [status(esa)], ['0'])).
% 0.45/0.66  thf('152', plain,
% 0.45/0.66      (~
% 0.45/0.66       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 0.45/0.66      inference('sat_resolution*', [status(thm)], ['18', '150', '151'])).
% 0.45/0.66  thf('153', plain,
% 0.45/0.66      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['10', '152'])).
% 0.45/0.66  thf('154', plain,
% 0.45/0.66      ((((sk_B) = (o_0_0_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['27', '34'])).
% 0.45/0.66  thf('155', plain, (((k1_relat_1 @ (k4_relat_1 @ sk_C)) = (sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['70', '75'])).
% 0.45/0.66  thf('156', plain,
% 0.45/0.66      (![X102 : $i]:
% 0.45/0.66         ((m1_subset_1 @ X102 @ 
% 0.45/0.66           (k1_zfmisc_1 @ 
% 0.45/0.66            (k2_zfmisc_1 @ (k1_relat_1 @ X102) @ (k2_relat_1 @ X102))))
% 0.45/0.66          | ~ (v1_funct_1 @ X102)
% 0.45/0.66          | ~ (v1_relat_1 @ X102))),
% 0.45/0.66      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.45/0.66  thf('157', plain,
% 0.45/0.66      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.66         (k1_zfmisc_1 @ 
% 0.45/0.66          (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ (k4_relat_1 @ sk_C)))))
% 0.45/0.66        | ~ (v1_relat_1 @ (k4_relat_1 @ sk_C))
% 0.45/0.66        | ~ (v1_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['155', '156'])).
% 0.45/0.66  thf('158', plain,
% 0.45/0.66      (((k2_relat_1 @ (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['81', '82'])).
% 0.45/0.66  thf('159', plain, ((v1_relat_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['41', '42', '43', '44'])).
% 0.45/0.66  thf('160', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.45/0.66      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.45/0.66  thf('161', plain,
% 0.45/0.66      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.66        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ (k1_relat_1 @ sk_C))))),
% 0.45/0.66      inference('demod', [status(thm)], ['157', '158', '159', '160'])).
% 0.45/0.66  thf('162', plain,
% 0.45/0.66      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.66         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.45/0.66        | ((sk_B) = (o_0_0_xboole_0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['154', '161'])).
% 0.45/0.66  thf('163', plain,
% 0.45/0.66      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.45/0.66          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('simpl_trail', [status(thm)], ['10', '152'])).
% 0.45/0.66  thf('164', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('clc', [status(thm)], ['162', '163'])).
% 0.45/0.66  thf(t113_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.66       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.66  thf('165', plain,
% 0.45/0.66      (![X31 : $i, X32 : $i]:
% 0.45/0.66         (((k2_zfmisc_1 @ X31 @ X32) = (k1_xboole_0))
% 0.45/0.66          | ((X31) != (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.45/0.66  thf('166', plain,
% 0.45/0.66      (![X32 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X32) = (k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['165'])).
% 0.45/0.66  thf('167', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('168', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.45/0.66  thf('169', plain,
% 0.45/0.66      (![X32 : $i]: ((k2_zfmisc_1 @ o_0_0_xboole_0 @ X32) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['166', '167', '168'])).
% 0.45/0.66  thf('170', plain,
% 0.45/0.66      (~ (m1_subset_1 @ (k4_relat_1 @ sk_C) @ (k1_zfmisc_1 @ o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['153', '164', '169'])).
% 0.45/0.66  thf('171', plain,
% 0.45/0.66      ((((sk_C) = (o_0_0_xboole_0)) | ((sk_B) != (o_0_0_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['106', '107'])).
% 0.45/0.66  thf('172', plain, (((sk_B) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('clc', [status(thm)], ['162', '163'])).
% 0.45/0.66  thf('173', plain,
% 0.45/0.66      ((((sk_C) = (o_0_0_xboole_0)) | ((o_0_0_xboole_0) != (o_0_0_xboole_0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['171', '172'])).
% 0.45/0.66  thf('174', plain, (((sk_C) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['173'])).
% 0.45/0.66  thf('175', plain, (((k4_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.45/0.66      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.45/0.66  thf('176', plain,
% 0.45/0.66      (![X38 : $i]: (m1_subset_1 @ o_0_0_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.45/0.66      inference('demod', [status(thm)], ['115', '118'])).
% 0.45/0.66  thf('177', plain, ($false),
% 0.45/0.66      inference('demod', [status(thm)], ['170', '174', '175', '176'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
