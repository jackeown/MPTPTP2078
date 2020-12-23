%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eFohyhCVjj

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:46 EST 2020

% Result     : Theorem 4.16s
% Output     : Refutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :  315 (4146 expanded)
%              Number of leaves         :   57 (1211 expanded)
%              Depth                    :   30
%              Number of atoms          : 2829 (103945 expanded)
%              Number of equality atoms :  206 (5260 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t62_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ B ) )
                  & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                    = ( k2_struct_0 @ A ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( ( ( k1_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ B ) )
                    & ( ( k2_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) )
                      = ( k2_struct_0 @ A ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_tops_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('20',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['24','29'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('35',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('40',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','40'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('43',plain,(
    ! [X49: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X49 ) )
      | ~ ( l1_struct_0 @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','48'])).

thf('50',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['19','49'])).

thf('51',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('53',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_partfun1 @ X44 @ X43 )
      | ( ( k1_relat_1 @ X44 )
        = X43 )
      | ~ ( v4_relat_1 @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('54',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('56',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','57'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('60',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('61',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X22 ) @ ( k9_relat_1 @ X22 @ X21 ) )
        = X21 )
      | ~ ( v2_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['58','62'])).

thf('64',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('66',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(t31_funct_2,axiom,(
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

thf('73',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X47 @ X46 @ X45 )
       != X46 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('74',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('77',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['89','94'])).

thf('96',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('99',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['74','75','88','102','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('107',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19
        = ( k7_relat_1 @ X19 @ X20 ) )
      | ~ ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('109',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('111',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('112',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','112'])).

thf('114',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k9_relat_1 @ X17 @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('115',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('117',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('121',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['63','117','118','119','120'])).

thf('122',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['122'])).

thf('124',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['41','48'])).

thf('125',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_partfun1 @ X44 @ X43 )
      | ( ( k1_relat_1 @ X44 )
        = X43 )
      | ~ ( v4_relat_1 @ X44 @ X43 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('126',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['11','12'])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('130',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127','130'])).

thf('132',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['126','127','130'])).

thf('133',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('135',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('136',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('137',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_relset_1 @ X51 @ X50 @ X52 )
       != X50 )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_tops_2 @ X51 @ X50 @ X52 )
        = ( k2_funct_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('138',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('141',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('142',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('145',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('146',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('148',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','142','143','148'])).

thf('150',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','149'])).

thf('151',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('152',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['150','151','152'])).

thf('154',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('156',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('157',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X47 @ X46 @ X45 )
       != X46 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('158',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('161',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('162',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['158','159','160','161','162'])).

thf('164',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['155','163'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('166',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['164','165','166'])).

thf('168',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('170',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('172',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','131','132','154','170','171'])).

thf('173',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('174',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('175',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('176',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['174','176'])).

thf('178',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('179',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('180',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('182',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['180','181'])).

thf('183',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ k1_xboole_0 )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['177','182'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('184',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('185',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('186',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 )
      | ( sk_C = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['183','188'])).

thf('190',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

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

thf('191',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('192',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['189','192'])).

thf('194',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('195',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('196',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( v2_funct_1 @ X45 )
      | ( ( k2_relset_1 @ X47 @ X46 @ X45 )
       != X46 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X45 ) @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X47 @ X46 )
      | ~ ( v1_funct_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('197',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('200',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['197','198','199','200'])).

thf('202',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('203',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['194','203'])).

thf('205',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('206',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['204','205','206'])).

thf('208',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('210',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( u1_struct_0 @ sk_B )
      = ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['193','210'])).

thf('212',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('213',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k2_relset_1 @ X51 @ X50 @ X52 )
       != X50 )
      | ~ ( v2_funct_1 @ X52 )
      | ( ( k2_tops_2 @ X51 @ X50 @ X52 )
        = ( k2_funct_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X50 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X51 @ X50 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('214',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('217',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('219',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['214','215','216','217','218'])).

thf('220',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('222',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('223',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('224',plain,(
    ! [X48: $i] :
      ( ( ( k2_struct_0 @ X48 )
        = ( u1_struct_0 @ X48 ) )
      | ~ ( l1_struct_0 @ X48 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('225',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['122'])).

thf('226',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['224','225'])).

thf('227',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['226','227'])).

thf('229',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['223','228'])).

thf('230',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['222','231'])).

thf('233',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['221','234'])).

thf('236',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('237',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('239',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('240',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['220','240'])).

thf('242',plain,
    ( ( ( ( u1_struct_0 @ sk_B )
       != ( k2_relat_1 @ sk_C ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['211','241'])).

thf('243',plain,
    ( ( ( ( k2_struct_0 @ sk_B )
       != ( k2_relat_1 @ sk_C ) )
      | ~ ( l1_struct_0 @ sk_B )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['173','242'])).

thf('244',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('245',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['243','244','245'])).

thf('247',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['246'])).

thf('248',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('249',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['247','248'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('250',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('251',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('252',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['249','250','251'])).

thf('253',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['122'])).

thf('254',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['252','253'])).

thf('255',plain,(
    ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['172','254'])).

thf('256',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['121','255'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eFohyhCVjj
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:04 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 4.16/4.39  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.16/4.39  % Solved by: fo/fo7.sh
% 4.16/4.39  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.16/4.39  % done 3716 iterations in 3.929s
% 4.16/4.39  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.16/4.39  % SZS output start Refutation
% 4.16/4.39  thf(sk_C_type, type, sk_C: $i).
% 4.16/4.39  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 4.16/4.39  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.16/4.39  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 4.16/4.39  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 4.16/4.39  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.16/4.39  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.16/4.39  thf(sk_A_type, type, sk_A: $i).
% 4.16/4.39  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.16/4.39  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.16/4.39  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.16/4.39  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 4.16/4.39  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.16/4.39  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 4.16/4.39  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.16/4.39  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.16/4.39  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.16/4.39  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 4.16/4.39  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 4.16/4.39  thf(sk_B_type, type, sk_B: $i).
% 4.16/4.39  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 4.16/4.39  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 4.16/4.39  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.16/4.39  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 4.16/4.39  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 4.16/4.39  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.16/4.39  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 4.16/4.39  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.16/4.39  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 4.16/4.39  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 4.16/4.39  thf(d3_struct_0, axiom,
% 4.16/4.39    (![A:$i]:
% 4.16/4.39     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.16/4.39  thf('0', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf(t62_tops_2, conjecture,
% 4.16/4.39    (![A:$i]:
% 4.16/4.39     ( ( l1_struct_0 @ A ) =>
% 4.16/4.39       ( ![B:$i]:
% 4.16/4.39         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 4.16/4.39           ( ![C:$i]:
% 4.16/4.39             ( ( ( v1_funct_1 @ C ) & 
% 4.16/4.39                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.16/4.39                 ( m1_subset_1 @
% 4.16/4.39                   C @ 
% 4.16/4.39                   ( k1_zfmisc_1 @
% 4.16/4.39                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.16/4.39               ( ( ( ( k2_relset_1 @
% 4.16/4.39                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.16/4.39                     ( k2_struct_0 @ B ) ) & 
% 4.16/4.39                   ( v2_funct_1 @ C ) ) =>
% 4.16/4.39                 ( ( ( k1_relset_1 @
% 4.16/4.39                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.16/4.39                       ( k2_tops_2 @
% 4.16/4.39                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 4.16/4.39                     ( k2_struct_0 @ B ) ) & 
% 4.16/4.39                   ( ( k2_relset_1 @
% 4.16/4.39                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.16/4.39                       ( k2_tops_2 @
% 4.16/4.39                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 4.16/4.39                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 4.16/4.39  thf(zf_stmt_0, negated_conjecture,
% 4.16/4.39    (~( ![A:$i]:
% 4.16/4.39        ( ( l1_struct_0 @ A ) =>
% 4.16/4.39          ( ![B:$i]:
% 4.16/4.39            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 4.16/4.39              ( ![C:$i]:
% 4.16/4.39                ( ( ( v1_funct_1 @ C ) & 
% 4.16/4.39                    ( v1_funct_2 @
% 4.16/4.39                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 4.16/4.39                    ( m1_subset_1 @
% 4.16/4.39                      C @ 
% 4.16/4.39                      ( k1_zfmisc_1 @
% 4.16/4.39                        ( k2_zfmisc_1 @
% 4.16/4.39                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 4.16/4.39                  ( ( ( ( k2_relset_1 @
% 4.16/4.39                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 4.16/4.39                        ( k2_struct_0 @ B ) ) & 
% 4.16/4.39                      ( v2_funct_1 @ C ) ) =>
% 4.16/4.39                    ( ( ( k1_relset_1 @
% 4.16/4.39                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.16/4.39                          ( k2_tops_2 @
% 4.16/4.39                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 4.16/4.39                        ( k2_struct_0 @ B ) ) & 
% 4.16/4.39                      ( ( k2_relset_1 @
% 4.16/4.39                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 4.16/4.39                          ( k2_tops_2 @
% 4.16/4.39                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 4.16/4.39                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 4.16/4.39    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 4.16/4.39  thf('1', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('2', plain,
% 4.16/4.39      (((m1_subset_1 @ sk_C @ 
% 4.16/4.39         (k1_zfmisc_1 @ 
% 4.16/4.39          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_A))),
% 4.16/4.39      inference('sup+', [status(thm)], ['0', '1'])).
% 4.16/4.39  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('4', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['2', '3'])).
% 4.16/4.39  thf(cc2_relset_1, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.39       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 4.16/4.39  thf('5', plain,
% 4.16/4.39      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.16/4.39         ((v4_relat_1 @ X26 @ X27)
% 4.16/4.39          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.16/4.39      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.16/4.39  thf('6', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('sup-', [status(thm)], ['4', '5'])).
% 4.16/4.39  thf(t209_relat_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.16/4.39       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 4.16/4.39  thf('7', plain,
% 4.16/4.39      (![X19 : $i, X20 : $i]:
% 4.16/4.39         (((X19) = (k7_relat_1 @ X19 @ X20))
% 4.16/4.39          | ~ (v4_relat_1 @ X19 @ X20)
% 4.16/4.39          | ~ (v1_relat_1 @ X19))),
% 4.16/4.39      inference('cnf', [status(esa)], [t209_relat_1])).
% 4.16/4.39  thf('8', plain,
% 4.16/4.39      ((~ (v1_relat_1 @ sk_C)
% 4.16/4.39        | ((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['6', '7'])).
% 4.16/4.39  thf('9', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf(cc2_relat_1, axiom,
% 4.16/4.39    (![A:$i]:
% 4.16/4.39     ( ( v1_relat_1 @ A ) =>
% 4.16/4.39       ( ![B:$i]:
% 4.16/4.39         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 4.16/4.39  thf('10', plain,
% 4.16/4.39      (![X13 : $i, X14 : $i]:
% 4.16/4.39         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 4.16/4.39          | (v1_relat_1 @ X13)
% 4.16/4.39          | ~ (v1_relat_1 @ X14))),
% 4.16/4.39      inference('cnf', [status(esa)], [cc2_relat_1])).
% 4.16/4.39  thf('11', plain,
% 4.16/4.39      ((~ (v1_relat_1 @ 
% 4.16/4.39           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 4.16/4.39        | (v1_relat_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['9', '10'])).
% 4.16/4.39  thf(fc6_relat_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 4.16/4.39  thf('12', plain,
% 4.16/4.39      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X15 @ X16))),
% 4.16/4.39      inference('cnf', [status(esa)], [fc6_relat_1])).
% 4.16/4.39  thf('13', plain, ((v1_relat_1 @ sk_C)),
% 4.16/4.39      inference('demod', [status(thm)], ['11', '12'])).
% 4.16/4.39  thf('14', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 4.16/4.39      inference('demod', [status(thm)], ['8', '13'])).
% 4.16/4.39  thf('15', plain, ((v1_relat_1 @ sk_C)),
% 4.16/4.39      inference('demod', [status(thm)], ['11', '12'])).
% 4.16/4.39  thf(t148_relat_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( v1_relat_1 @ B ) =>
% 4.16/4.39       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 4.16/4.39  thf('16', plain,
% 4.16/4.39      (![X17 : $i, X18 : $i]:
% 4.16/4.39         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 4.16/4.39          | ~ (v1_relat_1 @ X17))),
% 4.16/4.39      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.16/4.39  thf('17', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 4.16/4.39      inference('sup-', [status(thm)], ['15', '16'])).
% 4.16/4.39  thf('18', plain,
% 4.16/4.39      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['14', '17'])).
% 4.16/4.39  thf('19', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('20', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('21', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('22', plain,
% 4.16/4.39      (((m1_subset_1 @ sk_C @ 
% 4.16/4.39         (k1_zfmisc_1 @ 
% 4.16/4.39          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['20', '21'])).
% 4.16/4.39  thf('23', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('24', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['22', '23'])).
% 4.16/4.39  thf('25', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf(redefinition_k2_relset_1, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.39       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 4.16/4.39  thf('26', plain,
% 4.16/4.39      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.16/4.39         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 4.16/4.39          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 4.16/4.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.16/4.39  thf('27', plain,
% 4.16/4.39      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['25', '26'])).
% 4.16/4.39  thf('28', plain,
% 4.16/4.39      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('30', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.16/4.39      inference('demod', [status(thm)], ['24', '29'])).
% 4.16/4.39  thf(cc5_funct_2, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( ~( v1_xboole_0 @ B ) ) =>
% 4.16/4.39       ( ![C:$i]:
% 4.16/4.39         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.39           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 4.16/4.39             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 4.16/4.39  thf('31', plain,
% 4.16/4.39      (![X32 : $i, X33 : $i, X34 : $i]:
% 4.16/4.39         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 4.16/4.39          | (v1_partfun1 @ X32 @ X33)
% 4.16/4.39          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 4.16/4.39          | ~ (v1_funct_1 @ X32)
% 4.16/4.39          | (v1_xboole_0 @ X34))),
% 4.16/4.39      inference('cnf', [status(esa)], [cc5_funct_2])).
% 4.16/4.39  thf('32', plain,
% 4.16/4.39      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 4.16/4.39        | ~ (v1_funct_1 @ sk_C)
% 4.16/4.39        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 4.16/4.39        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['30', '31'])).
% 4.16/4.39  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('34', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('35', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('36', plain,
% 4.16/4.39      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['34', '35'])).
% 4.16/4.39  thf('37', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('38', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['36', '37'])).
% 4.16/4.39  thf('39', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('40', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['38', '39'])).
% 4.16/4.39  thf('41', plain,
% 4.16/4.39      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 4.16/4.39        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 4.16/4.39      inference('demod', [status(thm)], ['32', '33', '40'])).
% 4.16/4.39  thf('42', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf(fc5_struct_0, axiom,
% 4.16/4.39    (![A:$i]:
% 4.16/4.39     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.16/4.39       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 4.16/4.39  thf('43', plain,
% 4.16/4.39      (![X49 : $i]:
% 4.16/4.39         (~ (v1_xboole_0 @ (k2_struct_0 @ X49))
% 4.16/4.39          | ~ (l1_struct_0 @ X49)
% 4.16/4.39          | (v2_struct_0 @ X49))),
% 4.16/4.39      inference('cnf', [status(esa)], [fc5_struct_0])).
% 4.16/4.39  thf('44', plain,
% 4.16/4.39      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 4.16/4.39        | (v2_struct_0 @ sk_B)
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup-', [status(thm)], ['42', '43'])).
% 4.16/4.39  thf('45', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('46', plain,
% 4.16/4.39      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['44', '45'])).
% 4.16/4.39  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('48', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('clc', [status(thm)], ['46', '47'])).
% 4.16/4.39  thf('49', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 4.16/4.39      inference('clc', [status(thm)], ['41', '48'])).
% 4.16/4.39  thf('50', plain,
% 4.16/4.39      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 4.16/4.39      inference('sup+', [status(thm)], ['19', '49'])).
% 4.16/4.39  thf('51', plain, ((l1_struct_0 @ sk_A)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('52', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['50', '51'])).
% 4.16/4.39  thf(d4_partfun1, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 4.16/4.39       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 4.16/4.39  thf('53', plain,
% 4.16/4.39      (![X43 : $i, X44 : $i]:
% 4.16/4.39         (~ (v1_partfun1 @ X44 @ X43)
% 4.16/4.39          | ((k1_relat_1 @ X44) = (X43))
% 4.16/4.39          | ~ (v4_relat_1 @ X44 @ X43)
% 4.16/4.39          | ~ (v1_relat_1 @ X44))),
% 4.16/4.39      inference('cnf', [status(esa)], [d4_partfun1])).
% 4.16/4.39  thf('54', plain,
% 4.16/4.39      ((~ (v1_relat_1 @ sk_C)
% 4.16/4.39        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 4.16/4.39        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['52', '53'])).
% 4.16/4.39  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 4.16/4.39      inference('demod', [status(thm)], ['11', '12'])).
% 4.16/4.39  thf('56', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('sup-', [status(thm)], ['4', '5'])).
% 4.16/4.39  thf('57', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('58', plain,
% 4.16/4.39      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 4.16/4.39      inference('demod', [status(thm)], ['18', '57'])).
% 4.16/4.39  thf(d10_xboole_0, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.16/4.39  thf('59', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 4.16/4.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.16/4.39  thf('60', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 4.16/4.39      inference('simplify', [status(thm)], ['59'])).
% 4.16/4.39  thf(t177_funct_1, axiom,
% 4.16/4.39    (![A:$i]:
% 4.16/4.39     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 4.16/4.39       ( ![B:$i]:
% 4.16/4.39         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 4.16/4.39           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 4.16/4.39             ( B ) ) ) ) ))).
% 4.16/4.39  thf('61', plain,
% 4.16/4.39      (![X21 : $i, X22 : $i]:
% 4.16/4.39         (~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 4.16/4.39          | ((k9_relat_1 @ (k2_funct_1 @ X22) @ (k9_relat_1 @ X22 @ X21))
% 4.16/4.39              = (X21))
% 4.16/4.39          | ~ (v2_funct_1 @ X22)
% 4.16/4.39          | ~ (v1_funct_1 @ X22)
% 4.16/4.39          | ~ (v1_relat_1 @ X22))),
% 4.16/4.39      inference('cnf', [status(esa)], [t177_funct_1])).
% 4.16/4.39  thf('62', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         (~ (v1_relat_1 @ X0)
% 4.16/4.39          | ~ (v1_funct_1 @ X0)
% 4.16/4.39          | ~ (v2_funct_1 @ X0)
% 4.16/4.39          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 4.16/4.39              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['60', '61'])).
% 4.16/4.39  thf('63', plain,
% 4.16/4.39      ((((k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.16/4.39          = (k1_relat_1 @ sk_C))
% 4.16/4.39        | ~ (v2_funct_1 @ sk_C)
% 4.16/4.39        | ~ (v1_funct_1 @ sk_C)
% 4.16/4.39        | ~ (v1_relat_1 @ sk_C))),
% 4.16/4.39      inference('sup+', [status(thm)], ['58', '62'])).
% 4.16/4.39  thf('64', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('65', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['2', '3'])).
% 4.16/4.39  thf('66', plain,
% 4.16/4.39      (((m1_subset_1 @ sk_C @ 
% 4.16/4.39         (k1_zfmisc_1 @ 
% 4.16/4.39          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['64', '65'])).
% 4.16/4.39  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('68', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['66', '67'])).
% 4.16/4.39  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('70', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 4.16/4.39      inference('demod', [status(thm)], ['68', '69'])).
% 4.16/4.39  thf('71', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('72', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.16/4.39      inference('demod', [status(thm)], ['70', '71'])).
% 4.16/4.39  thf(t31_funct_2, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.16/4.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.16/4.39       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 4.16/4.39         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 4.16/4.39           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 4.16/4.39           ( m1_subset_1 @
% 4.16/4.39             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 4.16/4.39  thf('73', plain,
% 4.16/4.39      (![X45 : $i, X46 : $i, X47 : $i]:
% 4.16/4.39         (~ (v2_funct_1 @ X45)
% 4.16/4.39          | ((k2_relset_1 @ X47 @ X46 @ X45) != (X46))
% 4.16/4.39          | (m1_subset_1 @ (k2_funct_1 @ X45) @ 
% 4.16/4.39             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 4.16/4.39          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 4.16/4.39          | ~ (v1_funct_2 @ X45 @ X47 @ X46)
% 4.16/4.39          | ~ (v1_funct_1 @ X45))),
% 4.16/4.39      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.16/4.39  thf('74', plain,
% 4.16/4.39      ((~ (v1_funct_1 @ sk_C)
% 4.16/4.39        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.16/4.39        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39           (k1_zfmisc_1 @ 
% 4.16/4.39            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 4.16/4.39        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.16/4.39            != (k2_relat_1 @ sk_C))
% 4.16/4.39        | ~ (v2_funct_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['72', '73'])).
% 4.16/4.39  thf('75', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('76', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('77', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('78', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('79', plain,
% 4.16/4.39      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_A))),
% 4.16/4.39      inference('sup+', [status(thm)], ['77', '78'])).
% 4.16/4.39  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('81', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['79', '80'])).
% 4.16/4.39  thf('82', plain,
% 4.16/4.39      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['76', '81'])).
% 4.16/4.39  thf('83', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('84', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['82', '83'])).
% 4.16/4.39  thf('85', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('86', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['84', '85'])).
% 4.16/4.39  thf('87', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('88', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['86', '87'])).
% 4.16/4.39  thf('89', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('90', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('91', plain,
% 4.16/4.39      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('92', plain,
% 4.16/4.39      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39          = (k2_struct_0 @ sk_B))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_A))),
% 4.16/4.39      inference('sup+', [status(thm)], ['90', '91'])).
% 4.16/4.39  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('94', plain,
% 4.16/4.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['92', '93'])).
% 4.16/4.39  thf('95', plain,
% 4.16/4.39      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39          = (k2_struct_0 @ sk_B))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['89', '94'])).
% 4.16/4.39  thf('96', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('97', plain,
% 4.16/4.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['95', '96'])).
% 4.16/4.39  thf('98', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('99', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('100', plain,
% 4.16/4.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.16/4.39         = (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['97', '98', '99'])).
% 4.16/4.39  thf('101', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('102', plain,
% 4.16/4.39      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.16/4.39         = (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['100', '101'])).
% 4.16/4.39  thf('103', plain, ((v2_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('104', plain,
% 4.16/4.39      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39         (k1_zfmisc_1 @ 
% 4.16/4.39          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 4.16/4.39        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.16/4.39      inference('demod', [status(thm)], ['74', '75', '88', '102', '103'])).
% 4.16/4.39  thf('105', plain,
% 4.16/4.39      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.16/4.39      inference('simplify', [status(thm)], ['104'])).
% 4.16/4.39  thf('106', plain,
% 4.16/4.39      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.16/4.39         ((v4_relat_1 @ X26 @ X27)
% 4.16/4.39          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.16/4.39      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.16/4.39  thf('107', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['105', '106'])).
% 4.16/4.39  thf('108', plain,
% 4.16/4.39      (![X19 : $i, X20 : $i]:
% 4.16/4.39         (((X19) = (k7_relat_1 @ X19 @ X20))
% 4.16/4.39          | ~ (v4_relat_1 @ X19 @ X20)
% 4.16/4.39          | ~ (v1_relat_1 @ X19))),
% 4.16/4.39      inference('cnf', [status(esa)], [t209_relat_1])).
% 4.16/4.39  thf('109', plain,
% 4.16/4.39      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 4.16/4.39        | ((k2_funct_1 @ sk_C)
% 4.16/4.39            = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['107', '108'])).
% 4.16/4.39  thf('110', plain,
% 4.16/4.39      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 4.16/4.39      inference('simplify', [status(thm)], ['104'])).
% 4.16/4.39  thf(cc1_relset_1, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.39       ( v1_relat_1 @ C ) ))).
% 4.16/4.39  thf('111', plain,
% 4.16/4.39      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.16/4.39         ((v1_relat_1 @ X23)
% 4.16/4.39          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 4.16/4.39      inference('cnf', [status(esa)], [cc1_relset_1])).
% 4.16/4.39  thf('112', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['110', '111'])).
% 4.16/4.39  thf('113', plain,
% 4.16/4.39      (((k2_funct_1 @ sk_C)
% 4.16/4.39         = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 4.16/4.39      inference('demod', [status(thm)], ['109', '112'])).
% 4.16/4.39  thf('114', plain,
% 4.16/4.39      (![X17 : $i, X18 : $i]:
% 4.16/4.39         (((k2_relat_1 @ (k7_relat_1 @ X17 @ X18)) = (k9_relat_1 @ X17 @ X18))
% 4.16/4.39          | ~ (v1_relat_1 @ X17))),
% 4.16/4.39      inference('cnf', [status(esa)], [t148_relat_1])).
% 4.16/4.39  thf('115', plain,
% 4.16/4.39      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 4.16/4.39          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 4.16/4.39        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.16/4.39      inference('sup+', [status(thm)], ['113', '114'])).
% 4.16/4.39  thf('116', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['110', '111'])).
% 4.16/4.39  thf('117', plain,
% 4.16/4.39      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 4.16/4.39         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 4.16/4.39      inference('demod', [status(thm)], ['115', '116'])).
% 4.16/4.39  thf('118', plain, ((v2_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('119', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('120', plain, ((v1_relat_1 @ sk_C)),
% 4.16/4.39      inference('demod', [status(thm)], ['11', '12'])).
% 4.16/4.39  thf('121', plain,
% 4.16/4.39      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['63', '117', '118', '119', '120'])).
% 4.16/4.39  thf('122', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          != (k2_struct_0 @ sk_B))
% 4.16/4.39        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39            != (k2_struct_0 @ sk_A)))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('123', plain,
% 4.16/4.39      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          != (k2_struct_0 @ sk_A)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_A))))),
% 4.16/4.39      inference('split', [status(esa)], ['122'])).
% 4.16/4.39  thf('124', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 4.16/4.39      inference('clc', [status(thm)], ['41', '48'])).
% 4.16/4.39  thf('125', plain,
% 4.16/4.39      (![X43 : $i, X44 : $i]:
% 4.16/4.39         (~ (v1_partfun1 @ X44 @ X43)
% 4.16/4.39          | ((k1_relat_1 @ X44) = (X43))
% 4.16/4.39          | ~ (v4_relat_1 @ X44 @ X43)
% 4.16/4.39          | ~ (v1_relat_1 @ X44))),
% 4.16/4.39      inference('cnf', [status(esa)], [d4_partfun1])).
% 4.16/4.39  thf('126', plain,
% 4.16/4.39      ((~ (v1_relat_1 @ sk_C)
% 4.16/4.39        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 4.16/4.39        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['124', '125'])).
% 4.16/4.39  thf('127', plain, ((v1_relat_1 @ sk_C)),
% 4.16/4.39      inference('demod', [status(thm)], ['11', '12'])).
% 4.16/4.39  thf('128', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('129', plain,
% 4.16/4.39      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.16/4.39         ((v4_relat_1 @ X26 @ X27)
% 4.16/4.39          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 4.16/4.39      inference('cnf', [status(esa)], [cc2_relset_1])).
% 4.16/4.39  thf('130', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 4.16/4.39      inference('sup-', [status(thm)], ['128', '129'])).
% 4.16/4.39  thf('131', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['126', '127', '130'])).
% 4.16/4.39  thf('132', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['126', '127', '130'])).
% 4.16/4.39  thf('133', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('134', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['2', '3'])).
% 4.16/4.39  thf('135', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('136', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['134', '135'])).
% 4.16/4.39  thf(d4_tops_2, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 4.16/4.39         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 4.16/4.39       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 4.16/4.39         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 4.16/4.39  thf('137', plain,
% 4.16/4.39      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.16/4.39         (((k2_relset_1 @ X51 @ X50 @ X52) != (X50))
% 4.16/4.39          | ~ (v2_funct_1 @ X52)
% 4.16/4.39          | ((k2_tops_2 @ X51 @ X50 @ X52) = (k2_funct_1 @ X52))
% 4.16/4.39          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 4.16/4.39          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 4.16/4.39          | ~ (v1_funct_1 @ X52))),
% 4.16/4.39      inference('cnf', [status(esa)], [d4_tops_2])).
% 4.16/4.39  thf('138', plain,
% 4.16/4.39      ((~ (v1_funct_1 @ sk_C)
% 4.16/4.39        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.16/4.39        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39            = (k2_funct_1 @ sk_C))
% 4.16/4.39        | ~ (v2_funct_1 @ sk_C)
% 4.16/4.39        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39            != (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['136', '137'])).
% 4.16/4.39  thf('139', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('140', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['79', '80'])).
% 4.16/4.39  thf('141', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('142', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['140', '141'])).
% 4.16/4.39  thf('143', plain, ((v2_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('144', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['2', '3'])).
% 4.16/4.39  thf('145', plain,
% 4.16/4.39      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.16/4.39         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 4.16/4.39          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 4.16/4.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.16/4.39  thf('146', plain,
% 4.16/4.39      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['144', '145'])).
% 4.16/4.39  thf('147', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('148', plain,
% 4.16/4.39      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['146', '147'])).
% 4.16/4.39  thf('149', plain,
% 4.16/4.39      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39          = (k2_funct_1 @ sk_C))
% 4.16/4.39        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['138', '139', '142', '143', '148'])).
% 4.16/4.39  thf('150', plain,
% 4.16/4.39      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B)
% 4.16/4.39        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39            = (k2_funct_1 @ sk_C)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['133', '149'])).
% 4.16/4.39  thf('151', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('152', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('153', plain,
% 4.16/4.39      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.16/4.39        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39            = (k2_funct_1 @ sk_C)))),
% 4.16/4.39      inference('demod', [status(thm)], ['150', '151', '152'])).
% 4.16/4.39  thf('154', plain,
% 4.16/4.39      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_funct_1 @ sk_C))),
% 4.16/4.39      inference('simplify', [status(thm)], ['153'])).
% 4.16/4.39  thf('155', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('156', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['134', '135'])).
% 4.16/4.39  thf('157', plain,
% 4.16/4.39      (![X45 : $i, X46 : $i, X47 : $i]:
% 4.16/4.39         (~ (v2_funct_1 @ X45)
% 4.16/4.39          | ((k2_relset_1 @ X47 @ X46 @ X45) != (X46))
% 4.16/4.39          | (m1_subset_1 @ (k2_funct_1 @ X45) @ 
% 4.16/4.39             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 4.16/4.39          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 4.16/4.39          | ~ (v1_funct_2 @ X45 @ X47 @ X46)
% 4.16/4.39          | ~ (v1_funct_1 @ X45))),
% 4.16/4.39      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.16/4.39  thf('158', plain,
% 4.16/4.39      ((~ (v1_funct_1 @ sk_C)
% 4.16/4.39        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.16/4.39        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39           (k1_zfmisc_1 @ 
% 4.16/4.39            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 4.16/4.39        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39            != (u1_struct_0 @ sk_B))
% 4.16/4.39        | ~ (v2_funct_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['156', '157'])).
% 4.16/4.39  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('160', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['140', '141'])).
% 4.16/4.39  thf('161', plain,
% 4.16/4.39      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['146', '147'])).
% 4.16/4.39  thf('162', plain, ((v2_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('163', plain,
% 4.16/4.39      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39         (k1_zfmisc_1 @ 
% 4.16/4.39          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 4.16/4.39        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['158', '159', '160', '161', '162'])).
% 4.16/4.39  thf('164', plain,
% 4.16/4.39      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B)
% 4.16/4.39        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39           (k1_zfmisc_1 @ 
% 4.16/4.39            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['155', '163'])).
% 4.16/4.39  thf('165', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('166', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('167', plain,
% 4.16/4.39      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.16/4.39        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39           (k1_zfmisc_1 @ 
% 4.16/4.39            (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C)))))),
% 4.16/4.39      inference('demod', [status(thm)], ['164', '165', '166'])).
% 4.16/4.39  thf('168', plain,
% 4.16/4.39      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.16/4.39      inference('simplify', [status(thm)], ['167'])).
% 4.16/4.39  thf('169', plain,
% 4.16/4.39      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.16/4.39         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 4.16/4.39          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 4.16/4.39      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 4.16/4.39  thf('170', plain,
% 4.16/4.39      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.16/4.39         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['168', '169'])).
% 4.16/4.39  thf('171', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('172', plain,
% 4.16/4.39      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_A))))),
% 4.16/4.39      inference('demod', [status(thm)],
% 4.16/4.39                ['123', '131', '132', '154', '170', '171'])).
% 4.16/4.39  thf('173', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf(d1_funct_2, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.39       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.16/4.39           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 4.16/4.39             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 4.16/4.39         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.16/4.39           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 4.16/4.39             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 4.16/4.39  thf(zf_stmt_1, axiom,
% 4.16/4.39    (![B:$i,A:$i]:
% 4.16/4.39     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 4.16/4.39       ( zip_tseitin_0 @ B @ A ) ))).
% 4.16/4.39  thf('174', plain,
% 4.16/4.39      (![X35 : $i, X36 : $i]:
% 4.16/4.39         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_1])).
% 4.16/4.39  thf(t113_zfmisc_1, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.16/4.39       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.16/4.39  thf('175', plain,
% 4.16/4.39      (![X4 : $i, X5 : $i]:
% 4.16/4.39         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.16/4.39  thf('176', plain,
% 4.16/4.39      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 4.16/4.39      inference('simplify', [status(thm)], ['175'])).
% 4.16/4.39  thf('177', plain,
% 4.16/4.39      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.16/4.39         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 4.16/4.39      inference('sup+', [status(thm)], ['174', '176'])).
% 4.16/4.39  thf('178', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['2', '3'])).
% 4.16/4.39  thf(t3_subset, axiom,
% 4.16/4.39    (![A:$i,B:$i]:
% 4.16/4.39     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 4.16/4.39  thf('179', plain,
% 4.16/4.39      (![X7 : $i, X8 : $i]:
% 4.16/4.39         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t3_subset])).
% 4.16/4.39  thf('180', plain,
% 4.16/4.39      ((r1_tarski @ sk_C @ 
% 4.16/4.39        (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['178', '179'])).
% 4.16/4.39  thf('181', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('182', plain,
% 4.16/4.39      ((r1_tarski @ sk_C @ 
% 4.16/4.39        (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['180', '181'])).
% 4.16/4.39  thf('183', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((r1_tarski @ sk_C @ k1_xboole_0)
% 4.16/4.39          | (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0))),
% 4.16/4.39      inference('sup+', [status(thm)], ['177', '182'])).
% 4.16/4.39  thf(t4_subset_1, axiom,
% 4.16/4.39    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 4.16/4.39  thf('184', plain,
% 4.16/4.39      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 4.16/4.39      inference('cnf', [status(esa)], [t4_subset_1])).
% 4.16/4.39  thf('185', plain,
% 4.16/4.39      (![X7 : $i, X8 : $i]:
% 4.16/4.39         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 4.16/4.39      inference('cnf', [status(esa)], [t3_subset])).
% 4.16/4.39  thf('186', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.16/4.39      inference('sup-', [status(thm)], ['184', '185'])).
% 4.16/4.39  thf('187', plain,
% 4.16/4.39      (![X0 : $i, X2 : $i]:
% 4.16/4.39         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 4.16/4.39      inference('cnf', [status(esa)], [d10_xboole_0])).
% 4.16/4.39  thf('188', plain,
% 4.16/4.39      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['186', '187'])).
% 4.16/4.39  thf('189', plain,
% 4.16/4.39      (![X0 : $i]:
% 4.16/4.39         ((zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0) | ((sk_C) = (k1_xboole_0)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['183', '188'])).
% 4.16/4.39  thf('190', plain,
% 4.16/4.39      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 4.16/4.39      inference('simplify', [status(thm)], ['167'])).
% 4.16/4.39  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 4.16/4.39  thf(zf_stmt_3, axiom,
% 4.16/4.39    (![C:$i,B:$i,A:$i]:
% 4.16/4.39     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 4.16/4.39       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 4.16/4.39  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 4.16/4.39  thf(zf_stmt_5, axiom,
% 4.16/4.39    (![A:$i,B:$i,C:$i]:
% 4.16/4.39     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 4.16/4.39       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 4.16/4.39         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 4.16/4.39           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 4.16/4.39             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 4.16/4.39  thf('191', plain,
% 4.16/4.39      (![X40 : $i, X41 : $i, X42 : $i]:
% 4.16/4.39         (~ (zip_tseitin_0 @ X40 @ X41)
% 4.16/4.39          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 4.16/4.39          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_5])).
% 4.16/4.39  thf('192', plain,
% 4.16/4.39      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.16/4.39         (u1_struct_0 @ sk_B))
% 4.16/4.39        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['190', '191'])).
% 4.16/4.39  thf('193', plain,
% 4.16/4.39      ((((sk_C) = (k1_xboole_0))
% 4.16/4.39        | (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.16/4.39           (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['189', '192'])).
% 4.16/4.39  thf('194', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('195', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['134', '135'])).
% 4.16/4.39  thf('196', plain,
% 4.16/4.39      (![X45 : $i, X46 : $i, X47 : $i]:
% 4.16/4.39         (~ (v2_funct_1 @ X45)
% 4.16/4.39          | ((k2_relset_1 @ X47 @ X46 @ X45) != (X46))
% 4.16/4.39          | (v1_funct_2 @ (k2_funct_1 @ X45) @ X46 @ X47)
% 4.16/4.39          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 4.16/4.39          | ~ (v1_funct_2 @ X45 @ X47 @ X46)
% 4.16/4.39          | ~ (v1_funct_1 @ X45))),
% 4.16/4.39      inference('cnf', [status(esa)], [t31_funct_2])).
% 4.16/4.39  thf('197', plain,
% 4.16/4.39      ((~ (v1_funct_1 @ sk_C)
% 4.16/4.39        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 4.16/4.39        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.16/4.39           (k1_relat_1 @ sk_C))
% 4.16/4.39        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39            != (u1_struct_0 @ sk_B))
% 4.16/4.39        | ~ (v2_funct_1 @ sk_C))),
% 4.16/4.39      inference('sup-', [status(thm)], ['195', '196'])).
% 4.16/4.39  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('199', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 4.16/4.39      inference('demod', [status(thm)], ['140', '141'])).
% 4.16/4.39  thf('200', plain, ((v2_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('201', plain,
% 4.16/4.39      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.16/4.39         (k1_relat_1 @ sk_C))
% 4.16/4.39        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39            != (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['197', '198', '199', '200'])).
% 4.16/4.39  thf('202', plain,
% 4.16/4.39      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 4.16/4.39         = (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['146', '147'])).
% 4.16/4.39  thf('203', plain,
% 4.16/4.39      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.16/4.39         (k1_relat_1 @ sk_C))
% 4.16/4.39        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['201', '202'])).
% 4.16/4.39  thf('204', plain,
% 4.16/4.39      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 4.16/4.39        | ~ (l1_struct_0 @ sk_B)
% 4.16/4.39        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.16/4.39           (k1_relat_1 @ sk_C)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['194', '203'])).
% 4.16/4.39  thf('205', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('206', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('207', plain,
% 4.16/4.39      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.16/4.39        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.16/4.39           (k1_relat_1 @ sk_C)))),
% 4.16/4.39      inference('demod', [status(thm)], ['204', '205', '206'])).
% 4.16/4.39  thf('208', plain,
% 4.16/4.39      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 4.16/4.39        (k1_relat_1 @ sk_C))),
% 4.16/4.39      inference('simplify', [status(thm)], ['207'])).
% 4.16/4.39  thf('209', plain,
% 4.16/4.39      (![X37 : $i, X38 : $i, X39 : $i]:
% 4.16/4.39         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 4.16/4.39          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 4.16/4.39          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_3])).
% 4.16/4.39  thf('210', plain,
% 4.16/4.39      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 4.16/4.39           (u1_struct_0 @ sk_B))
% 4.16/4.39        | ((u1_struct_0 @ sk_B)
% 4.16/4.39            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.16/4.39               (k2_funct_1 @ sk_C))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['208', '209'])).
% 4.16/4.39  thf('211', plain,
% 4.16/4.39      ((((sk_C) = (k1_xboole_0))
% 4.16/4.39        | ((u1_struct_0 @ sk_B)
% 4.16/4.39            = (k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.16/4.39               (k2_funct_1 @ sk_C))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['193', '210'])).
% 4.16/4.39  thf('212', plain,
% 4.16/4.39      ((m1_subset_1 @ sk_C @ 
% 4.16/4.39        (k1_zfmisc_1 @ 
% 4.16/4.39         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 4.16/4.39      inference('demod', [status(thm)], ['70', '71'])).
% 4.16/4.39  thf('213', plain,
% 4.16/4.39      (![X50 : $i, X51 : $i, X52 : $i]:
% 4.16/4.39         (((k2_relset_1 @ X51 @ X50 @ X52) != (X50))
% 4.16/4.39          | ~ (v2_funct_1 @ X52)
% 4.16/4.39          | ((k2_tops_2 @ X51 @ X50 @ X52) = (k2_funct_1 @ X52))
% 4.16/4.39          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X50)))
% 4.16/4.39          | ~ (v1_funct_2 @ X52 @ X51 @ X50)
% 4.16/4.39          | ~ (v1_funct_1 @ X52))),
% 4.16/4.39      inference('cnf', [status(esa)], [d4_tops_2])).
% 4.16/4.39  thf('214', plain,
% 4.16/4.39      ((~ (v1_funct_1 @ sk_C)
% 4.16/4.39        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 4.16/4.39        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.16/4.39            = (k2_funct_1 @ sk_C))
% 4.16/4.39        | ~ (v2_funct_1 @ sk_C)
% 4.16/4.39        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.16/4.39            != (k2_relat_1 @ sk_C)))),
% 4.16/4.39      inference('sup-', [status(thm)], ['212', '213'])).
% 4.16/4.39  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('216', plain,
% 4.16/4.39      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['86', '87'])).
% 4.16/4.39  thf('217', plain, ((v2_funct_1 @ sk_C)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('218', plain,
% 4.16/4.39      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.16/4.39         = (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('demod', [status(thm)], ['100', '101'])).
% 4.16/4.39  thf('219', plain,
% 4.16/4.39      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.16/4.39          = (k2_funct_1 @ sk_C))
% 4.16/4.39        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 4.16/4.39      inference('demod', [status(thm)], ['214', '215', '216', '217', '218'])).
% 4.16/4.39  thf('220', plain,
% 4.16/4.39      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 4.16/4.39         = (k2_funct_1 @ sk_C))),
% 4.16/4.39      inference('simplify', [status(thm)], ['219'])).
% 4.16/4.39  thf('221', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('222', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('223', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('224', plain,
% 4.16/4.39      (![X48 : $i]:
% 4.16/4.39         (((k2_struct_0 @ X48) = (u1_struct_0 @ X48)) | ~ (l1_struct_0 @ X48))),
% 4.16/4.39      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.16/4.39  thf('225', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          != (k2_struct_0 @ sk_B)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('split', [status(esa)], ['122'])).
% 4.16/4.39  thf('226', plain,
% 4.16/4.39      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 4.16/4.39           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39           != (k2_struct_0 @ sk_B))
% 4.16/4.39         | ~ (l1_struct_0 @ sk_A)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['224', '225'])).
% 4.16/4.39  thf('227', plain, ((l1_struct_0 @ sk_A)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('228', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          != (k2_struct_0 @ sk_B)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['226', '227'])).
% 4.16/4.39  thf('229', plain,
% 4.16/4.39      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 4.16/4.39           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39           != (k2_struct_0 @ sk_B))
% 4.16/4.39         | ~ (l1_struct_0 @ sk_A)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['223', '228'])).
% 4.16/4.39  thf('230', plain, ((l1_struct_0 @ sk_A)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('231', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          != (k2_struct_0 @ sk_B)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['229', '230'])).
% 4.16/4.39  thf('232', plain,
% 4.16/4.39      (((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 4.16/4.39           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39           != (k2_struct_0 @ sk_B))
% 4.16/4.39         | ~ (l1_struct_0 @ sk_B)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['222', '231'])).
% 4.16/4.39  thf('233', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('234', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          != (k2_struct_0 @ sk_B)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['232', '233'])).
% 4.16/4.39  thf('235', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 4.16/4.39          != (k2_struct_0 @ sk_B)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['221', '234'])).
% 4.16/4.39  thf('236', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('237', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 4.16/4.39          != (k2_relat_1 @ sk_C)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['235', '236'])).
% 4.16/4.39  thf('238', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('239', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 4.16/4.39      inference('demod', [status(thm)], ['54', '55', '56'])).
% 4.16/4.39  thf('240', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.16/4.39          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 4.16/4.39          != (k2_relat_1 @ sk_C)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['237', '238', '239'])).
% 4.16/4.39  thf('241', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 4.16/4.39          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['220', '240'])).
% 4.16/4.39  thf('242', plain,
% 4.16/4.39      (((((u1_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 4.16/4.39         | ((sk_C) = (k1_xboole_0))))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['211', '241'])).
% 4.16/4.39  thf('243', plain,
% 4.16/4.39      (((((k2_struct_0 @ sk_B) != (k2_relat_1 @ sk_C))
% 4.16/4.39         | ~ (l1_struct_0 @ sk_B)
% 4.16/4.39         | ((sk_C) = (k1_xboole_0))))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['173', '242'])).
% 4.16/4.39  thf('244', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 4.16/4.39      inference('sup+', [status(thm)], ['27', '28'])).
% 4.16/4.39  thf('245', plain, ((l1_struct_0 @ sk_B)),
% 4.16/4.39      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.16/4.39  thf('246', plain,
% 4.16/4.39      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 4.16/4.39         | ((sk_C) = (k1_xboole_0))))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('demod', [status(thm)], ['243', '244', '245'])).
% 4.16/4.39  thf('247', plain,
% 4.16/4.39      ((((sk_C) = (k1_xboole_0)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('simplify', [status(thm)], ['246'])).
% 4.16/4.39  thf('248', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 4.16/4.39      inference('clc', [status(thm)], ['46', '47'])).
% 4.16/4.39  thf('249', plain,
% 4.16/4.39      ((~ (v1_xboole_0 @ (k2_relat_1 @ k1_xboole_0)))
% 4.16/4.39         <= (~
% 4.16/4.39             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39                = (k2_struct_0 @ sk_B))))),
% 4.16/4.39      inference('sup-', [status(thm)], ['247', '248'])).
% 4.16/4.39  thf(t60_relat_1, axiom,
% 4.16/4.39    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 4.16/4.39     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 4.16/4.39  thf('250', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.16/4.39      inference('cnf', [status(esa)], [t60_relat_1])).
% 4.16/4.39  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 4.16/4.39  thf('251', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 4.16/4.39      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 4.16/4.39  thf('252', plain,
% 4.16/4.39      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          = (k2_struct_0 @ sk_B)))),
% 4.16/4.39      inference('demod', [status(thm)], ['249', '250', '251'])).
% 4.16/4.39  thf('253', plain,
% 4.16/4.39      (~
% 4.16/4.39       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          = (k2_struct_0 @ sk_A))) | 
% 4.16/4.39       ~
% 4.16/4.39       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          = (k2_struct_0 @ sk_B)))),
% 4.16/4.39      inference('split', [status(esa)], ['122'])).
% 4.16/4.39  thf('254', plain,
% 4.16/4.39      (~
% 4.16/4.39       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 4.16/4.39          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 4.16/4.39          = (k2_struct_0 @ sk_A)))),
% 4.16/4.39      inference('sat_resolution*', [status(thm)], ['252', '253'])).
% 4.16/4.39  thf('255', plain,
% 4.16/4.39      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 4.16/4.39      inference('simpl_trail', [status(thm)], ['172', '254'])).
% 4.16/4.39  thf('256', plain, ($false),
% 4.16/4.39      inference('simplify_reflect-', [status(thm)], ['121', '255'])).
% 4.16/4.39  
% 4.16/4.39  % SZS output end Refutation
% 4.16/4.39  
% 4.16/4.40  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
