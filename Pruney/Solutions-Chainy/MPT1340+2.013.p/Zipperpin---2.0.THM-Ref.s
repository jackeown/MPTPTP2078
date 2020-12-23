%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LEZ2Ww61BL

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:07 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  284 (3501 expanded)
%              Number of leaves         :   38 (1021 expanded)
%              Depth                    :   41
%              Number of atoms          : 2505 (76825 expanded)
%              Number of equality atoms :  109 (2124 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t64_tops_2,conjecture,(
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
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

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
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('3',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ( v1_partfun1 @ X12 @ X13 )
      | ~ ( v1_funct_2 @ X12 @ X13 @ X14 )
      | ~ ( v1_funct_1 @ X12 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('26',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('34',plain,(
    ! [X25: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('41',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['16','40'])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('48',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','55'])).

thf('57',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['32','39'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v4_relat_1 @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('63',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('65',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','63'])).

thf('66',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','56','64','65'])).

thf('67',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('68',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','55'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

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

thf('71',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('72',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','55'])).

thf('80',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('83',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('84',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','55'])).

thf('86',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['72','73','80','81','86'])).

thf('88',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('90',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['88','89','90'])).

thf('92',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['66','92'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('95',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('97',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','55'])).

thf('103',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

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

thf('104',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('105',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('109',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['107','108'])).

thf('110',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('113',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','55'])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('117',plain,(
    ! [X24: $i] :
      ( ( ( k2_struct_0 @ X24 )
        = ( u1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('118',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['117','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['116','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('127',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','55'])).

thf('129',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','106','115','129','130'])).

thf('132',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X26 @ X28 )
       != X26 )
      | ~ ( v2_funct_1 @ X28 )
      | ( ( k2_tops_2 @ X27 @ X26 @ X28 )
        = ( k2_funct_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X27 @ X26 )
      | ~ ( v1_funct_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('136',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('137',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('140',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('141',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['137','138','139','140','141'])).

thf('143',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('145',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relset_1 @ X23 @ X22 @ X21 )
       != X22 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X21 ) @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('146',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114'])).

thf('149',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('150',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['146','147','148','149','150'])).

thf('152',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['134','143','152'])).

thf('154',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('155',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( ( k2_relset_1 @ X10 @ X11 @ X9 )
        = ( k2_relat_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('156',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('157',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('158',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('160',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('161',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('164',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('165',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','48','55'])).

thf('166',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('168',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('169',plain,(
    ! [X2: $i] :
      ( ~ ( v2_funct_1 @ X2 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X2 ) )
        = X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('170',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('171',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != X15 )
      | ( v1_partfun1 @ X16 @ X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('172',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v4_relat_1 @ X16 @ ( k1_relat_1 @ X16 ) )
      | ( v1_partfun1 @ X16 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['170','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ X0 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['169','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['168','174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['167','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['166','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('181',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['179','180','181','182'])).

thf('184',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['142'])).

thf('185',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('188',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['186','187','188','189'])).

thf('191',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['162','190'])).

thf('192',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('193',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['161','195'])).

thf('197',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('198',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['196','197','198','199'])).

thf('201',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['160','200'])).

thf('202',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['142'])).

thf('203',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['159','203'])).

thf('205',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('206',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['204','205','206','207'])).

thf('209',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['158','208'])).

thf('210',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('211',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210','211','212'])).

thf('214',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_partfun1 @ X16 @ X15 )
      | ( ( k1_relat_1 @ X16 )
        = X15 )
      | ~ ( v4_relat_1 @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('215',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('217',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['215','216'])).

thf('218',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['157','217'])).

thf('219',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('220',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['218','219','220','221','222'])).

thf('224',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['156','223'])).

thf('225',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['153','224'])).

thf('226',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['94','226'])).

thf('228',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('229',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['227','228','229','230'])).

thf('232',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['93','231'])).

thf('233',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','232'])).

thf('234',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('235',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_funct_2 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('236',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_funct_2 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['234','236'])).

thf('238',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['237','238','239'])).

thf('241',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['46','47'])).

thf('242',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    $false ),
    inference(demod,[status(thm)],['233','240','241','242','243'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LEZ2Ww61BL
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:40:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.39/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.59  % Solved by: fo/fo7.sh
% 0.39/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.59  % done 313 iterations in 0.123s
% 0.39/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.59  % SZS output start Refutation
% 0.39/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.39/0.59  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.39/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.39/0.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.39/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.59  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.39/0.59  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.59  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.39/0.59  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.39/0.59  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.39/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.59  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.59  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.39/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.59  thf(t65_funct_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.59       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.39/0.59  thf('0', plain,
% 0.39/0.59      (![X2 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X2)
% 0.39/0.59          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.39/0.59          | ~ (v1_funct_1 @ X2)
% 0.39/0.59          | ~ (v1_relat_1 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.39/0.59  thf(d3_struct_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.39/0.59  thf('1', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('2', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf(t64_tops_2, conjecture,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( l1_struct_0 @ A ) =>
% 0.39/0.59       ( ![B:$i]:
% 0.39/0.59         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.59           ( ![C:$i]:
% 0.39/0.59             ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.59                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                 ( m1_subset_1 @
% 0.39/0.59                   C @ 
% 0.39/0.59                   ( k1_zfmisc_1 @
% 0.39/0.59                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59               ( ( ( ( k2_relset_1 @
% 0.39/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.59                     ( k2_struct_0 @ B ) ) & 
% 0.39/0.59                   ( v2_funct_1 @ C ) ) =>
% 0.39/0.59                 ( r2_funct_2 @
% 0.39/0.59                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.59                   ( k2_tops_2 @
% 0.39/0.59                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.59                     ( k2_tops_2 @
% 0.39/0.59                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.39/0.59                   C ) ) ) ) ) ) ))).
% 0.39/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.59    (~( ![A:$i]:
% 0.39/0.59        ( ( l1_struct_0 @ A ) =>
% 0.39/0.59          ( ![B:$i]:
% 0.39/0.59            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.39/0.59              ( ![C:$i]:
% 0.39/0.59                ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.59                    ( v1_funct_2 @
% 0.39/0.59                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.39/0.59                    ( m1_subset_1 @
% 0.39/0.59                      C @ 
% 0.39/0.59                      ( k1_zfmisc_1 @
% 0.39/0.59                        ( k2_zfmisc_1 @
% 0.39/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.39/0.59                  ( ( ( ( k2_relset_1 @
% 0.39/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.39/0.59                        ( k2_struct_0 @ B ) ) & 
% 0.39/0.59                      ( v2_funct_1 @ C ) ) =>
% 0.39/0.59                    ( r2_funct_2 @
% 0.39/0.59                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.39/0.59                      ( k2_tops_2 @
% 0.39/0.59                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.39/0.59                        ( k2_tops_2 @
% 0.39/0.59                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.39/0.59                      C ) ) ) ) ) ) ) )),
% 0.39/0.59    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.39/0.59  thf('3', plain,
% 0.39/0.59      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.59          sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('4', plain,
% 0.39/0.59      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.59           sk_C)
% 0.39/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.59  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('6', plain,
% 0.39/0.59      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.59          sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.39/0.59  thf('7', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.59  thf('8', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.59         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.39/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.59  thf('9', plain,
% 0.39/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.39/0.59  thf('10', plain,
% 0.39/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('11', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('12', plain,
% 0.39/0.59      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.59          sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['6', '11'])).
% 0.39/0.59  thf('13', plain,
% 0.39/0.59      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59           (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.59           sk_C)
% 0.39/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['1', '12'])).
% 0.39/0.59  thf('14', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('15', plain,
% 0.39/0.59      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 0.39/0.59           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.59          sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['13', '14'])).
% 0.39/0.59  thf('16', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('17', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('18', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('19', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_C @ 
% 0.39/0.59         (k1_zfmisc_1 @ 
% 0.39/0.59          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['17', '18'])).
% 0.39/0.59  thf('20', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('21', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.59  thf(cc5_funct_2, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.59       ( ![C:$i]:
% 0.39/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.39/0.59             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.39/0.59  thf('22', plain,
% 0.39/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.39/0.59          | (v1_partfun1 @ X12 @ X13)
% 0.39/0.59          | ~ (v1_funct_2 @ X12 @ X13 @ X14)
% 0.39/0.59          | ~ (v1_funct_1 @ X12)
% 0.39/0.59          | (v1_xboole_0 @ X14))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.39/0.59  thf('23', plain,
% 0.39/0.59      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.59        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.59  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('25', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('26', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('27', plain,
% 0.39/0.59      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['25', '26'])).
% 0.39/0.59  thf('28', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('29', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.39/0.59  thf('30', plain,
% 0.39/0.59      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.39/0.59        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['23', '24', '29'])).
% 0.39/0.59  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('32', plain,
% 0.39/0.59      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.39/0.59        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.59  thf('33', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf(fc5_struct_0, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.39/0.59       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.39/0.59  thf('34', plain,
% 0.39/0.59      (![X25 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ (k2_struct_0 @ X25))
% 0.39/0.59          | ~ (l1_struct_0 @ X25)
% 0.39/0.59          | (v2_struct_0 @ X25))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.39/0.59  thf('35', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.39/0.59        | (v2_struct_0 @ sk_B)
% 0.39/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.39/0.59  thf('36', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('37', plain,
% 0.39/0.59      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['35', '36'])).
% 0.39/0.59  thf('38', plain, (~ (v2_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('39', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('clc', [status(thm)], ['37', '38'])).
% 0.39/0.59  thf('40', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('clc', [status(thm)], ['32', '39'])).
% 0.39/0.59  thf('41', plain,
% 0.39/0.59      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup+', [status(thm)], ['16', '40'])).
% 0.39/0.59  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('43', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.39/0.59  thf(d4_partfun1, axiom,
% 0.39/0.59    (![A:$i,B:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.39/0.59       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X15 : $i, X16 : $i]:
% 0.39/0.59         (~ (v1_partfun1 @ X16 @ X15)
% 0.39/0.59          | ((k1_relat_1 @ X16) = (X15))
% 0.39/0.59          | ~ (v4_relat_1 @ X16 @ X15)
% 0.39/0.59          | ~ (v1_relat_1 @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.39/0.59        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf(cc1_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( v1_relat_1 @ C ) ))).
% 0.39/0.59  thf('47', plain,
% 0.39/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.39/0.59         ((v1_relat_1 @ X3)
% 0.39/0.59          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.59  thf('48', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('50', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_C @ 
% 0.39/0.59         (k1_zfmisc_1 @ 
% 0.39/0.59          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup+', [status(thm)], ['49', '50'])).
% 0.39/0.59  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('53', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.59  thf(cc2_relset_1, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.59       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.59         ((v4_relat_1 @ X6 @ X7)
% 0.39/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.59  thf('55', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.59  thf('56', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['45', '48', '55'])).
% 0.39/0.59  thf('57', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('clc', [status(thm)], ['32', '39'])).
% 0.39/0.59  thf('58', plain,
% 0.39/0.59      (![X15 : $i, X16 : $i]:
% 0.39/0.59         (~ (v1_partfun1 @ X16 @ X15)
% 0.39/0.59          | ((k1_relat_1 @ X16) = (X15))
% 0.39/0.59          | ~ (v4_relat_1 @ X16 @ X15)
% 0.39/0.59          | ~ (v1_relat_1 @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.39/0.59  thf('59', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.39/0.59        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.59  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('62', plain,
% 0.39/0.59      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.39/0.59         ((v4_relat_1 @ X6 @ X7)
% 0.39/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.39/0.59      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.59  thf('63', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['61', '62'])).
% 0.39/0.59  thf('64', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.39/0.59  thf('65', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['59', '60', '63'])).
% 0.39/0.59  thf('66', plain,
% 0.39/0.59      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.39/0.59          sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['15', '56', '64', '65'])).
% 0.39/0.59  thf('67', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('68', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.59  thf('69', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['45', '48', '55'])).
% 0.39/0.59  thf('70', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['68', '69'])).
% 0.39/0.59  thf(d4_tops_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.59       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.39/0.59         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.39/0.59  thf('71', plain,
% 0.39/0.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.59         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.39/0.59          | ~ (v2_funct_1 @ X28)
% 0.39/0.59          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.39/0.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.39/0.59          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.39/0.59          | ~ (v1_funct_1 @ X28))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.59  thf('72', plain,
% 0.39/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.39/0.59        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59            = (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.59        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59            != (u1_struct_0 @ sk_B)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['70', '71'])).
% 0.39/0.59  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('74', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('75', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('76', plain,
% 0.39/0.59      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup+', [status(thm)], ['74', '75'])).
% 0.39/0.59  thf('77', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('78', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['76', '77'])).
% 0.39/0.59  thf('79', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['45', '48', '55'])).
% 0.39/0.59  thf('80', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['78', '79'])).
% 0.39/0.59  thf('81', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('82', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.59  thf('83', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.59         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.39/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.59  thf('84', plain,
% 0.39/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['82', '83'])).
% 0.39/0.59  thf('85', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['45', '48', '55'])).
% 0.39/0.59  thf('86', plain,
% 0.39/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['84', '85'])).
% 0.39/0.59  thf('87', plain,
% 0.39/0.59      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59          = (k2_funct_1 @ sk_C))
% 0.39/0.59        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.39/0.59      inference('demod', [status(thm)], ['72', '73', '80', '81', '86'])).
% 0.39/0.59  thf('88', plain,
% 0.39/0.59      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_B)
% 0.39/0.59        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59            = (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['67', '87'])).
% 0.39/0.59  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('90', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('91', plain,
% 0.39/0.59      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.39/0.59        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59            = (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['88', '89', '90'])).
% 0.39/0.59  thf('92', plain,
% 0.39/0.59      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_funct_1 @ sk_C))),
% 0.39/0.59      inference('simplify', [status(thm)], ['91'])).
% 0.39/0.59  thf('93', plain,
% 0.39/0.59      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59           (k2_funct_1 @ sk_C)) @ 
% 0.39/0.59          sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['66', '92'])).
% 0.39/0.59  thf(fc6_funct_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.39/0.59       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.39/0.59         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.39/0.59         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.39/0.59  thf('94', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.59  thf('95', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('96', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['51', '52'])).
% 0.39/0.59  thf('97', plain,
% 0.39/0.59      (((m1_subset_1 @ sk_C @ 
% 0.39/0.59         (k1_zfmisc_1 @ 
% 0.39/0.59          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['95', '96'])).
% 0.39/0.59  thf('98', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('99', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['97', '98'])).
% 0.39/0.59  thf('100', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('101', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.59      inference('demod', [status(thm)], ['99', '100'])).
% 0.39/0.59  thf('102', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['45', '48', '55'])).
% 0.39/0.59  thf('103', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.59      inference('demod', [status(thm)], ['101', '102'])).
% 0.39/0.59  thf(t31_funct_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i]:
% 0.39/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.59       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.39/0.59         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.39/0.59           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.39/0.59           ( m1_subset_1 @
% 0.39/0.59             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.39/0.59  thf('104', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X21)
% 0.39/0.59          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.39/0.59          | (m1_subset_1 @ (k2_funct_1 @ X21) @ 
% 0.39/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.39/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.39/0.59          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.39/0.59          | ~ (v1_funct_1 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.59  thf('105', plain,
% 0.39/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.39/0.59        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.59           (k1_zfmisc_1 @ 
% 0.39/0.59            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.39/0.59        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.59            != (k2_relat_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['103', '104'])).
% 0.39/0.59  thf('106', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('107', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('108', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['76', '77'])).
% 0.39/0.59  thf('109', plain,
% 0.39/0.59      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['107', '108'])).
% 0.39/0.59  thf('110', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('111', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['109', '110'])).
% 0.39/0.59  thf('112', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('113', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['111', '112'])).
% 0.39/0.59  thf('114', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['45', '48', '55'])).
% 0.39/0.59  thf('115', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['113', '114'])).
% 0.39/0.59  thf('116', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('117', plain,
% 0.39/0.59      (![X24 : $i]:
% 0.39/0.59         (((k2_struct_0 @ X24) = (u1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.39/0.59      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.39/0.59  thf('118', plain,
% 0.39/0.59      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('119', plain,
% 0.39/0.59      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59          = (k2_struct_0 @ sk_B))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup+', [status(thm)], ['117', '118'])).
% 0.39/0.59  thf('120', plain, ((l1_struct_0 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('121', plain,
% 0.39/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['119', '120'])).
% 0.39/0.59  thf('122', plain,
% 0.39/0.59      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59          = (k2_struct_0 @ sk_B))
% 0.39/0.59        | ~ (l1_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['116', '121'])).
% 0.39/0.59  thf('123', plain, ((l1_struct_0 @ sk_B)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('124', plain,
% 0.39/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.39/0.59         = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['122', '123'])).
% 0.39/0.59  thf('125', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('126', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.39/0.59      inference('sup+', [status(thm)], ['9', '10'])).
% 0.39/0.59  thf('127', plain,
% 0.39/0.59      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.59         = (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.39/0.59  thf('128', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['45', '48', '55'])).
% 0.39/0.59  thf('129', plain,
% 0.39/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.59         = (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['127', '128'])).
% 0.39/0.59  thf('130', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('131', plain,
% 0.39/0.59      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.59         (k1_zfmisc_1 @ 
% 0.39/0.59          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.39/0.59        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['105', '106', '115', '129', '130'])).
% 0.39/0.59  thf('132', plain,
% 0.39/0.59      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['131'])).
% 0.39/0.59  thf('133', plain,
% 0.39/0.59      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.59         (((k2_relset_1 @ X27 @ X26 @ X28) != (X26))
% 0.39/0.59          | ~ (v2_funct_1 @ X28)
% 0.39/0.59          | ((k2_tops_2 @ X27 @ X26 @ X28) = (k2_funct_1 @ X28))
% 0.39/0.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26)))
% 0.39/0.59          | ~ (v1_funct_2 @ X28 @ X27 @ X26)
% 0.39/0.59          | ~ (v1_funct_1 @ X28))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.39/0.59  thf('134', plain,
% 0.39/0.59      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.59             (k1_relat_1 @ sk_C))
% 0.39/0.59        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['132', '133'])).
% 0.39/0.59  thf('135', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.59      inference('demod', [status(thm)], ['101', '102'])).
% 0.39/0.59  thf('136', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X21)
% 0.39/0.59          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.39/0.59          | (v1_funct_1 @ (k2_funct_1 @ X21))
% 0.39/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.39/0.59          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.39/0.59          | ~ (v1_funct_1 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.59  thf('137', plain,
% 0.39/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.39/0.59        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.59            != (k2_relat_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['135', '136'])).
% 0.39/0.59  thf('138', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('139', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['113', '114'])).
% 0.39/0.59  thf('140', plain,
% 0.39/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.59         = (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['127', '128'])).
% 0.39/0.59  thf('141', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('142', plain,
% 0.39/0.59      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['137', '138', '139', '140', '141'])).
% 0.39/0.59  thf('143', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.59      inference('simplify', [status(thm)], ['142'])).
% 0.39/0.59  thf('144', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.39/0.59      inference('demod', [status(thm)], ['101', '102'])).
% 0.39/0.59  thf('145', plain,
% 0.39/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X21)
% 0.39/0.59          | ((k2_relset_1 @ X23 @ X22 @ X21) != (X22))
% 0.39/0.59          | (v1_funct_2 @ (k2_funct_1 @ X21) @ X22 @ X23)
% 0.39/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22)))
% 0.39/0.59          | ~ (v1_funct_2 @ X21 @ X23 @ X22)
% 0.39/0.59          | ~ (v1_funct_1 @ X21))),
% 0.39/0.59      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.39/0.59  thf('146', plain,
% 0.39/0.59      ((~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.39/0.59        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.59           (k1_relat_1 @ sk_C))
% 0.39/0.59        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.59            != (k2_relat_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['144', '145'])).
% 0.39/0.59  thf('147', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('148', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['113', '114'])).
% 0.39/0.59  thf('149', plain,
% 0.39/0.59      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.39/0.59         = (k2_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['127', '128'])).
% 0.39/0.59  thf('150', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('151', plain,
% 0.39/0.59      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.59         (k1_relat_1 @ sk_C))
% 0.39/0.59        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['146', '147', '148', '149', '150'])).
% 0.39/0.59  thf('152', plain,
% 0.39/0.59      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.39/0.59        (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('simplify', [status(thm)], ['151'])).
% 0.39/0.59  thf('153', plain,
% 0.39/0.59      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['134', '143', '152'])).
% 0.39/0.59  thf('154', plain,
% 0.39/0.59      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['131'])).
% 0.39/0.59  thf('155', plain,
% 0.39/0.59      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.39/0.59         (((k2_relset_1 @ X10 @ X11 @ X9) = (k2_relat_1 @ X9))
% 0.39/0.59          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.59  thf('156', plain,
% 0.39/0.59      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['154', '155'])).
% 0.39/0.59  thf(t55_funct_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.39/0.59       ( ( v2_funct_1 @ A ) =>
% 0.39/0.59         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.39/0.59           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.39/0.59  thf('157', plain,
% 0.39/0.59      (![X1 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X1)
% 0.39/0.59          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.39/0.59          | ~ (v1_funct_1 @ X1)
% 0.39/0.59          | ~ (v1_relat_1 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.59  thf('158', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.59  thf('159', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.59  thf('160', plain,
% 0.39/0.59      (![X1 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X1)
% 0.39/0.59          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.39/0.59          | ~ (v1_funct_1 @ X1)
% 0.39/0.59          | ~ (v1_relat_1 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.59  thf('161', plain,
% 0.39/0.59      (![X2 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X2)
% 0.39/0.59          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.39/0.59          | ~ (v1_funct_1 @ X2)
% 0.39/0.59          | ~ (v1_relat_1 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.39/0.59  thf('162', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.59  thf('163', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.59  thf('164', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.59  thf('165', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.39/0.59      inference('demod', [status(thm)], ['45', '48', '55'])).
% 0.39/0.59  thf('166', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['164', '165'])).
% 0.39/0.59  thf('167', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.39/0.59  thf('168', plain,
% 0.39/0.59      (![X1 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X1)
% 0.39/0.59          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 0.39/0.59          | ~ (v1_funct_1 @ X1)
% 0.39/0.59          | ~ (v1_relat_1 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.59  thf('169', plain,
% 0.39/0.59      (![X2 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X2)
% 0.39/0.59          | ((k2_funct_1 @ (k2_funct_1 @ X2)) = (X2))
% 0.39/0.59          | ~ (v1_funct_1 @ X2)
% 0.39/0.59          | ~ (v1_relat_1 @ X2))),
% 0.39/0.59      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.39/0.59  thf('170', plain,
% 0.39/0.59      (![X1 : $i]:
% 0.39/0.59         (~ (v2_funct_1 @ X1)
% 0.39/0.59          | ((k2_relat_1 @ X1) = (k1_relat_1 @ (k2_funct_1 @ X1)))
% 0.39/0.59          | ~ (v1_funct_1 @ X1)
% 0.39/0.59          | ~ (v1_relat_1 @ X1))),
% 0.39/0.59      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.39/0.59  thf('171', plain,
% 0.39/0.59      (![X15 : $i, X16 : $i]:
% 0.39/0.59         (((k1_relat_1 @ X16) != (X15))
% 0.39/0.59          | (v1_partfun1 @ X16 @ X15)
% 0.39/0.59          | ~ (v4_relat_1 @ X16 @ X15)
% 0.39/0.59          | ~ (v1_relat_1 @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.39/0.59  thf('172', plain,
% 0.39/0.59      (![X16 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X16)
% 0.39/0.59          | ~ (v4_relat_1 @ X16 @ (k1_relat_1 @ X16))
% 0.39/0.59          | (v1_partfun1 @ X16 @ (k1_relat_1 @ X16)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['171'])).
% 0.39/0.59  thf('173', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['170', '172'])).
% 0.39/0.59  thf('174', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.59          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.39/0.59             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.39/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['169', '173'])).
% 0.39/0.59  thf('175', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.39/0.59             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.39/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['168', '174'])).
% 0.39/0.59  thf('176', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.39/0.59          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.39/0.59             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.39/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['175'])).
% 0.39/0.59  thf('177', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.39/0.59             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['167', '176'])).
% 0.39/0.59  thf('178', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.39/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.39/0.59          | ~ (v2_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_funct_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.39/0.59          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.39/0.59      inference('simplify', [status(thm)], ['177'])).
% 0.39/0.59  thf('179', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['166', '178'])).
% 0.39/0.59  thf('180', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('181', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('183', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['179', '180', '181', '182'])).
% 0.39/0.59  thf('184', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.59      inference('simplify', [status(thm)], ['142'])).
% 0.39/0.59  thf('185', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.39/0.59      inference('demod', [status(thm)], ['183', '184'])).
% 0.39/0.59  thf('186', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['163', '185'])).
% 0.39/0.59  thf('187', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('188', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('190', plain,
% 0.39/0.59      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.59         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['186', '187', '188', '189'])).
% 0.39/0.59  thf('191', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.59        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.59           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['162', '190'])).
% 0.39/0.59  thf('192', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('193', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('194', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('195', plain,
% 0.39/0.59      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.39/0.59        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 0.39/0.59  thf('196', plain,
% 0.39/0.59      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.39/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.59      inference('sup+', [status(thm)], ['161', '195'])).
% 0.39/0.59  thf('197', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('198', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('199', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('200', plain,
% 0.39/0.59      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('demod', [status(thm)], ['196', '197', '198', '199'])).
% 0.39/0.59  thf('201', plain,
% 0.39/0.59      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.59        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('sup+', [status(thm)], ['160', '200'])).
% 0.39/0.59  thf('202', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.39/0.59      inference('simplify', [status(thm)], ['142'])).
% 0.39/0.59  thf('203', plain,
% 0.39/0.59      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.59        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['201', '202'])).
% 0.39/0.59  thf('204', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['159', '203'])).
% 0.39/0.59  thf('205', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('206', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('207', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('208', plain,
% 0.39/0.59      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('demod', [status(thm)], ['204', '205', '206', '207'])).
% 0.39/0.59  thf('209', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.59        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['158', '208'])).
% 0.39/0.59  thf('210', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('211', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('213', plain,
% 0.39/0.59      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['209', '210', '211', '212'])).
% 0.39/0.59  thf('214', plain,
% 0.39/0.59      (![X15 : $i, X16 : $i]:
% 0.39/0.59         (~ (v1_partfun1 @ X16 @ X15)
% 0.39/0.59          | ((k1_relat_1 @ X16) = (X15))
% 0.39/0.59          | ~ (v4_relat_1 @ X16 @ X15)
% 0.39/0.59          | ~ (v1_relat_1 @ X16))),
% 0.39/0.59      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.39/0.59  thf('215', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.59        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['213', '214'])).
% 0.39/0.59  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('217', plain,
% 0.39/0.59      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.59        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('demod', [status(thm)], ['215', '216'])).
% 0.39/0.59  thf('218', plain,
% 0.39/0.59      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.39/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.59        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['157', '217'])).
% 0.39/0.59  thf('219', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['164', '165'])).
% 0.39/0.59  thf('220', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('222', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('223', plain,
% 0.39/0.59      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['218', '219', '220', '221', '222'])).
% 0.39/0.59  thf('224', plain,
% 0.39/0.59      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.39/0.59      inference('demod', [status(thm)], ['156', '223'])).
% 0.39/0.59  thf('225', plain,
% 0.39/0.59      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.39/0.59        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['153', '224'])).
% 0.39/0.59  thf('226', plain,
% 0.39/0.59      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.39/0.59        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['225'])).
% 0.39/0.59  thf('227', plain,
% 0.39/0.59      ((~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C)
% 0.39/0.59        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['94', '226'])).
% 0.39/0.59  thf('228', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('229', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('230', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('231', plain,
% 0.39/0.59      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.39/0.59         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.39/0.59      inference('demod', [status(thm)], ['227', '228', '229', '230'])).
% 0.39/0.59  thf('232', plain,
% 0.39/0.59      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.39/0.59          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['93', '231'])).
% 0.39/0.59  thf('233', plain,
% 0.39/0.59      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.59           sk_C)
% 0.39/0.59        | ~ (v1_relat_1 @ sk_C)
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | ~ (v2_funct_1 @ sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['0', '232'])).
% 0.39/0.59  thf('234', plain,
% 0.39/0.59      ((m1_subset_1 @ sk_C @ 
% 0.39/0.59        (k1_zfmisc_1 @ 
% 0.39/0.59         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.39/0.59      inference('demod', [status(thm)], ['68', '69'])).
% 0.39/0.59  thf(redefinition_r2_funct_2, axiom,
% 0.39/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.59         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.59       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.39/0.59  thf('235', plain,
% 0.39/0.59      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.59         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.39/0.59          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.39/0.59          | ~ (v1_funct_1 @ X17)
% 0.39/0.59          | ~ (v1_funct_1 @ X20)
% 0.39/0.59          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.39/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.39/0.59          | (r2_funct_2 @ X18 @ X19 @ X17 @ X20)
% 0.39/0.59          | ((X17) != (X20)))),
% 0.39/0.59      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.39/0.59  thf('236', plain,
% 0.39/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.59         ((r2_funct_2 @ X18 @ X19 @ X20 @ X20)
% 0.39/0.59          | ~ (v1_funct_1 @ X20)
% 0.39/0.59          | ~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.39/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['235'])).
% 0.39/0.59  thf('237', plain,
% 0.39/0.59      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.39/0.59        | ~ (v1_funct_1 @ sk_C)
% 0.39/0.59        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.39/0.59           sk_C))),
% 0.39/0.59      inference('sup-', [status(thm)], ['234', '236'])).
% 0.39/0.59  thf('238', plain,
% 0.39/0.59      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.39/0.59      inference('demod', [status(thm)], ['78', '79'])).
% 0.39/0.59  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('240', plain,
% 0.39/0.59      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.39/0.59      inference('demod', [status(thm)], ['237', '238', '239'])).
% 0.39/0.59  thf('241', plain, ((v1_relat_1 @ sk_C)),
% 0.39/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('242', plain, ((v1_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('243', plain, ((v2_funct_1 @ sk_C)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('244', plain, ($false),
% 0.39/0.59      inference('demod', [status(thm)], ['233', '240', '241', '242', '243'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.39/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
