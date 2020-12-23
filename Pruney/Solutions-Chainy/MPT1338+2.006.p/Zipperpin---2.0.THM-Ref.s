%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DJTP3Y6MPH

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:47 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  264 (2881 expanded)
%              Number of leaves         :   48 ( 838 expanded)
%              Depth                    :   24
%              Number of atoms          : 2436 (72487 expanded)
%              Number of equality atoms :  169 (3717 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
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

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('11',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('22',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ( v1_partfun1 @ X14 @ X15 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('35',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X31: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_struct_0 @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','43'])).

thf('45',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','44'])).

thf('46',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['45','46'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('49',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('52',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('54',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('55',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','56'])).

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

thf('58',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X27 ) @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['61','66'])).

thf('68',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('71',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('75',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('76',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['74','79'])).

thf('81',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('84',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('85',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('87',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60','73','87','88'])).

thf('90',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['89'])).

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

thf('91',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('92',plain,
    ( ~ ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','56'])).

thf('94',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('98',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('99',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('103',plain,
    ( ( zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('105',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('108',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('109',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X10 ) ) )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('110',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('111',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('112',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['110','117'])).

thf('119',plain,
    ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['107','118'])).

thf('120',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ~ ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k2_struct_0 @ sk_A ) @ X0 ) ),
    inference('sup-',[status(thm)],['106','121'])).

thf('123',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('124',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ ( k1_relat_1 @ sk_C ) @ X0 ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    zip_tseitin_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['103','124'])).

thf('126',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['92','125'])).

thf('127',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('128',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('129',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('130',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['130'])).

thf('132',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['128','134'])).

thf('136',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','137'])).

thf('139',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('140',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('141',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['33','43'])).

thf('143',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_partfun1 @ X26 @ X25 )
      | ( ( k1_relat_1 @ X26 )
        = X25 )
      | ~ ( v4_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('144',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('148',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['146','147'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','145','148'])).

thf('150',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('151',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('152',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['151','152'])).

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

thf('154',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('158',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('159',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('162',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('163',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('165',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['155','156','159','160','165'])).

thf('167',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['150','166'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('169',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['167','168','169'])).

thf('171',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['141','149','171'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('173',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('174',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('175',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k2_relset_1 @ X12 @ X13 @ X11 )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('176',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['14','56'])).

thf('178',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X32 @ X34 )
       != X32 )
      | ~ ( v2_funct_1 @ X34 )
      | ( ( k2_tops_2 @ X33 @ X32 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('179',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('182',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('184',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['179','180','181','182','183'])).

thf('185',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('187',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('188',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( u1_struct_0 @ X30 ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('189',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['130'])).

thf('190',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['190','191'])).

thf('193',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['187','192'])).

thf('194',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['186','195'])).

thf('197',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('198',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','145','148'])).

thf('200',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['144','145','148'])).

thf('201',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['49','52','55'])).

thf('202',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['198','199','200','201'])).

thf('203',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['185','202'])).

thf('204',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['176','203'])).

thf('205',plain,
    ( ( ( ( k1_relat_1 @ sk_C )
       != ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['173','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['205','206','207','208'])).

thf('210',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['130'])).

thf('212',plain,(
    ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['210','211'])).

thf('213',plain,(
    ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k2_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['172','212'])).

thf('214',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['126','213'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DJTP3Y6MPH
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.64/1.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.64/1.82  % Solved by: fo/fo7.sh
% 1.64/1.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.64/1.82  % done 1429 iterations in 1.378s
% 1.64/1.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.64/1.82  % SZS output start Refutation
% 1.64/1.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.64/1.82  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.64/1.82  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.64/1.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.64/1.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.64/1.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.64/1.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.64/1.82  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.64/1.82  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 1.64/1.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.64/1.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.64/1.82  thf(sk_C_type, type, sk_C: $i).
% 1.64/1.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.64/1.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.64/1.82  thf(sk_A_type, type, sk_A: $i).
% 1.64/1.82  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.64/1.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.64/1.82  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 1.64/1.82  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.64/1.82  thf(sk_B_type, type, sk_B: $i).
% 1.64/1.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.64/1.82  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.64/1.82  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.64/1.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.64/1.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.64/1.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.64/1.82  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.64/1.82  thf(d3_struct_0, axiom,
% 1.64/1.82    (![A:$i]:
% 1.64/1.82     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.64/1.82  thf('0', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('1', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf(t62_tops_2, conjecture,
% 1.64/1.82    (![A:$i]:
% 1.64/1.82     ( ( l1_struct_0 @ A ) =>
% 1.64/1.82       ( ![B:$i]:
% 1.64/1.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.64/1.82           ( ![C:$i]:
% 1.64/1.82             ( ( ( v1_funct_1 @ C ) & 
% 1.64/1.82                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.64/1.82                 ( m1_subset_1 @
% 1.64/1.82                   C @ 
% 1.64/1.82                   ( k1_zfmisc_1 @
% 1.64/1.82                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.64/1.82               ( ( ( ( k2_relset_1 @
% 1.64/1.82                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.64/1.82                     ( k2_struct_0 @ B ) ) & 
% 1.64/1.82                   ( v2_funct_1 @ C ) ) =>
% 1.64/1.82                 ( ( ( k1_relset_1 @
% 1.64/1.82                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.64/1.82                       ( k2_tops_2 @
% 1.64/1.82                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.64/1.82                     ( k2_struct_0 @ B ) ) & 
% 1.64/1.82                   ( ( k2_relset_1 @
% 1.64/1.82                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.64/1.82                       ( k2_tops_2 @
% 1.64/1.82                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.64/1.82                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 1.64/1.82  thf(zf_stmt_0, negated_conjecture,
% 1.64/1.82    (~( ![A:$i]:
% 1.64/1.82        ( ( l1_struct_0 @ A ) =>
% 1.64/1.82          ( ![B:$i]:
% 1.64/1.82            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 1.64/1.82              ( ![C:$i]:
% 1.64/1.82                ( ( ( v1_funct_1 @ C ) & 
% 1.64/1.82                    ( v1_funct_2 @
% 1.64/1.82                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 1.64/1.82                    ( m1_subset_1 @
% 1.64/1.82                      C @ 
% 1.64/1.82                      ( k1_zfmisc_1 @
% 1.64/1.82                        ( k2_zfmisc_1 @
% 1.64/1.82                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 1.64/1.82                  ( ( ( ( k2_relset_1 @
% 1.64/1.82                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 1.64/1.82                        ( k2_struct_0 @ B ) ) & 
% 1.64/1.82                      ( v2_funct_1 @ C ) ) =>
% 1.64/1.82                    ( ( ( k1_relset_1 @
% 1.64/1.82                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.64/1.82                          ( k2_tops_2 @
% 1.64/1.82                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.64/1.82                        ( k2_struct_0 @ B ) ) & 
% 1.64/1.82                      ( ( k2_relset_1 @
% 1.64/1.82                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 1.64/1.82                          ( k2_tops_2 @
% 1.64/1.82                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 1.64/1.82                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 1.64/1.82    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 1.64/1.82  thf('2', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('3', plain,
% 1.64/1.82      (((m1_subset_1 @ sk_C @ 
% 1.64/1.82         (k1_zfmisc_1 @ 
% 1.64/1.82          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_A))),
% 1.64/1.82      inference('sup+', [status(thm)], ['1', '2'])).
% 1.64/1.82  thf('4', plain, ((l1_struct_0 @ sk_A)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('5', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['3', '4'])).
% 1.64/1.82  thf('6', plain,
% 1.64/1.82      (((m1_subset_1 @ sk_C @ 
% 1.64/1.82         (k1_zfmisc_1 @ 
% 1.64/1.82          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['0', '5'])).
% 1.64/1.82  thf('7', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('8', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['6', '7'])).
% 1.64/1.82  thf('9', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf(redefinition_k2_relset_1, axiom,
% 1.64/1.82    (![A:$i,B:$i,C:$i]:
% 1.64/1.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.82       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.64/1.82  thf('10', plain,
% 1.64/1.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.64/1.82         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.64/1.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.64/1.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.64/1.82  thf('11', plain,
% 1.64/1.82      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82         = (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('sup-', [status(thm)], ['9', '10'])).
% 1.64/1.82  thf('12', plain,
% 1.64/1.82      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82         = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('13', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('14', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.64/1.82      inference('demod', [status(thm)], ['8', '13'])).
% 1.64/1.82  thf('15', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('16', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('17', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('18', plain,
% 1.64/1.82      (((m1_subset_1 @ sk_C @ 
% 1.64/1.82         (k1_zfmisc_1 @ 
% 1.64/1.82          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['16', '17'])).
% 1.64/1.82  thf('19', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('20', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['18', '19'])).
% 1.64/1.82  thf('21', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('22', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.64/1.82      inference('demod', [status(thm)], ['20', '21'])).
% 1.64/1.82  thf(cc5_funct_2, axiom,
% 1.64/1.82    (![A:$i,B:$i]:
% 1.64/1.82     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.64/1.82       ( ![C:$i]:
% 1.64/1.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.82           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 1.64/1.82             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 1.64/1.82  thf('23', plain,
% 1.64/1.82      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.64/1.82         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 1.64/1.82          | (v1_partfun1 @ X14 @ X15)
% 1.64/1.82          | ~ (v1_funct_2 @ X14 @ X15 @ X16)
% 1.64/1.82          | ~ (v1_funct_1 @ X14)
% 1.64/1.82          | (v1_xboole_0 @ X16))),
% 1.64/1.82      inference('cnf', [status(esa)], [cc5_funct_2])).
% 1.64/1.82  thf('24', plain,
% 1.64/1.82      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.64/1.82        | ~ (v1_funct_1 @ sk_C)
% 1.64/1.82        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 1.64/1.82        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['22', '23'])).
% 1.64/1.82  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('26', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('27', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('28', plain,
% 1.64/1.82      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['26', '27'])).
% 1.64/1.82  thf('29', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('30', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('demod', [status(thm)], ['28', '29'])).
% 1.64/1.82  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('32', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['30', '31'])).
% 1.64/1.82  thf('33', plain,
% 1.64/1.82      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.64/1.82        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 1.64/1.82      inference('demod', [status(thm)], ['24', '25', '32'])).
% 1.64/1.82  thf('34', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('35', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf(fc2_struct_0, axiom,
% 1.64/1.82    (![A:$i]:
% 1.64/1.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.64/1.82       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.64/1.82  thf('36', plain,
% 1.64/1.82      (![X31 : $i]:
% 1.64/1.82         (~ (v1_xboole_0 @ (u1_struct_0 @ X31))
% 1.64/1.82          | ~ (l1_struct_0 @ X31)
% 1.64/1.82          | (v2_struct_0 @ X31))),
% 1.64/1.82      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.64/1.82  thf('37', plain,
% 1.64/1.82      (![X0 : $i]:
% 1.64/1.82         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.64/1.82          | ~ (l1_struct_0 @ X0)
% 1.64/1.82          | (v2_struct_0 @ X0)
% 1.64/1.82          | ~ (l1_struct_0 @ X0))),
% 1.64/1.82      inference('sup-', [status(thm)], ['35', '36'])).
% 1.64/1.82  thf('38', plain,
% 1.64/1.82      (![X0 : $i]:
% 1.64/1.82         ((v2_struct_0 @ X0)
% 1.64/1.82          | ~ (l1_struct_0 @ X0)
% 1.64/1.82          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.64/1.82      inference('simplify', [status(thm)], ['37'])).
% 1.64/1.82  thf('39', plain,
% 1.64/1.82      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_B)
% 1.64/1.82        | (v2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup-', [status(thm)], ['34', '38'])).
% 1.64/1.82  thf('40', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('41', plain,
% 1.64/1.82      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 1.64/1.82      inference('demod', [status(thm)], ['39', '40'])).
% 1.64/1.82  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('43', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('clc', [status(thm)], ['41', '42'])).
% 1.64/1.82  thf('44', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.64/1.82      inference('clc', [status(thm)], ['33', '43'])).
% 1.64/1.82  thf('45', plain,
% 1.64/1.82      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.64/1.82      inference('sup+', [status(thm)], ['15', '44'])).
% 1.64/1.82  thf('46', plain, ((l1_struct_0 @ sk_A)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('47', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['45', '46'])).
% 1.64/1.82  thf(d4_partfun1, axiom,
% 1.64/1.82    (![A:$i,B:$i]:
% 1.64/1.82     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.64/1.82       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 1.64/1.82  thf('48', plain,
% 1.64/1.82      (![X25 : $i, X26 : $i]:
% 1.64/1.82         (~ (v1_partfun1 @ X26 @ X25)
% 1.64/1.82          | ((k1_relat_1 @ X26) = (X25))
% 1.64/1.82          | ~ (v4_relat_1 @ X26 @ X25)
% 1.64/1.82          | ~ (v1_relat_1 @ X26))),
% 1.64/1.82      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.64/1.82  thf('49', plain,
% 1.64/1.82      ((~ (v1_relat_1 @ sk_C)
% 1.64/1.82        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 1.64/1.82        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['47', '48'])).
% 1.64/1.82  thf('50', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf(cc1_relset_1, axiom,
% 1.64/1.82    (![A:$i,B:$i,C:$i]:
% 1.64/1.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.82       ( v1_relat_1 @ C ) ))).
% 1.64/1.82  thf('51', plain,
% 1.64/1.82      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.64/1.82         ((v1_relat_1 @ X2)
% 1.64/1.82          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 1.64/1.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.64/1.82  thf('52', plain, ((v1_relat_1 @ sk_C)),
% 1.64/1.82      inference('sup-', [status(thm)], ['50', '51'])).
% 1.64/1.82  thf('53', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['3', '4'])).
% 1.64/1.82  thf(cc2_relset_1, axiom,
% 1.64/1.82    (![A:$i,B:$i,C:$i]:
% 1.64/1.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.82       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.64/1.82  thf('54', plain,
% 1.64/1.82      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.64/1.82         ((v4_relat_1 @ X5 @ X6)
% 1.64/1.82          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.64/1.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.64/1.82  thf('55', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('sup-', [status(thm)], ['53', '54'])).
% 1.64/1.82  thf('56', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.82  thf('57', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.64/1.82      inference('demod', [status(thm)], ['14', '56'])).
% 1.64/1.82  thf(t31_funct_2, axiom,
% 1.64/1.82    (![A:$i,B:$i,C:$i]:
% 1.64/1.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.64/1.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.64/1.82       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 1.64/1.82         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 1.64/1.82           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 1.64/1.82           ( m1_subset_1 @
% 1.64/1.82             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 1.64/1.82  thf('58', plain,
% 1.64/1.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.64/1.82         (~ (v2_funct_1 @ X27)
% 1.64/1.82          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 1.64/1.82          | (v1_funct_2 @ (k2_funct_1 @ X27) @ X28 @ X29)
% 1.64/1.82          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.64/1.82          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 1.64/1.82          | ~ (v1_funct_1 @ X27))),
% 1.64/1.82      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.64/1.82  thf('59', plain,
% 1.64/1.82      ((~ (v1_funct_1 @ sk_C)
% 1.64/1.82        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.64/1.82        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.64/1.82           (k1_relat_1 @ sk_C))
% 1.64/1.82        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82            != (k2_relat_1 @ sk_C))
% 1.64/1.82        | ~ (v2_funct_1 @ sk_C))),
% 1.64/1.82      inference('sup-', [status(thm)], ['57', '58'])).
% 1.64/1.82  thf('60', plain, ((v1_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('61', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('62', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('63', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('64', plain,
% 1.64/1.82      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_A))),
% 1.64/1.82      inference('sup+', [status(thm)], ['62', '63'])).
% 1.64/1.82  thf('65', plain, ((l1_struct_0 @ sk_A)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('66', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.64/1.82      inference('demod', [status(thm)], ['64', '65'])).
% 1.64/1.82  thf('67', plain,
% 1.64/1.82      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['61', '66'])).
% 1.64/1.82  thf('68', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('69', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('demod', [status(thm)], ['67', '68'])).
% 1.64/1.82  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('71', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['69', '70'])).
% 1.64/1.82  thf('72', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.82  thf('73', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['71', '72'])).
% 1.64/1.82  thf('74', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('75', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('76', plain,
% 1.64/1.82      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82         = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('77', plain,
% 1.64/1.82      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82          = (k2_struct_0 @ sk_B))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_A))),
% 1.64/1.82      inference('sup+', [status(thm)], ['75', '76'])).
% 1.64/1.82  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('79', plain,
% 1.64/1.82      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82         = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('demod', [status(thm)], ['77', '78'])).
% 1.64/1.82  thf('80', plain,
% 1.64/1.82      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82          = (k2_struct_0 @ sk_B))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['74', '79'])).
% 1.64/1.82  thf('81', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('82', plain,
% 1.64/1.82      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82         = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('demod', [status(thm)], ['80', '81'])).
% 1.64/1.82  thf('83', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('84', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('85', plain,
% 1.64/1.82      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82         = (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['82', '83', '84'])).
% 1.64/1.82  thf('86', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.82  thf('87', plain,
% 1.64/1.82      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82         = (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['85', '86'])).
% 1.64/1.82  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('89', plain,
% 1.64/1.82      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.64/1.82         (k1_relat_1 @ sk_C))
% 1.64/1.82        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.64/1.82      inference('demod', [status(thm)], ['59', '60', '73', '87', '88'])).
% 1.64/1.82  thf('90', plain,
% 1.64/1.82      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 1.64/1.82        (k1_relat_1 @ sk_C))),
% 1.64/1.82      inference('simplify', [status(thm)], ['89'])).
% 1.64/1.82  thf(d1_funct_2, axiom,
% 1.64/1.82    (![A:$i,B:$i,C:$i]:
% 1.64/1.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.64/1.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.64/1.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.64/1.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.64/1.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.64/1.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.64/1.82  thf(zf_stmt_1, axiom,
% 1.64/1.82    (![C:$i,B:$i,A:$i]:
% 1.64/1.82     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.64/1.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.64/1.82  thf('91', plain,
% 1.64/1.82      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.64/1.82         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 1.64/1.82          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 1.64/1.82          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.64/1.82  thf('92', plain,
% 1.64/1.82      ((~ (zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82           (k2_relat_1 @ sk_C))
% 1.64/1.82        | ((k2_relat_1 @ sk_C)
% 1.64/1.82            = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82               (k2_funct_1 @ sk_C))))),
% 1.64/1.82      inference('sup-', [status(thm)], ['90', '91'])).
% 1.64/1.82  thf('93', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.64/1.82      inference('demod', [status(thm)], ['14', '56'])).
% 1.64/1.82  thf('94', plain,
% 1.64/1.82      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.64/1.82         (~ (v2_funct_1 @ X27)
% 1.64/1.82          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 1.64/1.82          | (m1_subset_1 @ (k2_funct_1 @ X27) @ 
% 1.64/1.82             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.64/1.82          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 1.64/1.82          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 1.64/1.82          | ~ (v1_funct_1 @ X27))),
% 1.64/1.82      inference('cnf', [status(esa)], [t31_funct_2])).
% 1.64/1.82  thf('95', plain,
% 1.64/1.82      ((~ (v1_funct_1 @ sk_C)
% 1.64/1.82        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.64/1.82        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.64/1.82           (k1_zfmisc_1 @ 
% 1.64/1.82            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.64/1.82        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82            != (k2_relat_1 @ sk_C))
% 1.64/1.82        | ~ (v2_funct_1 @ sk_C))),
% 1.64/1.82      inference('sup-', [status(thm)], ['93', '94'])).
% 1.64/1.82  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('97', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['71', '72'])).
% 1.64/1.82  thf('98', plain,
% 1.64/1.82      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82         = (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['85', '86'])).
% 1.64/1.82  thf('99', plain, ((v2_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('100', plain,
% 1.64/1.82      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.64/1.82         (k1_zfmisc_1 @ 
% 1.64/1.82          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 1.64/1.82        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.64/1.82      inference('demod', [status(thm)], ['95', '96', '97', '98', '99'])).
% 1.64/1.82  thf('101', plain,
% 1.64/1.82      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.64/1.82      inference('simplify', [status(thm)], ['100'])).
% 1.64/1.82  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.64/1.82  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.64/1.82  thf(zf_stmt_4, axiom,
% 1.64/1.82    (![B:$i,A:$i]:
% 1.64/1.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.64/1.82       ( zip_tseitin_0 @ B @ A ) ))).
% 1.64/1.82  thf(zf_stmt_5, axiom,
% 1.64/1.82    (![A:$i,B:$i,C:$i]:
% 1.64/1.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.82       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.64/1.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.64/1.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.64/1.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.64/1.82  thf('102', plain,
% 1.64/1.82      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.64/1.82         (~ (zip_tseitin_0 @ X22 @ X23)
% 1.64/1.82          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 1.64/1.82          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.64/1.82  thf('103', plain,
% 1.64/1.82      (((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82         (k2_relat_1 @ sk_C))
% 1.64/1.82        | ~ (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['101', '102'])).
% 1.64/1.82  thf('104', plain,
% 1.64/1.82      (![X17 : $i, X18 : $i]:
% 1.64/1.82         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.64/1.82  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.64/1.82  thf('105', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.64/1.82  thf('106', plain,
% 1.64/1.82      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.64/1.82      inference('sup+', [status(thm)], ['104', '105'])).
% 1.64/1.82  thf('107', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('108', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.64/1.82      inference('demod', [status(thm)], ['20', '21'])).
% 1.64/1.82  thf(cc3_relset_1, axiom,
% 1.64/1.82    (![A:$i,B:$i]:
% 1.64/1.82     ( ( v1_xboole_0 @ A ) =>
% 1.64/1.82       ( ![C:$i]:
% 1.64/1.82         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.64/1.82           ( v1_xboole_0 @ C ) ) ) ))).
% 1.64/1.82  thf('109', plain,
% 1.64/1.82      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.64/1.82         (~ (v1_xboole_0 @ X8)
% 1.64/1.82          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X10)))
% 1.64/1.82          | (v1_xboole_0 @ X9))),
% 1.64/1.82      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.64/1.82  thf('110', plain,
% 1.64/1.82      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['108', '109'])).
% 1.64/1.82  thf(l13_xboole_0, axiom,
% 1.64/1.82    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.64/1.82  thf('111', plain,
% 1.64/1.82      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.82      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.64/1.82  thf(t60_relat_1, axiom,
% 1.64/1.82    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.64/1.82     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.64/1.82  thf('112', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.64/1.82      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.64/1.82  thf('113', plain,
% 1.64/1.82      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.82      inference('sup+', [status(thm)], ['111', '112'])).
% 1.64/1.82  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.64/1.82      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.64/1.82  thf('115', plain,
% 1.64/1.82      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.64/1.82      inference('sup+', [status(thm)], ['113', '114'])).
% 1.64/1.82  thf('116', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('clc', [status(thm)], ['41', '42'])).
% 1.64/1.82  thf('117', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.64/1.82      inference('sup-', [status(thm)], ['115', '116'])).
% 1.64/1.82  thf('118', plain, (~ (v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 1.64/1.82      inference('clc', [status(thm)], ['110', '117'])).
% 1.64/1.82  thf('119', plain,
% 1.64/1.82      ((~ (v1_xboole_0 @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.64/1.82      inference('sup-', [status(thm)], ['107', '118'])).
% 1.64/1.82  thf('120', plain, ((l1_struct_0 @ sk_A)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('121', plain, (~ (v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['119', '120'])).
% 1.64/1.82  thf('122', plain, (![X0 : $i]: (zip_tseitin_0 @ (k2_struct_0 @ sk_A) @ X0)),
% 1.64/1.82      inference('sup-', [status(thm)], ['106', '121'])).
% 1.64/1.82  thf('123', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.82  thf('124', plain, (![X0 : $i]: (zip_tseitin_0 @ (k1_relat_1 @ sk_C) @ X0)),
% 1.64/1.82      inference('demod', [status(thm)], ['122', '123'])).
% 1.64/1.82  thf('125', plain,
% 1.64/1.82      ((zip_tseitin_1 @ (k2_funct_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82        (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['103', '124'])).
% 1.64/1.82  thf('126', plain,
% 1.64/1.82      (((k2_relat_1 @ sk_C)
% 1.64/1.82         = (k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82            (k2_funct_1 @ sk_C)))),
% 1.64/1.82      inference('demod', [status(thm)], ['92', '125'])).
% 1.64/1.82  thf('127', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.82  thf('128', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('129', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('130', plain,
% 1.64/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82          != (k2_struct_0 @ sk_B))
% 1.64/1.82        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82            != (k2_struct_0 @ sk_A)))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('131', plain,
% 1.64/1.82      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82          != (k2_struct_0 @ sk_B)))
% 1.64/1.82         <= (~
% 1.64/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82                = (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('split', [status(esa)], ['130'])).
% 1.64/1.82  thf('132', plain,
% 1.64/1.82      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82           != (k2_struct_0 @ sk_B))
% 1.64/1.82         | ~ (l1_struct_0 @ sk_B)))
% 1.64/1.82         <= (~
% 1.64/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82                = (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('sup-', [status(thm)], ['129', '131'])).
% 1.64/1.82  thf('133', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('134', plain,
% 1.64/1.82      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82          != (k2_struct_0 @ sk_B)))
% 1.64/1.82         <= (~
% 1.64/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82                = (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['132', '133'])).
% 1.64/1.82  thf('135', plain,
% 1.64/1.82      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.64/1.82           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82           != (k2_struct_0 @ sk_B))
% 1.64/1.82         | ~ (l1_struct_0 @ sk_A)))
% 1.64/1.82         <= (~
% 1.64/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82                = (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('sup-', [status(thm)], ['128', '134'])).
% 1.64/1.82  thf('136', plain, ((l1_struct_0 @ sk_A)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('137', plain,
% 1.64/1.82      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 1.64/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82          != (k2_struct_0 @ sk_B)))
% 1.64/1.82         <= (~
% 1.64/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82                = (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['135', '136'])).
% 1.64/1.82  thf('138', plain,
% 1.64/1.82      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82          != (k2_struct_0 @ sk_B)))
% 1.64/1.82         <= (~
% 1.64/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82                = (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('sup-', [status(thm)], ['127', '137'])).
% 1.64/1.82  thf('139', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('140', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('141', plain,
% 1.64/1.82      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82          != (k2_relat_1 @ sk_C)))
% 1.64/1.82         <= (~
% 1.64/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82                = (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['138', '139', '140'])).
% 1.64/1.82  thf('142', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.64/1.82      inference('clc', [status(thm)], ['33', '43'])).
% 1.64/1.82  thf('143', plain,
% 1.64/1.82      (![X25 : $i, X26 : $i]:
% 1.64/1.82         (~ (v1_partfun1 @ X26 @ X25)
% 1.64/1.82          | ((k1_relat_1 @ X26) = (X25))
% 1.64/1.82          | ~ (v4_relat_1 @ X26 @ X25)
% 1.64/1.82          | ~ (v1_relat_1 @ X26))),
% 1.64/1.82      inference('cnf', [status(esa)], [d4_partfun1])).
% 1.64/1.82  thf('144', plain,
% 1.64/1.82      ((~ (v1_relat_1 @ sk_C)
% 1.64/1.82        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 1.64/1.82        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['142', '143'])).
% 1.64/1.82  thf('145', plain, ((v1_relat_1 @ sk_C)),
% 1.64/1.82      inference('sup-', [status(thm)], ['50', '51'])).
% 1.64/1.82  thf('146', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('147', plain,
% 1.64/1.82      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.64/1.82         ((v4_relat_1 @ X5 @ X6)
% 1.64/1.82          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 1.64/1.82      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.64/1.82  thf('148', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 1.64/1.82      inference('sup-', [status(thm)], ['146', '147'])).
% 1.64/1.82  thf('149', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['144', '145', '148'])).
% 1.64/1.82  thf('150', plain,
% 1.64/1.82      (![X30 : $i]:
% 1.64/1.82         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.82  thf('151', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['3', '4'])).
% 1.64/1.82  thf('152', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.82  thf('153', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['151', '152'])).
% 1.64/1.82  thf(d4_tops_2, axiom,
% 1.64/1.82    (![A:$i,B:$i,C:$i]:
% 1.64/1.82     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.64/1.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.64/1.82       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 1.64/1.82         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 1.64/1.82  thf('154', plain,
% 1.64/1.82      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.64/1.82         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 1.64/1.82          | ~ (v2_funct_1 @ X34)
% 1.64/1.82          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 1.64/1.82          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.64/1.82          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.64/1.82          | ~ (v1_funct_1 @ X34))),
% 1.64/1.82      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.64/1.82  thf('155', plain,
% 1.64/1.82      ((~ (v1_funct_1 @ sk_C)
% 1.64/1.82        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 1.64/1.82        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82            = (k2_funct_1 @ sk_C))
% 1.64/1.82        | ~ (v2_funct_1 @ sk_C)
% 1.64/1.82        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82            != (u1_struct_0 @ sk_B)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['153', '154'])).
% 1.64/1.82  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('157', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 1.64/1.82      inference('demod', [status(thm)], ['64', '65'])).
% 1.64/1.82  thf('158', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.82  thf('159', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 1.64/1.82      inference('demod', [status(thm)], ['157', '158'])).
% 1.64/1.82  thf('160', plain, ((v2_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('161', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['3', '4'])).
% 1.64/1.82  thf('162', plain,
% 1.64/1.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.64/1.82         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.64/1.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.64/1.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.64/1.82  thf('163', plain,
% 1.64/1.82      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82         = (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('sup-', [status(thm)], ['161', '162'])).
% 1.64/1.82  thf('164', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.82      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.82  thf('165', plain,
% 1.64/1.82      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82         = (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['163', '164'])).
% 1.64/1.82  thf('166', plain,
% 1.64/1.82      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82          = (k2_funct_1 @ sk_C))
% 1.64/1.82        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 1.64/1.82      inference('demod', [status(thm)], ['155', '156', '159', '160', '165'])).
% 1.64/1.82  thf('167', plain,
% 1.64/1.82      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 1.64/1.82        | ~ (l1_struct_0 @ sk_B)
% 1.64/1.82        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82            = (k2_funct_1 @ sk_C)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['150', '166'])).
% 1.64/1.82  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.82      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.82  thf('169', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('170', plain,
% 1.64/1.82      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 1.64/1.82        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82            = (k2_funct_1 @ sk_C)))),
% 1.64/1.82      inference('demod', [status(thm)], ['167', '168', '169'])).
% 1.64/1.82  thf('171', plain,
% 1.64/1.82      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 1.64/1.82         = (k2_funct_1 @ sk_C))),
% 1.64/1.82      inference('simplify', [status(thm)], ['170'])).
% 1.64/1.82  thf('172', plain,
% 1.64/1.82      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 1.64/1.82         <= (~
% 1.64/1.82             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.82                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.82                = (k2_struct_0 @ sk_B))))),
% 1.64/1.82      inference('demod', [status(thm)], ['141', '149', '171'])).
% 1.64/1.82  thf(t55_funct_1, axiom,
% 1.64/1.82    (![A:$i]:
% 1.64/1.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.64/1.82       ( ( v2_funct_1 @ A ) =>
% 1.64/1.82         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 1.64/1.82           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 1.64/1.82  thf('173', plain,
% 1.64/1.82      (![X1 : $i]:
% 1.64/1.82         (~ (v2_funct_1 @ X1)
% 1.64/1.82          | ((k1_relat_1 @ X1) = (k2_relat_1 @ (k2_funct_1 @ X1)))
% 1.64/1.82          | ~ (v1_funct_1 @ X1)
% 1.64/1.82          | ~ (v1_relat_1 @ X1))),
% 1.64/1.82      inference('cnf', [status(esa)], [t55_funct_1])).
% 1.64/1.82  thf('174', plain,
% 1.64/1.82      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 1.64/1.82      inference('simplify', [status(thm)], ['100'])).
% 1.64/1.82  thf('175', plain,
% 1.64/1.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.64/1.82         (((k2_relset_1 @ X12 @ X13 @ X11) = (k2_relat_1 @ X11))
% 1.64/1.82          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 1.64/1.82      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.64/1.82  thf('176', plain,
% 1.64/1.82      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.82         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['174', '175'])).
% 1.64/1.82  thf('177', plain,
% 1.64/1.82      ((m1_subset_1 @ sk_C @ 
% 1.64/1.82        (k1_zfmisc_1 @ 
% 1.64/1.82         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 1.64/1.82      inference('demod', [status(thm)], ['14', '56'])).
% 1.64/1.82  thf('178', plain,
% 1.64/1.82      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.64/1.82         (((k2_relset_1 @ X33 @ X32 @ X34) != (X32))
% 1.64/1.82          | ~ (v2_funct_1 @ X34)
% 1.64/1.82          | ((k2_tops_2 @ X33 @ X32 @ X34) = (k2_funct_1 @ X34))
% 1.64/1.82          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.64/1.82          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.64/1.82          | ~ (v1_funct_1 @ X34))),
% 1.64/1.82      inference('cnf', [status(esa)], [d4_tops_2])).
% 1.64/1.82  thf('179', plain,
% 1.64/1.82      ((~ (v1_funct_1 @ sk_C)
% 1.64/1.82        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 1.64/1.82        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82            = (k2_funct_1 @ sk_C))
% 1.64/1.82        | ~ (v2_funct_1 @ sk_C)
% 1.64/1.82        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82            != (k2_relat_1 @ sk_C)))),
% 1.64/1.82      inference('sup-', [status(thm)], ['177', '178'])).
% 1.64/1.82  thf('180', plain, ((v1_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('181', plain,
% 1.64/1.82      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['71', '72'])).
% 1.64/1.82  thf('182', plain, ((v2_funct_1 @ sk_C)),
% 1.64/1.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.82  thf('183', plain,
% 1.64/1.82      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82         = (k2_relat_1 @ sk_C))),
% 1.64/1.82      inference('demod', [status(thm)], ['85', '86'])).
% 1.64/1.82  thf('184', plain,
% 1.64/1.82      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82          = (k2_funct_1 @ sk_C))
% 1.64/1.82        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 1.64/1.82      inference('demod', [status(thm)], ['179', '180', '181', '182', '183'])).
% 1.64/1.82  thf('185', plain,
% 1.64/1.82      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 1.64/1.82         = (k2_funct_1 @ sk_C))),
% 1.64/1.82      inference('simplify', [status(thm)], ['184'])).
% 1.64/1.83  thf('186', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.83      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.83  thf('187', plain,
% 1.64/1.83      (![X30 : $i]:
% 1.64/1.83         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.83  thf('188', plain,
% 1.64/1.83      (![X30 : $i]:
% 1.64/1.83         (((k2_struct_0 @ X30) = (u1_struct_0 @ X30)) | ~ (l1_struct_0 @ X30))),
% 1.64/1.83      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.64/1.83  thf('189', plain,
% 1.64/1.83      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83          != (k2_struct_0 @ sk_A)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('split', [status(esa)], ['130'])).
% 1.64/1.83  thf('190', plain,
% 1.64/1.83      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83           != (k2_struct_0 @ sk_A))
% 1.64/1.83         | ~ (l1_struct_0 @ sk_B)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('sup-', [status(thm)], ['188', '189'])).
% 1.64/1.83  thf('191', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.83  thf('192', plain,
% 1.64/1.83      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83          != (k2_struct_0 @ sk_A)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('demod', [status(thm)], ['190', '191'])).
% 1.64/1.83  thf('193', plain,
% 1.64/1.83      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83           != (k2_struct_0 @ sk_A))
% 1.64/1.83         | ~ (l1_struct_0 @ sk_B)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('sup-', [status(thm)], ['187', '192'])).
% 1.64/1.83  thf('194', plain, ((l1_struct_0 @ sk_B)),
% 1.64/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.83  thf('195', plain,
% 1.64/1.83      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83          != (k2_struct_0 @ sk_A)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('demod', [status(thm)], ['193', '194'])).
% 1.64/1.83  thf('196', plain,
% 1.64/1.83      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.64/1.83          != (k2_struct_0 @ sk_A)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('sup-', [status(thm)], ['186', '195'])).
% 1.64/1.83  thf('197', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 1.64/1.83      inference('sup+', [status(thm)], ['11', '12'])).
% 1.64/1.83  thf('198', plain,
% 1.64/1.83      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.64/1.83          != (k2_struct_0 @ sk_A)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('demod', [status(thm)], ['196', '197'])).
% 1.64/1.83  thf('199', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.64/1.83      inference('demod', [status(thm)], ['144', '145', '148'])).
% 1.64/1.83  thf('200', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 1.64/1.83      inference('demod', [status(thm)], ['144', '145', '148'])).
% 1.64/1.83  thf('201', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 1.64/1.83      inference('demod', [status(thm)], ['49', '52', '55'])).
% 1.64/1.83  thf('202', plain,
% 1.64/1.83      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.83          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 1.64/1.83          != (k1_relat_1 @ sk_C)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('demod', [status(thm)], ['198', '199', '200', '201'])).
% 1.64/1.83  thf('203', plain,
% 1.64/1.83      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.83          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('sup-', [status(thm)], ['185', '202'])).
% 1.64/1.83  thf('204', plain,
% 1.64/1.83      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('sup-', [status(thm)], ['176', '203'])).
% 1.64/1.83  thf('205', plain,
% 1.64/1.83      (((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))
% 1.64/1.83         | ~ (v1_relat_1 @ sk_C)
% 1.64/1.83         | ~ (v1_funct_1 @ sk_C)
% 1.64/1.83         | ~ (v2_funct_1 @ sk_C)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('sup-', [status(thm)], ['173', '204'])).
% 1.64/1.83  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 1.64/1.83      inference('sup-', [status(thm)], ['50', '51'])).
% 1.64/1.83  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 1.64/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.83  thf('208', plain, ((v2_funct_1 @ sk_C)),
% 1.64/1.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.64/1.83  thf('209', plain,
% 1.64/1.83      ((((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))
% 1.64/1.83         <= (~
% 1.64/1.83             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83                = (k2_struct_0 @ sk_A))))),
% 1.64/1.83      inference('demod', [status(thm)], ['205', '206', '207', '208'])).
% 1.64/1.83  thf('210', plain,
% 1.64/1.83      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83          = (k2_struct_0 @ sk_A)))),
% 1.64/1.83      inference('simplify', [status(thm)], ['209'])).
% 1.64/1.83  thf('211', plain,
% 1.64/1.83      (~
% 1.64/1.83       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83          = (k2_struct_0 @ sk_B))) | 
% 1.64/1.83       ~
% 1.64/1.83       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83          = (k2_struct_0 @ sk_A)))),
% 1.64/1.83      inference('split', [status(esa)], ['130'])).
% 1.64/1.83  thf('212', plain,
% 1.64/1.83      (~
% 1.64/1.83       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 1.64/1.83          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 1.64/1.83          = (k2_struct_0 @ sk_B)))),
% 1.64/1.83      inference('sat_resolution*', [status(thm)], ['210', '211'])).
% 1.64/1.83  thf('213', plain,
% 1.64/1.83      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 1.64/1.83         (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C))),
% 1.64/1.83      inference('simpl_trail', [status(thm)], ['172', '212'])).
% 1.64/1.83  thf('214', plain, ($false),
% 1.64/1.83      inference('simplify_reflect-', [status(thm)], ['126', '213'])).
% 1.64/1.83  
% 1.64/1.83  % SZS output end Refutation
% 1.64/1.83  
% 1.66/1.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
