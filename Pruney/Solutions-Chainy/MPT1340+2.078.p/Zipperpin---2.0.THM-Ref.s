%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0FEC0D5Zh4

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:20 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  299 (3864 expanded)
%              Number of leaves         :   39 (1128 expanded)
%              Depth                    :   43
%              Number of atoms          : 2573 (83519 expanded)
%              Number of equality atoms :  113 (2329 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
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

thf('4',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['5','10','11'])).

thf('13',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('29',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X26: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X26 ) )
      | ~ ( l1_struct_0 @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','37'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('39',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('45',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48'])).

thf('52',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['12','49','50','51'])).

thf('53',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['53','58'])).

thf('60',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('63',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('66',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('73',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('74',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75'])).

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

thf('77',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('78',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('81',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('82',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('90',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('95',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('96',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['94','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('104',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('105',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('107',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['78','79','92','93','107'])).

thf('109',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['52','109'])).

thf('111',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','110'])).

thf('112',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('113',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','114'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('117',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['115','116','117'])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('119',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('120',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75'])).

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

thf('121',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('122',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('125',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('126',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X27 @ X29 )
       != X27 )
      | ~ ( v2_funct_1 @ X29 )
      | ( ( k2_tops_2 @ X28 @ X27 @ X29 )
        = ( k2_funct_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X28 @ X27 )
      | ~ ( v1_funct_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('130',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('132',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('134',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('136',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('139',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('140',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('142',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('145',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','137','140','145','146'])).

thf('148',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['131','147'])).

thf('149',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('150',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75'])).

thf('154',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k2_relset_1 @ X24 @ X23 @ X22 )
       != X23 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X22 ) @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('155',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('158',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('159',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['155','156','157','158','159'])).

thf('161',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['130','152','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('164',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k2_relset_1 @ X11 @ X12 @ X10 )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('165',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('166',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('167',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('168',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('169',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('170',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('171',plain,(
    ! [X4: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('172',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('173',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('174',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['70','71','74'])).

thf('175',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('176',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X4 ) )
      | ~ ( v2_funct_1 @ X4 )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('177',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('178',plain,(
    ! [X6: $i] :
      ( ~ ( v2_funct_1 @ X6 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X6 ) )
        = X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('179',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('180',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_relat_1 @ X17 )
       != X16 )
      | ( v1_partfun1 @ X17 @ X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('181',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v4_relat_1 @ X17 @ ( k1_relat_1 @ X17 ) )
      | ( v1_partfun1 @ X17 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['179','181'])).

thf('183',plain,(
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
    inference('sup-',[status(thm)],['178','182'])).

thf('184',plain,(
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
    inference('sup-',[status(thm)],['177','183'])).

thf('185',plain,(
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
    inference(simplify,[status(thm)],['184'])).

thf('186',plain,(
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
    inference('sup-',[status(thm)],['176','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['175','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('190',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['188','189','190','191'])).

thf('193',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('194',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['192','193'])).

thf('195',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['172','194'])).

thf('196',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['171','199'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['200','201','202','203'])).

thf('205',plain,
    ( ( v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['170','204'])).

thf('206',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('207',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('209',plain,(
    v1_partfun1 @ sk_C @ ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['205','206','207','208'])).

thf('210',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['169','209'])).

thf('211',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['151'])).

thf('212',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['168','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('215',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['213','214','215','216'])).

thf('218',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['167','217'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('220',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    v1_partfun1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['218','219','220','221'])).

thf('223',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v1_partfun1 @ X17 @ X16 )
      | ( ( k1_relat_1 @ X17 )
        = X16 )
      | ~ ( v4_relat_1 @ X17 @ X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('224',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('226',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,
    ( ~ ( v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['166','226'])).

thf('228',plain,(
    v4_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['173','174'])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['227','228','229','230','231'])).

thf('233',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['165','232'])).

thf('234',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['162','233'])).

thf('235',plain,
    ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['119','235'])).

thf('237',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('238',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['236','237','238','239'])).

thf('241',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['118','240'])).

thf('242',plain,
    ( ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','241'])).

thf('243',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( u1_struct_0 @ X25 ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('244',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

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

thf('245',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_funct_2 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('246',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_funct_2 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['244','246'])).

thf('248',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('249',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['247','248','249'])).

thf('251',plain,
    ( ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['243','250'])).

thf('252',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('253',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['251','252','253'])).

thf('255',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('256',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('257',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    $false ),
    inference(demod,[status(thm)],['242','254','255','256','257'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0FEC0D5Zh4
% 0.14/0.37  % Computer   : n002.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 17:33:52 EST 2020
% 0.14/0.38  % CPUTime    : 
% 0.14/0.38  % Running portfolio for 600 s
% 0.14/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 294 iterations in 0.111s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.24/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.56  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.24/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.24/0.56  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.24/0.56  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.24/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.24/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.24/0.56  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.24/0.56  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.24/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.24/0.56  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.24/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.56  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.24/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.56  thf(t65_funct_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.56       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.24/0.56  thf('0', plain,
% 0.24/0.56      (![X6 : $i]:
% 0.24/0.56         (~ (v2_funct_1 @ X6)
% 0.24/0.56          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.24/0.56          | ~ (v1_funct_1 @ X6)
% 0.24/0.56          | ~ (v1_relat_1 @ X6))),
% 0.24/0.56      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.24/0.56  thf(d3_struct_0, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.24/0.56  thf('1', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('2', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('3', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf(t64_tops_2, conjecture,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( l1_struct_0 @ A ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.24/0.56           ( ![C:$i]:
% 0.24/0.56             ( ( ( v1_funct_1 @ C ) & 
% 0.24/0.56                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.56                 ( m1_subset_1 @
% 0.24/0.56                   C @ 
% 0.24/0.56                   ( k1_zfmisc_1 @
% 0.24/0.56                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.56               ( ( ( ( k2_relset_1 @
% 0.24/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.24/0.56                     ( k2_struct_0 @ B ) ) & 
% 0.24/0.56                   ( v2_funct_1 @ C ) ) =>
% 0.24/0.56                 ( r2_funct_2 @
% 0.24/0.56                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.24/0.56                   ( k2_tops_2 @
% 0.24/0.56                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.24/0.56                     ( k2_tops_2 @
% 0.24/0.56                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.24/0.56                   C ) ) ) ) ) ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ![A:$i]:
% 0.24/0.56        ( ( l1_struct_0 @ A ) =>
% 0.24/0.56          ( ![B:$i]:
% 0.24/0.56            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.24/0.56              ( ![C:$i]:
% 0.24/0.56                ( ( ( v1_funct_1 @ C ) & 
% 0.24/0.56                    ( v1_funct_2 @
% 0.24/0.56                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.24/0.56                    ( m1_subset_1 @
% 0.24/0.56                      C @ 
% 0.24/0.56                      ( k1_zfmisc_1 @
% 0.24/0.56                        ( k2_zfmisc_1 @
% 0.24/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.24/0.56                  ( ( ( ( k2_relset_1 @
% 0.24/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.24/0.56                        ( k2_struct_0 @ B ) ) & 
% 0.24/0.56                      ( v2_funct_1 @ C ) ) =>
% 0.24/0.56                    ( r2_funct_2 @
% 0.24/0.56                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.24/0.56                      ( k2_tops_2 @
% 0.24/0.56                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.24/0.56                        ( k2_tops_2 @
% 0.24/0.56                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.24/0.56                      C ) ) ) ) ) ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.24/0.56  thf('4', plain,
% 0.24/0.56      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.24/0.56          sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('5', plain,
% 0.24/0.56      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.56            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.24/0.56           sk_C)
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.56  thf('6', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.24/0.56  thf('7', plain,
% 0.24/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.56         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.24/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.24/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.24/0.56  thf('8', plain,
% 0.24/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56         = (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.24/0.56  thf('9', plain,
% 0.24/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56         = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('10', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('11', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('12', plain,
% 0.24/0.56      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.24/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.24/0.56          sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['5', '10', '11'])).
% 0.24/0.56  thf('13', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('14', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('15', plain,
% 0.24/0.56      (((m1_subset_1 @ sk_C @ 
% 0.24/0.56         (k1_zfmisc_1 @ 
% 0.24/0.56          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['13', '14'])).
% 0.24/0.56  thf('16', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('17', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.24/0.56      inference('demod', [status(thm)], ['15', '16'])).
% 0.24/0.56  thf('18', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('19', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.24/0.56      inference('demod', [status(thm)], ['17', '18'])).
% 0.24/0.56  thf(cc5_funct_2, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.24/0.56       ( ![C:$i]:
% 0.24/0.56         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.56           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.24/0.56             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.24/0.56  thf('20', plain,
% 0.24/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.24/0.56         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.24/0.56          | (v1_partfun1 @ X13 @ X14)
% 0.24/0.56          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.24/0.56          | ~ (v1_funct_1 @ X13)
% 0.24/0.56          | (v1_xboole_0 @ X15))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.24/0.56  thf('21', plain,
% 0.24/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.24/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.56        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.24/0.56        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.24/0.56  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('24', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('25', plain,
% 0.24/0.56      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['23', '24'])).
% 0.24/0.56  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('27', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['25', '26'])).
% 0.24/0.56  thf('28', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('29', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['27', '28'])).
% 0.24/0.56  thf('30', plain,
% 0.24/0.56      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.24/0.56        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.24/0.56      inference('demod', [status(thm)], ['21', '22', '29'])).
% 0.24/0.56  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf(fc5_struct_0, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.24/0.56       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.24/0.56  thf('32', plain,
% 0.24/0.56      (![X26 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ (k2_struct_0 @ X26))
% 0.24/0.56          | ~ (l1_struct_0 @ X26)
% 0.24/0.56          | (v2_struct_0 @ X26))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.24/0.56  thf('33', plain,
% 0.24/0.56      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.24/0.56        | (v2_struct_0 @ sk_B)
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.56  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('35', plain,
% 0.24/0.56      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['33', '34'])).
% 0.24/0.56  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('37', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('clc', [status(thm)], ['35', '36'])).
% 0.24/0.56  thf('38', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('clc', [status(thm)], ['30', '37'])).
% 0.24/0.56  thf(d4_partfun1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.24/0.56       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.24/0.56  thf('39', plain,
% 0.24/0.56      (![X16 : $i, X17 : $i]:
% 0.24/0.56         (~ (v1_partfun1 @ X17 @ X16)
% 0.24/0.56          | ((k1_relat_1 @ X17) = (X16))
% 0.24/0.56          | ~ (v4_relat_1 @ X17 @ X16)
% 0.24/0.56          | ~ (v1_relat_1 @ X17))),
% 0.24/0.56      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.24/0.56  thf('40', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.56        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.24/0.56        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['38', '39'])).
% 0.24/0.56  thf('41', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(cc2_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.24/0.56  thf('42', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.24/0.56          | (v1_relat_1 @ X0)
% 0.24/0.56          | ~ (v1_relat_1 @ X1))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.24/0.56  thf('43', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ 
% 0.24/0.56           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.24/0.56        | (v1_relat_1 @ sk_C))),
% 0.24/0.56      inference('sup-', [status(thm)], ['41', '42'])).
% 0.24/0.56  thf(fc6_relat_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.24/0.56  thf('44', plain,
% 0.24/0.56      (![X2 : $i, X3 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X2 @ X3))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.24/0.56  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.56  thf('46', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf(cc2_relset_1, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.24/0.56  thf('47', plain,
% 0.24/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.56         ((v4_relat_1 @ X7 @ X8)
% 0.24/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.24/0.56  thf('48', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.24/0.56  thf('49', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['40', '45', '48'])).
% 0.24/0.56  thf('50', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['40', '45', '48'])).
% 0.24/0.56  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['40', '45', '48'])).
% 0.24/0.56  thf('52', plain,
% 0.24/0.56      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.56           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.24/0.56          sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['12', '49', '50', '51'])).
% 0.24/0.56  thf('53', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('54', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('55', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('56', plain,
% 0.24/0.56      (((m1_subset_1 @ sk_C @ 
% 0.24/0.56         (k1_zfmisc_1 @ 
% 0.24/0.56          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup+', [status(thm)], ['54', '55'])).
% 0.24/0.56  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('58', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.24/0.56  thf('59', plain,
% 0.24/0.56      (((m1_subset_1 @ sk_C @ 
% 0.24/0.56         (k1_zfmisc_1 @ 
% 0.24/0.56          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['53', '58'])).
% 0.24/0.56  thf('60', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('61', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.24/0.56      inference('demod', [status(thm)], ['59', '60'])).
% 0.24/0.56  thf('62', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('63', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.24/0.56      inference('demod', [status(thm)], ['61', '62'])).
% 0.24/0.56  thf('64', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('65', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.24/0.56      inference('clc', [status(thm)], ['30', '37'])).
% 0.24/0.56  thf('66', plain,
% 0.24/0.56      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup+', [status(thm)], ['64', '65'])).
% 0.24/0.56  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('68', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['66', '67'])).
% 0.24/0.56  thf('69', plain,
% 0.24/0.56      (![X16 : $i, X17 : $i]:
% 0.24/0.56         (~ (v1_partfun1 @ X17 @ X16)
% 0.24/0.56          | ((k1_relat_1 @ X17) = (X16))
% 0.24/0.56          | ~ (v4_relat_1 @ X17 @ X16)
% 0.24/0.56          | ~ (v1_relat_1 @ X17))),
% 0.24/0.56      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.24/0.56  thf('70', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.56        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.24/0.56        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['68', '69'])).
% 0.24/0.56  thf('71', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.56  thf('72', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.24/0.56  thf('73', plain,
% 0.24/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.56         ((v4_relat_1 @ X7 @ X8)
% 0.24/0.56          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.24/0.56  thf('74', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup-', [status(thm)], ['72', '73'])).
% 0.24/0.56  thf('75', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.24/0.56  thf('76', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.24/0.56      inference('demod', [status(thm)], ['63', '75'])).
% 0.24/0.56  thf(d4_tops_2, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.56       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.24/0.56         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.24/0.56  thf('77', plain,
% 0.24/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.24/0.56         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.24/0.56          | ~ (v2_funct_1 @ X29)
% 0.24/0.56          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.24/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.24/0.56          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.24/0.56          | ~ (v1_funct_1 @ X29))),
% 0.24/0.56      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.24/0.56  thf('78', plain,
% 0.24/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.24/0.56        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.24/0.56        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.56            = (k2_funct_1 @ sk_C))
% 0.24/0.56        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.56        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.56            != (k2_relat_1 @ sk_C)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.24/0.56  thf('79', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('80', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('81', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('82', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('83', plain,
% 0.24/0.56      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup+', [status(thm)], ['81', '82'])).
% 0.24/0.56  thf('84', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('85', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['83', '84'])).
% 0.24/0.56  thf('86', plain,
% 0.24/0.56      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['80', '85'])).
% 0.24/0.56  thf('87', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('88', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['86', '87'])).
% 0.24/0.56  thf('89', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('90', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.24/0.56  thf('91', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.24/0.56  thf('92', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['90', '91'])).
% 0.24/0.56  thf('93', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('94', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('95', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('96', plain,
% 0.24/0.56      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56         = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('97', plain,
% 0.24/0.56      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56          = (k2_struct_0 @ sk_B))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_A))),
% 0.24/0.56      inference('sup+', [status(thm)], ['95', '96'])).
% 0.24/0.56  thf('98', plain, ((l1_struct_0 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('99', plain,
% 0.24/0.56      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56         = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['97', '98'])).
% 0.24/0.56  thf('100', plain,
% 0.24/0.56      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56          = (k2_struct_0 @ sk_B))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['94', '99'])).
% 0.24/0.56  thf('101', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('102', plain,
% 0.24/0.56      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56         = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['100', '101'])).
% 0.24/0.56  thf('103', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('104', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('105', plain,
% 0.24/0.56      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.56         = (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['102', '103', '104'])).
% 0.24/0.56  thf('106', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.24/0.56  thf('107', plain,
% 0.24/0.56      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.56         = (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.24/0.56  thf('108', plain,
% 0.24/0.56      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.56          = (k2_funct_1 @ sk_C))
% 0.24/0.56        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.24/0.56      inference('demod', [status(thm)], ['78', '79', '92', '93', '107'])).
% 0.24/0.56  thf('109', plain,
% 0.24/0.56      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.56         = (k2_funct_1 @ sk_C))),
% 0.24/0.56      inference('simplify', [status(thm)], ['108'])).
% 0.24/0.56  thf('110', plain,
% 0.24/0.56      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.24/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.56           (k2_funct_1 @ sk_C)) @ 
% 0.24/0.56          sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['52', '109'])).
% 0.24/0.56  thf('111', plain,
% 0.24/0.56      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ 
% 0.24/0.56           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.56            (k2_funct_1 @ sk_C)) @ 
% 0.24/0.56           sk_C)
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['2', '110'])).
% 0.24/0.56  thf('112', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('113', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('114', plain,
% 0.24/0.56      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.24/0.56          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.56           (k2_funct_1 @ sk_C)) @ 
% 0.24/0.56          sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.24/0.56  thf('115', plain,
% 0.24/0.56      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.24/0.56           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.56            (k2_funct_1 @ sk_C)) @ 
% 0.24/0.56           sk_C)
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup-', [status(thm)], ['1', '114'])).
% 0.24/0.56  thf('116', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('117', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('118', plain,
% 0.24/0.56      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.24/0.56          (k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.56           (k2_funct_1 @ sk_C)) @ 
% 0.24/0.56          sk_C)),
% 0.24/0.56      inference('demod', [status(thm)], ['115', '116', '117'])).
% 0.24/0.56  thf(fc6_funct_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.24/0.56       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.24/0.56         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.24/0.56         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.24/0.56  thf('119', plain,
% 0.24/0.56      (![X4 : $i]:
% 0.24/0.56         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.24/0.56          | ~ (v2_funct_1 @ X4)
% 0.24/0.56          | ~ (v1_funct_1 @ X4)
% 0.24/0.56          | ~ (v1_relat_1 @ X4))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.24/0.56  thf('120', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.24/0.56      inference('demod', [status(thm)], ['63', '75'])).
% 0.24/0.56  thf(t31_funct_2, axiom,
% 0.24/0.56    (![A:$i,B:$i,C:$i]:
% 0.24/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.56         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.56       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.24/0.56         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.24/0.56           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.24/0.56           ( m1_subset_1 @
% 0.24/0.56             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.24/0.56  thf('121', plain,
% 0.24/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.24/0.56         (~ (v2_funct_1 @ X22)
% 0.24/0.56          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.24/0.56          | (m1_subset_1 @ (k2_funct_1 @ X22) @ 
% 0.24/0.56             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.24/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.24/0.56          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.24/0.56          | ~ (v1_funct_1 @ X22))),
% 0.24/0.56      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.24/0.56  thf('122', plain,
% 0.24/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.24/0.56        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.24/0.56        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.56           (k1_zfmisc_1 @ 
% 0.24/0.56            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.24/0.56        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.56            != (k2_relat_1 @ sk_C))
% 0.24/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.24/0.56      inference('sup-', [status(thm)], ['120', '121'])).
% 0.24/0.56  thf('123', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('124', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['90', '91'])).
% 0.24/0.56  thf('125', plain,
% 0.24/0.56      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.56         = (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['105', '106'])).
% 0.24/0.56  thf('126', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('127', plain,
% 0.24/0.56      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.56         (k1_zfmisc_1 @ 
% 0.24/0.56          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.24/0.56        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.24/0.56      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.24/0.56  thf('128', plain,
% 0.24/0.56      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.24/0.56      inference('simplify', [status(thm)], ['127'])).
% 0.24/0.56  thf('129', plain,
% 0.24/0.56      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.24/0.56         (((k2_relset_1 @ X28 @ X27 @ X29) != (X27))
% 0.24/0.56          | ~ (v2_funct_1 @ X29)
% 0.24/0.56          | ((k2_tops_2 @ X28 @ X27 @ X29) = (k2_funct_1 @ X29))
% 0.24/0.56          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27)))
% 0.24/0.56          | ~ (v1_funct_2 @ X29 @ X28 @ X27)
% 0.24/0.56          | ~ (v1_funct_1 @ X29))),
% 0.24/0.56      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.24/0.56  thf('130', plain,
% 0.24/0.56      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.56        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.24/0.56             (k1_relat_1 @ sk_C))
% 0.24/0.56        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.56            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.24/0.56        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.56        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.56            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['128', '129'])).
% 0.24/0.56  thf('131', plain,
% 0.24/0.56      (![X25 : $i]:
% 0.24/0.56         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.56  thf('132', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.24/0.56  thf('133', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.24/0.56  thf('134', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('demod', [status(thm)], ['132', '133'])).
% 0.24/0.56  thf('135', plain,
% 0.24/0.56      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.24/0.56         (~ (v2_funct_1 @ X22)
% 0.24/0.56          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.24/0.56          | (v1_funct_1 @ (k2_funct_1 @ X22))
% 0.24/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.24/0.56          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.24/0.56          | ~ (v1_funct_1 @ X22))),
% 0.24/0.56      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.24/0.56  thf('136', plain,
% 0.24/0.56      ((~ (v1_funct_1 @ sk_C)
% 0.24/0.56        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.24/0.56        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.56        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56            != (u1_struct_0 @ sk_B))
% 0.24/0.56        | ~ (v2_funct_1 @ sk_C))),
% 0.24/0.56      inference('sup-', [status(thm)], ['134', '135'])).
% 0.24/0.56  thf('137', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('138', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['83', '84'])).
% 0.24/0.56  thf('139', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.24/0.56  thf('140', plain,
% 0.24/0.56      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.24/0.56      inference('demod', [status(thm)], ['138', '139'])).
% 0.24/0.56  thf('141', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.56      inference('demod', [status(thm)], ['56', '57'])).
% 0.24/0.56  thf('142', plain,
% 0.24/0.56      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.56         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.24/0.56          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.24/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.24/0.56  thf('143', plain,
% 0.24/0.56      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56         = (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('sup-', [status(thm)], ['141', '142'])).
% 0.24/0.56  thf('144', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.24/0.56      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.24/0.56  thf('145', plain,
% 0.24/0.56      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.24/0.56         = (k2_relat_1 @ sk_C))),
% 0.24/0.56      inference('demod', [status(thm)], ['143', '144'])).
% 0.24/0.56  thf('146', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('147', plain,
% 0.24/0.56      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.56        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.24/0.56      inference('demod', [status(thm)], ['136', '137', '140', '145', '146'])).
% 0.24/0.56  thf('148', plain,
% 0.24/0.56      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.24/0.56        | ~ (l1_struct_0 @ sk_B)
% 0.24/0.56        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['131', '147'])).
% 0.24/0.56  thf('149', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.56      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.56  thf('150', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('151', plain,
% 0.24/0.56      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.24/0.56        | (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.56      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.24/0.56  thf('152', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.24/0.56      inference('simplify', [status(thm)], ['151'])).
% 0.24/0.56  thf('153', plain,
% 0.24/0.56      ((m1_subset_1 @ sk_C @ 
% 0.24/0.56        (k1_zfmisc_1 @ 
% 0.24/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.24/0.56      inference('demod', [status(thm)], ['63', '75'])).
% 0.24/0.57  thf('154', plain,
% 0.24/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.24/0.57         (~ (v2_funct_1 @ X22)
% 0.24/0.57          | ((k2_relset_1 @ X24 @ X23 @ X22) != (X23))
% 0.24/0.57          | (v1_funct_2 @ (k2_funct_1 @ X22) @ X23 @ X24)
% 0.24/0.57          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.24/0.57          | ~ (v1_funct_2 @ X22 @ X24 @ X23)
% 0.24/0.57          | ~ (v1_funct_1 @ X22))),
% 0.24/0.57      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.24/0.57  thf('155', plain,
% 0.24/0.57      ((~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.24/0.57        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.24/0.57           (k1_relat_1 @ sk_C))
% 0.24/0.57        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.57            != (k2_relat_1 @ sk_C))
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.24/0.57      inference('sup-', [status(thm)], ['153', '154'])).
% 0.24/0.57  thf('156', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('157', plain,
% 0.24/0.57      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['90', '91'])).
% 0.24/0.57  thf('158', plain,
% 0.24/0.57      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.24/0.57         = (k2_relat_1 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['105', '106'])).
% 0.24/0.57  thf('159', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('160', plain,
% 0.24/0.57      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.24/0.57         (k1_relat_1 @ sk_C))
% 0.24/0.57        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.24/0.57      inference('demod', [status(thm)], ['155', '156', '157', '158', '159'])).
% 0.24/0.57  thf('161', plain,
% 0.24/0.57      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.24/0.57        (k1_relat_1 @ sk_C))),
% 0.24/0.57      inference('simplify', [status(thm)], ['160'])).
% 0.24/0.57  thf('162', plain,
% 0.24/0.57      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.57          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.57            (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.24/0.57      inference('demod', [status(thm)], ['130', '152', '161'])).
% 0.24/0.57  thf('163', plain,
% 0.24/0.57      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.24/0.57        (k1_zfmisc_1 @ 
% 0.24/0.57         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.24/0.57      inference('simplify', [status(thm)], ['127'])).
% 0.24/0.57  thf('164', plain,
% 0.24/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.57         (((k2_relset_1 @ X11 @ X12 @ X10) = (k2_relat_1 @ X10))
% 0.24/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.24/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.24/0.57  thf('165', plain,
% 0.24/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.57         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['163', '164'])).
% 0.24/0.57  thf(t55_funct_1, axiom,
% 0.24/0.57    (![A:$i]:
% 0.24/0.57     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.24/0.57       ( ( v2_funct_1 @ A ) =>
% 0.24/0.57         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.24/0.57           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.24/0.57  thf('166', plain,
% 0.24/0.57      (![X5 : $i]:
% 0.24/0.57         (~ (v2_funct_1 @ X5)
% 0.24/0.57          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.24/0.57          | ~ (v1_funct_1 @ X5)
% 0.24/0.57          | ~ (v1_relat_1 @ X5))),
% 0.24/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.24/0.57  thf('167', plain,
% 0.24/0.57      (![X4 : $i]:
% 0.24/0.57         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.24/0.57          | ~ (v2_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_relat_1 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.24/0.57  thf('168', plain,
% 0.24/0.57      (![X4 : $i]:
% 0.24/0.57         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.24/0.57          | ~ (v2_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_relat_1 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.24/0.57  thf('169', plain,
% 0.24/0.57      (![X5 : $i]:
% 0.24/0.57         (~ (v2_funct_1 @ X5)
% 0.24/0.57          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.24/0.57          | ~ (v1_funct_1 @ X5)
% 0.24/0.57          | ~ (v1_relat_1 @ X5))),
% 0.24/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.24/0.57  thf('170', plain,
% 0.24/0.57      (![X6 : $i]:
% 0.24/0.57         (~ (v2_funct_1 @ X6)
% 0.24/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.24/0.57          | ~ (v1_funct_1 @ X6)
% 0.24/0.57          | ~ (v1_relat_1 @ X6))),
% 0.24/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.24/0.57  thf('171', plain,
% 0.24/0.57      (![X4 : $i]:
% 0.24/0.57         ((v2_funct_1 @ (k2_funct_1 @ X4))
% 0.24/0.57          | ~ (v2_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_relat_1 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.24/0.57  thf('172', plain,
% 0.24/0.57      (![X4 : $i]:
% 0.24/0.57         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.24/0.57          | ~ (v2_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_relat_1 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.24/0.57  thf('173', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.24/0.57      inference('sup-', [status(thm)], ['72', '73'])).
% 0.24/0.57  thf('174', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.24/0.57      inference('demod', [status(thm)], ['70', '71', '74'])).
% 0.24/0.57  thf('175', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['173', '174'])).
% 0.24/0.57  thf('176', plain,
% 0.24/0.57      (![X4 : $i]:
% 0.24/0.57         ((v1_relat_1 @ (k2_funct_1 @ X4))
% 0.24/0.57          | ~ (v2_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_funct_1 @ X4)
% 0.24/0.57          | ~ (v1_relat_1 @ X4))),
% 0.24/0.57      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.24/0.57  thf('177', plain,
% 0.24/0.57      (![X5 : $i]:
% 0.24/0.57         (~ (v2_funct_1 @ X5)
% 0.24/0.57          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.24/0.57          | ~ (v1_funct_1 @ X5)
% 0.24/0.57          | ~ (v1_relat_1 @ X5))),
% 0.24/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.24/0.57  thf('178', plain,
% 0.24/0.57      (![X6 : $i]:
% 0.24/0.57         (~ (v2_funct_1 @ X6)
% 0.24/0.57          | ((k2_funct_1 @ (k2_funct_1 @ X6)) = (X6))
% 0.24/0.57          | ~ (v1_funct_1 @ X6)
% 0.24/0.57          | ~ (v1_relat_1 @ X6))),
% 0.24/0.57      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.24/0.57  thf('179', plain,
% 0.24/0.57      (![X5 : $i]:
% 0.24/0.57         (~ (v2_funct_1 @ X5)
% 0.24/0.57          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.24/0.57          | ~ (v1_funct_1 @ X5)
% 0.24/0.57          | ~ (v1_relat_1 @ X5))),
% 0.24/0.57      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.24/0.57  thf('180', plain,
% 0.24/0.57      (![X16 : $i, X17 : $i]:
% 0.24/0.57         (((k1_relat_1 @ X17) != (X16))
% 0.24/0.57          | (v1_partfun1 @ X17 @ X16)
% 0.24/0.57          | ~ (v4_relat_1 @ X17 @ X16)
% 0.24/0.57          | ~ (v1_relat_1 @ X17))),
% 0.24/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.24/0.57  thf('181', plain,
% 0.24/0.57      (![X17 : $i]:
% 0.24/0.57         (~ (v1_relat_1 @ X17)
% 0.24/0.57          | ~ (v4_relat_1 @ X17 @ (k1_relat_1 @ X17))
% 0.24/0.57          | (v1_partfun1 @ X17 @ (k1_relat_1 @ X17)))),
% 0.24/0.57      inference('simplify', [status(thm)], ['180'])).
% 0.24/0.57  thf('182', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         (~ (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.24/0.57          | ~ (v1_relat_1 @ X0)
% 0.24/0.57          | ~ (v1_funct_1 @ X0)
% 0.24/0.57          | ~ (v2_funct_1 @ X0)
% 0.24/0.57          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.24/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['179', '181'])).
% 0.24/0.57  thf('183', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         (~ (v4_relat_1 @ X0 @ (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.24/0.57          | ~ (v1_relat_1 @ X0)
% 0.24/0.57          | ~ (v1_funct_1 @ X0)
% 0.24/0.57          | ~ (v2_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.24/0.57          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.24/0.57             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.24/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['178', '182'])).
% 0.24/0.57  thf('184', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         (~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.24/0.57          | ~ (v1_relat_1 @ X0)
% 0.24/0.57          | ~ (v1_funct_1 @ X0)
% 0.24/0.57          | ~ (v2_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.24/0.57             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.24/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.24/0.57          | ~ (v2_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_relat_1 @ X0))),
% 0.24/0.57      inference('sup-', [status(thm)], ['177', '183'])).
% 0.24/0.57  thf('185', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.24/0.57          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.24/0.57             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.24/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v2_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_relat_1 @ X0)
% 0.24/0.57          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.24/0.57      inference('simplify', [status(thm)], ['184'])).
% 0.24/0.57  thf('186', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.24/0.57          | ~ (v1_relat_1 @ X0)
% 0.24/0.57          | ~ (v1_funct_1 @ X0)
% 0.24/0.57          | ~ (v2_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.24/0.57             (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['176', '185'])).
% 0.24/0.57  thf('187', plain,
% 0.24/0.57      (![X0 : $i]:
% 0.24/0.57         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.24/0.57           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0))))
% 0.24/0.57          | ~ (v2_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_funct_1 @ X0)
% 0.24/0.57          | ~ (v1_relat_1 @ X0)
% 0.24/0.57          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ X0))
% 0.24/0.57          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.24/0.57          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.24/0.57      inference('simplify', [status(thm)], ['186'])).
% 0.24/0.57  thf('188', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.57        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.24/0.57           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['175', '187'])).
% 0.24/0.57  thf('189', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('190', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('191', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('192', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.24/0.57           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.24/0.57      inference('demod', [status(thm)], ['188', '189', '190', '191'])).
% 0.24/0.57  thf('193', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.24/0.57      inference('simplify', [status(thm)], ['151'])).
% 0.24/0.57  thf('194', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.24/0.57           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.24/0.57      inference('demod', [status(thm)], ['192', '193'])).
% 0.24/0.57  thf('195', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.57        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.24/0.57           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.57      inference('sup-', [status(thm)], ['172', '194'])).
% 0.24/0.57  thf('196', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('198', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('199', plain,
% 0.24/0.57      (((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.24/0.57         (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.57      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 0.24/0.57  thf('200', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.57        | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.24/0.57           (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['171', '199'])).
% 0.24/0.57  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('203', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('204', plain,
% 0.24/0.57      ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ 
% 0.24/0.57        (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('demod', [status(thm)], ['200', '201', '202', '203'])).
% 0.24/0.57  thf('205', plain,
% 0.24/0.57      (((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))
% 0.24/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.24/0.57      inference('sup+', [status(thm)], ['170', '204'])).
% 0.24/0.57  thf('206', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('207', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('208', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('209', plain,
% 0.24/0.57      ((v1_partfun1 @ sk_C @ (k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('demod', [status(thm)], ['205', '206', '207', '208'])).
% 0.24/0.57  thf('210', plain,
% 0.24/0.57      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.24/0.57        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.57      inference('sup+', [status(thm)], ['169', '209'])).
% 0.24/0.57  thf('211', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.24/0.57      inference('simplify', [status(thm)], ['151'])).
% 0.24/0.57  thf('212', plain,
% 0.24/0.57      (((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.24/0.57        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.57      inference('demod', [status(thm)], ['210', '211'])).
% 0.24/0.57  thf('213', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['168', '212'])).
% 0.24/0.57  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('215', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('216', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('217', plain,
% 0.24/0.57      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('demod', [status(thm)], ['213', '214', '215', '216'])).
% 0.24/0.57  thf('218', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.57        | (v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['167', '217'])).
% 0.24/0.57  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('220', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('221', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('222', plain,
% 0.24/0.57      ((v1_partfun1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.57      inference('demod', [status(thm)], ['218', '219', '220', '221'])).
% 0.24/0.57  thf('223', plain,
% 0.24/0.57      (![X16 : $i, X17 : $i]:
% 0.24/0.57         (~ (v1_partfun1 @ X17 @ X16)
% 0.24/0.57          | ((k1_relat_1 @ X17) = (X16))
% 0.24/0.57          | ~ (v4_relat_1 @ X17 @ X16)
% 0.24/0.57          | ~ (v1_relat_1 @ X17))),
% 0.24/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.24/0.57  thf('224', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.24/0.57        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['222', '223'])).
% 0.24/0.57  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('226', plain,
% 0.24/0.57      ((~ (v4_relat_1 @ sk_C @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.24/0.57        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('demod', [status(thm)], ['224', '225'])).
% 0.24/0.57  thf('227', plain,
% 0.24/0.57      ((~ (v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))
% 0.24/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.57        | ((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['166', '226'])).
% 0.24/0.57  thf('228', plain, ((v4_relat_1 @ sk_C @ (k1_relat_1 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['173', '174'])).
% 0.24/0.57  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('231', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('232', plain,
% 0.24/0.57      (((k1_relat_1 @ sk_C) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.57      inference('demod', [status(thm)], ['227', '228', '229', '230', '231'])).
% 0.24/0.57  thf('233', plain,
% 0.24/0.57      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.57         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.24/0.57      inference('demod', [status(thm)], ['165', '232'])).
% 0.24/0.57  thf('234', plain,
% 0.24/0.57      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.57          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.24/0.57        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.24/0.57      inference('demod', [status(thm)], ['162', '233'])).
% 0.24/0.57  thf('235', plain,
% 0.24/0.57      ((~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.24/0.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('simplify', [status(thm)], ['234'])).
% 0.24/0.57  thf('236', plain,
% 0.24/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C)
% 0.24/0.57        | ((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.57            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.24/0.57      inference('sup-', [status(thm)], ['119', '235'])).
% 0.24/0.57  thf('237', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('238', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('239', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('240', plain,
% 0.24/0.57      (((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.24/0.57         (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.24/0.57      inference('demod', [status(thm)], ['236', '237', '238', '239'])).
% 0.24/0.57  thf('241', plain,
% 0.24/0.57      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.24/0.57          (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['118', '240'])).
% 0.24/0.57  thf('242', plain,
% 0.24/0.57      ((~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C)
% 0.24/0.57        | ~ (v1_relat_1 @ sk_C)
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | ~ (v2_funct_1 @ sk_C))),
% 0.24/0.57      inference('sup-', [status(thm)], ['0', '241'])).
% 0.24/0.57  thf('243', plain,
% 0.24/0.57      (![X25 : $i]:
% 0.24/0.57         (((k2_struct_0 @ X25) = (u1_struct_0 @ X25)) | ~ (l1_struct_0 @ X25))),
% 0.24/0.57      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.24/0.57  thf('244', plain,
% 0.24/0.57      ((m1_subset_1 @ sk_C @ 
% 0.24/0.57        (k1_zfmisc_1 @ 
% 0.24/0.57         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.24/0.57      inference('demod', [status(thm)], ['132', '133'])).
% 0.24/0.57  thf(redefinition_r2_funct_2, axiom,
% 0.24/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.24/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.24/0.57         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.57       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.24/0.57  thf('245', plain,
% 0.24/0.57      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.24/0.57         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.24/0.57          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.24/0.57          | ~ (v1_funct_1 @ X18)
% 0.24/0.57          | ~ (v1_funct_1 @ X21)
% 0.24/0.57          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.24/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.24/0.57          | (r2_funct_2 @ X19 @ X20 @ X18 @ X21)
% 0.24/0.57          | ((X18) != (X21)))),
% 0.24/0.57      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.24/0.57  thf('246', plain,
% 0.24/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.24/0.57         ((r2_funct_2 @ X19 @ X20 @ X21 @ X21)
% 0.24/0.57          | ~ (v1_funct_1 @ X21)
% 0.24/0.57          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.24/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.24/0.57      inference('simplify', [status(thm)], ['245'])).
% 0.24/0.57  thf('247', plain,
% 0.24/0.57      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.24/0.57        | ~ (v1_funct_1 @ sk_C)
% 0.24/0.57        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.24/0.57           sk_C))),
% 0.24/0.57      inference('sup-', [status(thm)], ['244', '246'])).
% 0.24/0.57  thf('248', plain,
% 0.24/0.57      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.24/0.57      inference('demod', [status(thm)], ['138', '139'])).
% 0.24/0.57  thf('249', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('250', plain,
% 0.24/0.57      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['247', '248', '249'])).
% 0.24/0.57  thf('251', plain,
% 0.24/0.57      (((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.24/0.57        | ~ (l1_struct_0 @ sk_B))),
% 0.24/0.57      inference('sup+', [status(thm)], ['243', '250'])).
% 0.24/0.57  thf('252', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.24/0.57      inference('sup+', [status(thm)], ['8', '9'])).
% 0.24/0.57  thf('253', plain, ((l1_struct_0 @ sk_B)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('254', plain,
% 0.24/0.57      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['251', '252', '253'])).
% 0.24/0.57  thf('255', plain, ((v1_relat_1 @ sk_C)),
% 0.24/0.57      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.57  thf('256', plain, ((v1_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('257', plain, ((v2_funct_1 @ sk_C)),
% 0.24/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.57  thf('258', plain, ($false),
% 0.24/0.57      inference('demod', [status(thm)], ['242', '254', '255', '256', '257'])).
% 0.24/0.57  
% 0.24/0.57  % SZS output end Refutation
% 0.24/0.57  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
