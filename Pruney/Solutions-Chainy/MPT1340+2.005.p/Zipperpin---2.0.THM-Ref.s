%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m3DjugI2EE

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:05 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  279 (3260 expanded)
%              Number of leaves         :   45 ( 951 expanded)
%              Depth                    :   22
%              Number of atoms          : 2448 (72036 expanded)
%              Number of equality atoms :  139 (2037 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(k3_relset_1_type,type,(
    k3_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('2',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
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
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
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

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X25 )
      | ~ ( v1_funct_1 @ X23 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('28',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('33',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('36',plain,(
    ! [X36: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','41'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('43',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('49',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('50',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('52',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('53',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('54',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['34','41'])).

thf('55',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_partfun1 @ X27 @ X26 )
      | ( ( k1_relat_1 @ X27 )
        = X26 )
      | ~ ( v4_relat_1 @ X27 @ X26 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('61',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v4_relat_1 @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('69',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('71',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['12','51','52','68','69','70'])).

thf('72',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('74',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

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

thf('81',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X37 @ X39 )
       != X37 )
      | ~ ( v2_funct_1 @ X39 )
      | ( ( k2_tops_2 @ X38 @ X37 @ X39 )
        = ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('82',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('85',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('86',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['84','89'])).

thf('91',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('94',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('96',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ A )
          = ( k4_relat_1 @ A ) ) ) ) )).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_funct_1 @ X0 )
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d9_funct_1])).

thf('99',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k2_funct_1 @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('103',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('106',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('107',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['105','110'])).

thf('112',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('115',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('116',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['113','114','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('118',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['82','83','96','103','104','118'])).

thf('120',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ~ ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['71','120'])).

thf('122',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('123',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k3_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) )).

thf('124',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k3_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_relset_1])).

thf('125',plain,(
    m1_subset_1 @ ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k3_relset_1 @ A @ B @ C )
        = ( k4_relat_1 @ C ) ) ) )).

thf('127',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k3_relset_1 @ X18 @ X19 @ X17 )
        = ( k4_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('128',plain,
    ( ( k3_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['125','128'])).

thf('130',plain,
    ( ( m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['122','129'])).

thf('131',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('134',plain,(
    m1_subset_1 @ ( k4_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X37 @ X39 )
       != X37 )
      | ~ ( v2_funct_1 @ X39 )
      | ( ( k2_tops_2 @ X38 @ X37 @ X39 )
        = ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('136',plain,
    ( ~ ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) ) )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

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

thf('138',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('139',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('142',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('143',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('144',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v1_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['139','140','141','142','143','144'])).

thf('146',plain,(
    v1_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('148',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('149',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X32 ) @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('152',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('155',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('156',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('158',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('159',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('160',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('162',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['152','153','156','157','162','163'])).

thf('165',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['147','164'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('167',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['165','166','167'])).

thf('169',plain,(
    v1_funct_2 @ ( k4_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('171',plain,(
    ! [X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X1 ) )
        = X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf('172',plain,
    ( ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['170','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['45','46'])).

thf('174',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['172','173','174','175'])).

thf('177',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(t24_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('178',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X20 @ ( k3_relset_1 @ X20 @ X21 @ X22 ) )
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_relset_1])).

thf('179',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('181',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k3_relset_1 @ X18 @ X19 @ X17 )
        = ( k4_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_relset_1])).

thf('182',plain,
    ( ( k3_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('184',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('185',plain,
    ( ( k1_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','182','185'])).

thf('187',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','67'])).

thf('188',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
      = sk_C )
    | ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['136','146','169','176','188'])).

thf('190',plain,
    ( ~ ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
      = sk_C ) ),
    inference(simplify,[status(thm)],['189'])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('192',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf(t63_tops_2,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_struct_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) )).

thf('193',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( l1_struct_0 @ X40 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X40 ) @ X42 )
       != ( k2_struct_0 @ X40 ) )
      | ~ ( v2_funct_1 @ X42 )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X40 ) @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X40 ) ) ) )
      | ~ ( v1_funct_2 @ X42 @ ( u1_struct_0 @ X41 ) @ ( u1_struct_0 @ X40 ) )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( l1_struct_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t63_tops_2])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('197',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('198',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','47','50'])).

thf('199',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ X0 ) @ X1 )
       != ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['194','195','196','197','198'])).

thf('200',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( v2_funct_1 @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['191','199'])).

thf('201',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('203',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('204',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('206',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('207',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X37 @ X39 )
       != X37 )
      | ~ ( v2_funct_1 @ X39 )
      | ( ( k2_tops_2 @ X38 @ X37 @ X39 )
        = ( k2_funct_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('208',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('211',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('212',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('214',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['208','209','210','211','212','213'])).

thf('215',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['205','214'])).

thf('216',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('217',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['215','216','217'])).

thf('219',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('221',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,
    ( ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ( v2_funct_1 @ ( k4_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['200','201','202','203','204','219','220','221'])).

thf('223',plain,(
    v2_funct_1 @ ( k4_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) @ ( k4_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['190','223'])).

thf('225',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

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

thf('226',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X30 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_funct_2 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('227',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_funct_2 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['226'])).

thf('228',plain,
    ( ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['225','227'])).

thf('229',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('230',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    r2_funct_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['228','229','230'])).

thf('232',plain,(
    $false ),
    inference(demod,[status(thm)],['121','224','231'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.m3DjugI2EE
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 15:45:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.49/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.66  % Solved by: fo/fo7.sh
% 0.49/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.66  % done 641 iterations in 0.196s
% 0.49/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.66  % SZS output start Refutation
% 0.49/0.66  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.66  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.49/0.66  thf(k3_relset_1_type, type, k3_relset_1: $i > $i > $i > $i).
% 0.49/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.66  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.66  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.49/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.49/0.66  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.49/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.66  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.66  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.66  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.49/0.66  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.49/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.66  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.49/0.66  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.66  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.49/0.66  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.66  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.66  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.66  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.49/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.66  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.49/0.66  thf(d3_struct_0, axiom,
% 0.49/0.66    (![A:$i]:
% 0.49/0.66     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.49/0.66  thf('0', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('1', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('2', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf(t64_tops_2, conjecture,
% 0.49/0.66    (![A:$i]:
% 0.49/0.66     ( ( l1_struct_0 @ A ) =>
% 0.49/0.66       ( ![B:$i]:
% 0.49/0.66         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.49/0.66           ( ![C:$i]:
% 0.49/0.66             ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.66                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.66                 ( m1_subset_1 @
% 0.49/0.66                   C @ 
% 0.49/0.66                   ( k1_zfmisc_1 @
% 0.49/0.66                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.66               ( ( ( ( k2_relset_1 @
% 0.49/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.49/0.66                     ( k2_struct_0 @ B ) ) & 
% 0.49/0.66                   ( v2_funct_1 @ C ) ) =>
% 0.49/0.66                 ( r2_funct_2 @
% 0.49/0.66                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.49/0.66                   ( k2_tops_2 @
% 0.49/0.66                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.49/0.66                     ( k2_tops_2 @
% 0.49/0.66                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.49/0.66                   C ) ) ) ) ) ) ))).
% 0.49/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.66    (~( ![A:$i]:
% 0.49/0.66        ( ( l1_struct_0 @ A ) =>
% 0.49/0.66          ( ![B:$i]:
% 0.49/0.66            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.49/0.66              ( ![C:$i]:
% 0.49/0.66                ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.66                    ( v1_funct_2 @
% 0.49/0.66                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.66                    ( m1_subset_1 @
% 0.49/0.66                      C @ 
% 0.49/0.66                      ( k1_zfmisc_1 @
% 0.49/0.66                        ( k2_zfmisc_1 @
% 0.49/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.66                  ( ( ( ( k2_relset_1 @
% 0.49/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.49/0.66                        ( k2_struct_0 @ B ) ) & 
% 0.49/0.66                      ( v2_funct_1 @ C ) ) =>
% 0.49/0.66                    ( r2_funct_2 @
% 0.49/0.66                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.49/0.66                      ( k2_tops_2 @
% 0.49/0.66                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.49/0.66                        ( k2_tops_2 @
% 0.49/0.66                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.49/0.66                      C ) ) ) ) ) ) ) )),
% 0.49/0.66    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.49/0.66  thf('3', plain,
% 0.49/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.66          sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('4', plain,
% 0.49/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.66           sk_C)
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.66  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('6', plain,
% 0.49/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.49/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.66          sk_C)),
% 0.49/0.66      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.66  thf('7', plain,
% 0.49/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.66           sk_C)
% 0.49/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.66      inference('sup-', [status(thm)], ['1', '6'])).
% 0.49/0.66  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('9', plain,
% 0.49/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.66          sk_C)),
% 0.49/0.66      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.66  thf('10', plain,
% 0.49/0.66      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.66            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.66           sk_C)
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup-', [status(thm)], ['0', '9'])).
% 0.49/0.66  thf('11', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('12', plain,
% 0.49/0.66      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ 
% 0.49/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.66           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.49/0.66          sk_C)),
% 0.49/0.66      inference('demod', [status(thm)], ['10', '11'])).
% 0.49/0.66  thf('13', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('14', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('15', plain,
% 0.49/0.66      (((m1_subset_1 @ sk_C @ 
% 0.49/0.66         (k1_zfmisc_1 @ 
% 0.49/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['13', '14'])).
% 0.49/0.66  thf('16', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('17', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['15', '16'])).
% 0.49/0.66  thf('18', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf(redefinition_k2_relset_1, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.66       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.49/0.66  thf('19', plain,
% 0.49/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.66         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.49/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.66  thf('20', plain,
% 0.49/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.49/0.66  thf('21', plain,
% 0.49/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('22', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('23', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.66      inference('demod', [status(thm)], ['17', '22'])).
% 0.49/0.66  thf(cc5_funct_2, axiom,
% 0.49/0.66    (![A:$i,B:$i]:
% 0.49/0.66     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.49/0.66       ( ![C:$i]:
% 0.49/0.66         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.66           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.49/0.66             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.49/0.66  thf('24', plain,
% 0.49/0.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.49/0.66         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.49/0.66          | (v1_partfun1 @ X23 @ X24)
% 0.49/0.66          | ~ (v1_funct_2 @ X23 @ X24 @ X25)
% 0.49/0.66          | ~ (v1_funct_1 @ X23)
% 0.49/0.66          | (v1_xboole_0 @ X25))),
% 0.49/0.66      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.49/0.66  thf('25', plain,
% 0.49/0.66      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.49/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.66        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))
% 0.49/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['23', '24'])).
% 0.49/0.66  thf('26', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('27', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('28', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('29', plain,
% 0.49/0.66      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['27', '28'])).
% 0.49/0.66  thf('30', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('31', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('demod', [status(thm)], ['29', '30'])).
% 0.49/0.66  thf('32', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('33', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['31', '32'])).
% 0.49/0.66  thf('34', plain,
% 0.49/0.66      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.49/0.66        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.49/0.66      inference('demod', [status(thm)], ['25', '26', '33'])).
% 0.49/0.66  thf('35', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf(fc5_struct_0, axiom,
% 0.49/0.66    (![A:$i]:
% 0.49/0.66     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.49/0.66       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.49/0.66  thf('36', plain,
% 0.49/0.66      (![X36 : $i]:
% 0.49/0.66         (~ (v1_xboole_0 @ (k2_struct_0 @ X36))
% 0.49/0.66          | ~ (l1_struct_0 @ X36)
% 0.49/0.66          | (v2_struct_0 @ X36))),
% 0.49/0.66      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.49/0.66  thf('37', plain,
% 0.49/0.66      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.49/0.66        | (v2_struct_0 @ sk_B)
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup-', [status(thm)], ['35', '36'])).
% 0.49/0.66  thf('38', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('39', plain,
% 0.49/0.66      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.49/0.66      inference('demod', [status(thm)], ['37', '38'])).
% 0.49/0.66  thf('40', plain, (~ (v2_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('41', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('clc', [status(thm)], ['39', '40'])).
% 0.49/0.66  thf('42', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.49/0.66      inference('clc', [status(thm)], ['34', '41'])).
% 0.49/0.66  thf(d4_partfun1, axiom,
% 0.49/0.66    (![A:$i,B:$i]:
% 0.49/0.66     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.49/0.66       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.49/0.66  thf('43', plain,
% 0.49/0.66      (![X26 : $i, X27 : $i]:
% 0.49/0.66         (~ (v1_partfun1 @ X27 @ X26)
% 0.49/0.66          | ((k1_relat_1 @ X27) = (X26))
% 0.49/0.66          | ~ (v4_relat_1 @ X27 @ X26)
% 0.49/0.66          | ~ (v1_relat_1 @ X27))),
% 0.49/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.66  thf('44', plain,
% 0.49/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.66        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.49/0.66        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['42', '43'])).
% 0.49/0.66  thf('45', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf(cc1_relset_1, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.66       ( v1_relat_1 @ C ) ))).
% 0.49/0.66  thf('46', plain,
% 0.49/0.66      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.66         ((v1_relat_1 @ X2)
% 0.49/0.66          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.49/0.66      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.66  thf('47', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.66  thf('48', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf(cc2_relset_1, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.66       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.49/0.66  thf('49', plain,
% 0.49/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.49/0.66         ((v4_relat_1 @ X5 @ X6)
% 0.49/0.66          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.49/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.66  thf('50', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.49/0.66      inference('sup-', [status(thm)], ['48', '49'])).
% 0.49/0.66  thf('51', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['44', '47', '50'])).
% 0.49/0.66  thf('52', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('53', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('54', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.49/0.66      inference('clc', [status(thm)], ['34', '41'])).
% 0.49/0.66  thf('55', plain,
% 0.49/0.66      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.66      inference('sup+', [status(thm)], ['53', '54'])).
% 0.49/0.66  thf('56', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('57', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['55', '56'])).
% 0.49/0.66  thf('58', plain,
% 0.49/0.66      (![X26 : $i, X27 : $i]:
% 0.49/0.66         (~ (v1_partfun1 @ X27 @ X26)
% 0.49/0.66          | ((k1_relat_1 @ X27) = (X26))
% 0.49/0.66          | ~ (v4_relat_1 @ X27 @ X26)
% 0.49/0.66          | ~ (v1_relat_1 @ X27))),
% 0.49/0.66      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.49/0.66  thf('59', plain,
% 0.49/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.66        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.49/0.66        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['57', '58'])).
% 0.49/0.66  thf('60', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.66  thf('61', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('62', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('63', plain,
% 0.49/0.66      (((m1_subset_1 @ sk_C @ 
% 0.49/0.66         (k1_zfmisc_1 @ 
% 0.49/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.66      inference('sup+', [status(thm)], ['61', '62'])).
% 0.49/0.66  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('65', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.66  thf('66', plain,
% 0.49/0.66      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.49/0.66         ((v4_relat_1 @ X5 @ X6)
% 0.49/0.66          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.49/0.66      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.66  thf('67', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('sup-', [status(thm)], ['65', '66'])).
% 0.49/0.66  thf('68', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.66  thf('69', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['44', '47', '50'])).
% 0.49/0.66  thf('70', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('71', plain,
% 0.49/0.66      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.49/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.49/0.66           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)) @ 
% 0.49/0.66          sk_C)),
% 0.49/0.66      inference('demod', [status(thm)], ['12', '51', '52', '68', '69', '70'])).
% 0.49/0.66  thf('72', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('73', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.66  thf('74', plain,
% 0.49/0.66      (((m1_subset_1 @ sk_C @ 
% 0.49/0.66         (k1_zfmisc_1 @ 
% 0.49/0.66          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['72', '73'])).
% 0.49/0.66  thf('75', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('76', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['74', '75'])).
% 0.49/0.66  thf('77', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('78', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.66      inference('demod', [status(thm)], ['76', '77'])).
% 0.49/0.66  thf('79', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.66  thf('80', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.66      inference('demod', [status(thm)], ['78', '79'])).
% 0.49/0.66  thf(d4_tops_2, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.66       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.49/0.66         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.49/0.66  thf('81', plain,
% 0.49/0.66      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.49/0.66         (((k2_relset_1 @ X38 @ X37 @ X39) != (X37))
% 0.49/0.66          | ~ (v2_funct_1 @ X39)
% 0.49/0.66          | ((k2_tops_2 @ X38 @ X37 @ X39) = (k2_funct_1 @ X39))
% 0.49/0.66          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.49/0.66          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.49/0.66          | ~ (v1_funct_1 @ X39))),
% 0.49/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.49/0.66  thf('82', plain,
% 0.49/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.66        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.49/0.66        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.66            = (k2_funct_1 @ sk_C))
% 0.49/0.66        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.66        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.66            != (k2_relat_1 @ sk_C)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['80', '81'])).
% 0.49/0.66  thf('83', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('84', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('85', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('86', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('87', plain,
% 0.49/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.66      inference('sup+', [status(thm)], ['85', '86'])).
% 0.49/0.66  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('89', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.66      inference('demod', [status(thm)], ['87', '88'])).
% 0.49/0.66  thf('90', plain,
% 0.49/0.66      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['84', '89'])).
% 0.49/0.66  thf('91', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('92', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.66  thf('93', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('94', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['92', '93'])).
% 0.49/0.66  thf('95', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.66  thf('96', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['94', '95'])).
% 0.49/0.66  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf(d9_funct_1, axiom,
% 0.49/0.66    (![A:$i]:
% 0.49/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.66       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ A ) = ( k4_relat_1 @ A ) ) ) ))).
% 0.49/0.66  thf('98', plain,
% 0.49/0.66      (![X0 : $i]:
% 0.49/0.66         (~ (v2_funct_1 @ X0)
% 0.49/0.66          | ((k2_funct_1 @ X0) = (k4_relat_1 @ X0))
% 0.49/0.66          | ~ (v1_funct_1 @ X0)
% 0.49/0.66          | ~ (v1_relat_1 @ X0))),
% 0.49/0.66      inference('cnf', [status(esa)], [d9_funct_1])).
% 0.49/0.66  thf('99', plain,
% 0.49/0.66      ((~ (v1_relat_1 @ sk_C)
% 0.49/0.66        | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))
% 0.49/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.66      inference('sup-', [status(thm)], ['97', '98'])).
% 0.49/0.66  thf('100', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('101', plain,
% 0.49/0.66      ((~ (v1_relat_1 @ sk_C) | ((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C)))),
% 0.49/0.66      inference('demod', [status(thm)], ['99', '100'])).
% 0.49/0.66  thf('102', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.66  thf('103', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.49/0.66  thf('104', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('105', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('106', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('107', plain,
% 0.49/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('108', plain,
% 0.49/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66          = (k2_struct_0 @ sk_B))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.66      inference('sup+', [status(thm)], ['106', '107'])).
% 0.49/0.66  thf('109', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('110', plain,
% 0.49/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('demod', [status(thm)], ['108', '109'])).
% 0.49/0.66  thf('111', plain,
% 0.49/0.66      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66          = (k2_struct_0 @ sk_B))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['105', '110'])).
% 0.49/0.66  thf('112', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('113', plain,
% 0.49/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('demod', [status(thm)], ['111', '112'])).
% 0.49/0.66  thf('114', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('115', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('116', plain,
% 0.49/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.66         = (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['113', '114', '115'])).
% 0.49/0.66  thf('117', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.66  thf('118', plain,
% 0.49/0.66      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.66         = (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['116', '117'])).
% 0.49/0.66  thf('119', plain,
% 0.49/0.66      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.66          = (k4_relat_1 @ sk_C))
% 0.49/0.66        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.49/0.66      inference('demod', [status(thm)], ['82', '83', '96', '103', '104', '118'])).
% 0.49/0.66  thf('120', plain,
% 0.49/0.66      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.66         = (k4_relat_1 @ sk_C))),
% 0.49/0.66      inference('simplify', [status(thm)], ['119'])).
% 0.49/0.66  thf('121', plain,
% 0.49/0.66      (~ (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.49/0.66          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.49/0.66           (k4_relat_1 @ sk_C)) @ 
% 0.49/0.66          sk_C)),
% 0.49/0.66      inference('demod', [status(thm)], ['71', '120'])).
% 0.49/0.66  thf('122', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('123', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf(dt_k3_relset_1, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.66       ( m1_subset_1 @
% 0.49/0.66         ( k3_relset_1 @ A @ B @ C ) @ 
% 0.49/0.66         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ))).
% 0.49/0.66  thf('124', plain,
% 0.49/0.66      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.66         ((m1_subset_1 @ (k3_relset_1 @ X8 @ X9 @ X10) @ 
% 0.49/0.66           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X8)))
% 0.49/0.66          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.49/0.66      inference('cnf', [status(esa)], [dt_k3_relset_1])).
% 0.49/0.66  thf('125', plain,
% 0.49/0.66      ((m1_subset_1 @ 
% 0.49/0.66        (k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C) @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.49/0.66      inference('sup-', [status(thm)], ['123', '124'])).
% 0.49/0.66  thf('126', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf(redefinition_k3_relset_1, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.66       ( ( k3_relset_1 @ A @ B @ C ) = ( k4_relat_1 @ C ) ) ))).
% 0.49/0.66  thf('127', plain,
% 0.49/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.66         (((k3_relset_1 @ X18 @ X19 @ X17) = (k4_relat_1 @ X17))
% 0.49/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.49/0.66      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.49/0.66  thf('128', plain,
% 0.49/0.66      (((k3_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k4_relat_1 @ sk_C))),
% 0.49/0.66      inference('sup-', [status(thm)], ['126', '127'])).
% 0.49/0.66  thf('129', plain,
% 0.49/0.66      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A))))),
% 0.49/0.66      inference('demod', [status(thm)], ['125', '128'])).
% 0.49/0.66  thf('130', plain,
% 0.49/0.66      (((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.66         (k1_zfmisc_1 @ 
% 0.49/0.66          (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_A))),
% 0.49/0.66      inference('sup+', [status(thm)], ['122', '129'])).
% 0.49/0.66  thf('131', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('132', plain,
% 0.49/0.66      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.49/0.66      inference('demod', [status(thm)], ['130', '131'])).
% 0.49/0.66  thf('133', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.66  thf('134', plain,
% 0.49/0.66      ((m1_subset_1 @ (k4_relat_1 @ sk_C) @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))),
% 0.49/0.66      inference('demod', [status(thm)], ['132', '133'])).
% 0.49/0.66  thf('135', plain,
% 0.49/0.66      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.49/0.66         (((k2_relset_1 @ X38 @ X37 @ X39) != (X37))
% 0.49/0.66          | ~ (v2_funct_1 @ X39)
% 0.49/0.66          | ((k2_tops_2 @ X38 @ X37 @ X39) = (k2_funct_1 @ X39))
% 0.49/0.66          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.49/0.66          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.49/0.66          | ~ (v1_funct_1 @ X39))),
% 0.49/0.66      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.49/0.66  thf('136', plain,
% 0.49/0.66      ((~ (v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.66        | ~ (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.66             (k1_relat_1 @ sk_C))
% 0.49/0.66        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.49/0.66            (k4_relat_1 @ sk_C)) = (k2_funct_1 @ (k4_relat_1 @ sk_C)))
% 0.49/0.66        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.66        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.49/0.66            (k4_relat_1 @ sk_C)) != (k1_relat_1 @ sk_C)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['134', '135'])).
% 0.49/0.66  thf('137', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.66      inference('demod', [status(thm)], ['78', '79'])).
% 0.49/0.66  thf(t31_funct_2, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.66         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.66       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.49/0.66         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.49/0.66           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.49/0.66           ( m1_subset_1 @
% 0.49/0.66             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.49/0.66  thf('138', plain,
% 0.49/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.49/0.66         (~ (v2_funct_1 @ X32)
% 0.49/0.66          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.49/0.66          | (v1_funct_1 @ (k2_funct_1 @ X32))
% 0.49/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.49/0.66          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.49/0.66          | ~ (v1_funct_1 @ X32))),
% 0.49/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.66  thf('139', plain,
% 0.49/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.66        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.49/0.66        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.49/0.66        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.66            != (k2_relat_1 @ sk_C))
% 0.49/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.66      inference('sup-', [status(thm)], ['137', '138'])).
% 0.49/0.66  thf('140', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('141', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['94', '95'])).
% 0.49/0.66  thf('142', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.49/0.66  thf('143', plain,
% 0.49/0.66      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.49/0.66         = (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['116', '117'])).
% 0.49/0.66  thf('144', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('145', plain,
% 0.49/0.66      (((v1_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.66        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.49/0.66      inference('demod', [status(thm)],
% 0.49/0.66                ['139', '140', '141', '142', '143', '144'])).
% 0.49/0.66  thf('146', plain, ((v1_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.66      inference('simplify', [status(thm)], ['145'])).
% 0.49/0.66  thf('147', plain,
% 0.49/0.66      (![X35 : $i]:
% 0.49/0.66         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.66      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.66  thf('148', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.66  thf('149', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.66  thf('150', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['148', '149'])).
% 0.49/0.66  thf('151', plain,
% 0.49/0.66      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.49/0.66         (~ (v2_funct_1 @ X32)
% 0.49/0.66          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.49/0.66          | (v1_funct_2 @ (k2_funct_1 @ X32) @ X33 @ X34)
% 0.49/0.66          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.49/0.66          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.49/0.66          | ~ (v1_funct_1 @ X32))),
% 0.49/0.66      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.49/0.66  thf('152', plain,
% 0.49/0.66      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.66        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.49/0.66        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.66           (k1_relat_1 @ sk_C))
% 0.49/0.66        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66            != (u1_struct_0 @ sk_B))
% 0.49/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.66      inference('sup-', [status(thm)], ['150', '151'])).
% 0.49/0.66  thf('153', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('154', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.49/0.66      inference('demod', [status(thm)], ['87', '88'])).
% 0.49/0.66  thf('155', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.66  thf('156', plain,
% 0.49/0.66      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.49/0.66      inference('demod', [status(thm)], ['154', '155'])).
% 0.49/0.66  thf('157', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.49/0.66  thf('158', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.66  thf('159', plain,
% 0.49/0.66      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.49/0.66         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.49/0.66          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.49/0.66      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.49/0.66  thf('160', plain,
% 0.49/0.66      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('sup-', [status(thm)], ['158', '159'])).
% 0.49/0.66  thf('161', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.66      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.66  thf('162', plain,
% 0.49/0.66      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k2_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['160', '161'])).
% 0.49/0.66  thf('163', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('164', plain,
% 0.49/0.66      (((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.66         (k1_relat_1 @ sk_C))
% 0.49/0.66        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.49/0.66      inference('demod', [status(thm)],
% 0.49/0.66                ['152', '153', '156', '157', '162', '163'])).
% 0.49/0.66  thf('165', plain,
% 0.49/0.66      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.49/0.66        | ~ (l1_struct_0 @ sk_B)
% 0.49/0.66        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.66           (k1_relat_1 @ sk_C)))),
% 0.49/0.66      inference('sup-', [status(thm)], ['147', '164'])).
% 0.49/0.66  thf('166', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.66      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.66  thf('167', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('168', plain,
% 0.49/0.66      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.49/0.66        | (v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.66           (k1_relat_1 @ sk_C)))),
% 0.49/0.66      inference('demod', [status(thm)], ['165', '166', '167'])).
% 0.49/0.66  thf('169', plain,
% 0.49/0.66      ((v1_funct_2 @ (k4_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.49/0.66        (k1_relat_1 @ sk_C))),
% 0.49/0.66      inference('simplify', [status(thm)], ['168'])).
% 0.49/0.66  thf('170', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['101', '102'])).
% 0.49/0.66  thf(t65_funct_1, axiom,
% 0.49/0.66    (![A:$i]:
% 0.49/0.66     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.49/0.66       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.49/0.66  thf('171', plain,
% 0.49/0.66      (![X1 : $i]:
% 0.49/0.66         (~ (v2_funct_1 @ X1)
% 0.49/0.66          | ((k2_funct_1 @ (k2_funct_1 @ X1)) = (X1))
% 0.49/0.66          | ~ (v1_funct_1 @ X1)
% 0.49/0.66          | ~ (v1_relat_1 @ X1))),
% 0.49/0.66      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.49/0.66  thf('172', plain,
% 0.49/0.66      ((((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))
% 0.49/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.49/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.49/0.66      inference('sup+', [status(thm)], ['170', '171'])).
% 0.49/0.66  thf('173', plain, ((v1_relat_1 @ sk_C)),
% 0.49/0.66      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.66  thf('174', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('175', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.66  thf('176', plain, (((k2_funct_1 @ (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.49/0.66      inference('demod', [status(thm)], ['172', '173', '174', '175'])).
% 0.49/0.66  thf('177', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.66  thf(t24_relset_1, axiom,
% 0.49/0.66    (![A:$i,B:$i,C:$i]:
% 0.49/0.66     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.66       ( ( ( k1_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.49/0.66           ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.49/0.66         ( ( k2_relset_1 @ B @ A @ ( k3_relset_1 @ A @ B @ C ) ) =
% 0.49/0.66           ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.49/0.66  thf('178', plain,
% 0.49/0.66      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.66         (((k2_relset_1 @ X21 @ X20 @ (k3_relset_1 @ X20 @ X21 @ X22))
% 0.49/0.66            = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.49/0.66          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.49/0.66      inference('cnf', [status(esa)], [t24_relset_1])).
% 0.49/0.66  thf('179', plain,
% 0.49/0.66      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.66         (k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.49/0.66         = (k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))),
% 0.49/0.66      inference('sup-', [status(thm)], ['177', '178'])).
% 0.49/0.66  thf('180', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.66        (k1_zfmisc_1 @ 
% 0.49/0.66         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.66      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.66  thf('181', plain,
% 0.49/0.66      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.66         (((k3_relset_1 @ X18 @ X19 @ X17) = (k4_relat_1 @ X17))
% 0.49/0.66          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.49/0.66      inference('cnf', [status(esa)], [redefinition_k3_relset_1])).
% 0.49/0.66  thf('182', plain,
% 0.49/0.66      (((k3_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.66         = (k4_relat_1 @ sk_C))),
% 0.49/0.66      inference('sup-', [status(thm)], ['180', '181'])).
% 0.49/0.66  thf('183', plain,
% 0.49/0.66      ((m1_subset_1 @ sk_C @ 
% 0.49/0.67        (k1_zfmisc_1 @ 
% 0.49/0.67         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.67      inference('demod', [status(thm)], ['63', '64'])).
% 0.49/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i]:
% 0.49/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.67  thf('184', plain,
% 0.49/0.67      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.67         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.49/0.67          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.49/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.67  thf('185', plain,
% 0.49/0.67      (((k1_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67         = (k1_relat_1 @ sk_C))),
% 0.49/0.67      inference('sup-', [status(thm)], ['183', '184'])).
% 0.49/0.67  thf('186', plain,
% 0.49/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.49/0.67         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['179', '182', '185'])).
% 0.49/0.67  thf('187', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['59', '60', '67'])).
% 0.49/0.67  thf('188', plain,
% 0.49/0.67      (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.49/0.67         (k4_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['186', '187'])).
% 0.49/0.67  thf('189', plain,
% 0.49/0.67      ((((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.49/0.67          (k4_relat_1 @ sk_C)) = (sk_C))
% 0.49/0.67        | ~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.67        | ((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C)))),
% 0.49/0.67      inference('demod', [status(thm)], ['136', '146', '169', '176', '188'])).
% 0.49/0.67  thf('190', plain,
% 0.49/0.67      ((~ (v2_funct_1 @ (k4_relat_1 @ sk_C))
% 0.49/0.67        | ((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.49/0.67            (k4_relat_1 @ sk_C)) = (sk_C)))),
% 0.49/0.67      inference('simplify', [status(thm)], ['189'])).
% 0.49/0.67  thf('191', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ 
% 0.49/0.67        (k1_zfmisc_1 @ 
% 0.49/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.67      inference('demod', [status(thm)], ['148', '149'])).
% 0.49/0.67  thf('192', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['44', '47', '50'])).
% 0.49/0.67  thf(t63_tops_2, axiom,
% 0.49/0.67    (![A:$i]:
% 0.49/0.67     ( ( l1_struct_0 @ A ) =>
% 0.49/0.67       ( ![B:$i]:
% 0.49/0.67         ( ( l1_struct_0 @ B ) =>
% 0.49/0.67           ( ![C:$i]:
% 0.49/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.67                 ( m1_subset_1 @
% 0.49/0.67                   C @ 
% 0.49/0.67                   ( k1_zfmisc_1 @
% 0.49/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.67               ( ( ( ( k2_relset_1 @
% 0.49/0.67                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.49/0.67                     ( k2_struct_0 @ B ) ) & 
% 0.49/0.67                   ( v2_funct_1 @ C ) ) =>
% 0.49/0.67                 ( v2_funct_1 @
% 0.49/0.67                   ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) ) ) ) ) ) ))).
% 0.49/0.67  thf('193', plain,
% 0.49/0.67      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.49/0.67         (~ (l1_struct_0 @ X40)
% 0.49/0.67          | ((k2_relset_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X40) @ X42)
% 0.49/0.67              != (k2_struct_0 @ X40))
% 0.49/0.67          | ~ (v2_funct_1 @ X42)
% 0.49/0.67          | (v2_funct_1 @ 
% 0.49/0.67             (k2_tops_2 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X40) @ X42))
% 0.49/0.67          | ~ (m1_subset_1 @ X42 @ 
% 0.49/0.67               (k1_zfmisc_1 @ 
% 0.49/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X40))))
% 0.49/0.67          | ~ (v1_funct_2 @ X42 @ (u1_struct_0 @ X41) @ (u1_struct_0 @ X40))
% 0.49/0.67          | ~ (v1_funct_1 @ X42)
% 0.49/0.67          | ~ (l1_struct_0 @ X41))),
% 0.49/0.67      inference('cnf', [status(esa)], [t63_tops_2])).
% 0.49/0.67  thf('194', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X1 @ 
% 0.49/0.67             (k1_zfmisc_1 @ 
% 0.49/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.49/0.67          | ~ (l1_struct_0 @ sk_A)
% 0.49/0.67          | ~ (v1_funct_1 @ X1)
% 0.49/0.67          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.49/0.67          | (v2_funct_1 @ 
% 0.49/0.67             (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1))
% 0.49/0.67          | ~ (v2_funct_1 @ X1)
% 0.49/0.67          | ((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0) @ X1)
% 0.49/0.67              != (k2_struct_0 @ X0))
% 0.49/0.67          | ~ (l1_struct_0 @ X0))),
% 0.49/0.67      inference('sup-', [status(thm)], ['192', '193'])).
% 0.49/0.67  thf('195', plain, ((l1_struct_0 @ sk_A)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('196', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['44', '47', '50'])).
% 0.49/0.67  thf('197', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['44', '47', '50'])).
% 0.49/0.67  thf('198', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.49/0.67      inference('demod', [status(thm)], ['44', '47', '50'])).
% 0.49/0.67  thf('199', plain,
% 0.49/0.67      (![X0 : $i, X1 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X1 @ 
% 0.49/0.67             (k1_zfmisc_1 @ 
% 0.49/0.67              (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.49/0.67          | ~ (v1_funct_1 @ X1)
% 0.49/0.67          | ~ (v1_funct_2 @ X1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0))
% 0.49/0.67          | (v2_funct_1 @ 
% 0.49/0.67             (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1))
% 0.49/0.67          | ~ (v2_funct_1 @ X1)
% 0.49/0.67          | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ X0) @ X1)
% 0.49/0.67              != (k2_struct_0 @ X0))
% 0.49/0.67          | ~ (l1_struct_0 @ X0))),
% 0.49/0.67      inference('demod', [status(thm)], ['194', '195', '196', '197', '198'])).
% 0.49/0.67  thf('200', plain,
% 0.49/0.67      ((~ (l1_struct_0 @ sk_B)
% 0.49/0.67        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67            != (k2_struct_0 @ sk_B))
% 0.49/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.67        | (v2_funct_1 @ 
% 0.49/0.67           (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.49/0.67        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.49/0.67        | ~ (v1_funct_1 @ sk_C))),
% 0.49/0.67      inference('sup-', [status(thm)], ['191', '199'])).
% 0.49/0.67  thf('201', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('202', plain,
% 0.49/0.67      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67         = (k2_relat_1 @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['160', '161'])).
% 0.49/0.67  thf('203', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.67  thf('204', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('205', plain,
% 0.49/0.67      (![X35 : $i]:
% 0.49/0.67         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.49/0.67      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.49/0.67  thf('206', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ 
% 0.49/0.67        (k1_zfmisc_1 @ 
% 0.49/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.49/0.67      inference('demod', [status(thm)], ['148', '149'])).
% 0.49/0.67  thf('207', plain,
% 0.49/0.67      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.49/0.67         (((k2_relset_1 @ X38 @ X37 @ X39) != (X37))
% 0.49/0.67          | ~ (v2_funct_1 @ X39)
% 0.49/0.67          | ((k2_tops_2 @ X38 @ X37 @ X39) = (k2_funct_1 @ X39))
% 0.49/0.67          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.49/0.67          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.49/0.67          | ~ (v1_funct_1 @ X39))),
% 0.49/0.67      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.49/0.67  thf('208', plain,
% 0.49/0.67      ((~ (v1_funct_1 @ sk_C)
% 0.49/0.67        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.49/0.67        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67            = (k2_funct_1 @ sk_C))
% 0.49/0.67        | ~ (v2_funct_1 @ sk_C)
% 0.49/0.67        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67            != (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['206', '207'])).
% 0.49/0.67  thf('209', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('210', plain,
% 0.49/0.67      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['154', '155'])).
% 0.49/0.67  thf('211', plain, (((k2_funct_1 @ sk_C) = (k4_relat_1 @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['101', '102'])).
% 0.49/0.67  thf('212', plain, ((v2_funct_1 @ sk_C)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('213', plain,
% 0.49/0.67      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67         = (k2_relat_1 @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['160', '161'])).
% 0.49/0.67  thf('214', plain,
% 0.49/0.67      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67          = (k4_relat_1 @ sk_C))
% 0.49/0.67        | ((k2_relat_1 @ sk_C) != (u1_struct_0 @ sk_B)))),
% 0.49/0.67      inference('demod', [status(thm)],
% 0.49/0.67                ['208', '209', '210', '211', '212', '213'])).
% 0.49/0.67  thf('215', plain,
% 0.49/0.67      ((((k2_relat_1 @ sk_C) != (k2_struct_0 @ sk_B))
% 0.49/0.67        | ~ (l1_struct_0 @ sk_B)
% 0.49/0.67        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67            = (k4_relat_1 @ sk_C)))),
% 0.49/0.67      inference('sup-', [status(thm)], ['205', '214'])).
% 0.49/0.67  thf('216', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.49/0.67      inference('sup+', [status(thm)], ['20', '21'])).
% 0.49/0.67  thf('217', plain, ((l1_struct_0 @ sk_B)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('218', plain,
% 0.49/0.67      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.49/0.67        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67            = (k4_relat_1 @ sk_C)))),
% 0.49/0.67      inference('demod', [status(thm)], ['215', '216', '217'])).
% 0.49/0.67  thf('219', plain,
% 0.49/0.67      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.49/0.67         = (k4_relat_1 @ sk_C))),
% 0.49/0.67      inference('simplify', [status(thm)], ['218'])).
% 0.49/0.67  thf('220', plain,
% 0.49/0.67      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.49/0.67      inference('demod', [status(thm)], ['154', '155'])).
% 0.49/0.67  thf('221', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('222', plain,
% 0.49/0.67      ((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.49/0.67        | (v2_funct_1 @ (k4_relat_1 @ sk_C)))),
% 0.49/0.67      inference('demod', [status(thm)],
% 0.49/0.67                ['200', '201', '202', '203', '204', '219', '220', '221'])).
% 0.49/0.67  thf('223', plain, ((v2_funct_1 @ (k4_relat_1 @ sk_C))),
% 0.49/0.67      inference('simplify', [status(thm)], ['222'])).
% 0.49/0.67  thf('224', plain,
% 0.49/0.67      (((k2_tops_2 @ (u1_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C) @ 
% 0.49/0.67         (k4_relat_1 @ sk_C)) = (sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['190', '223'])).
% 0.49/0.67  thf('225', plain,
% 0.49/0.67      ((m1_subset_1 @ sk_C @ 
% 0.49/0.67        (k1_zfmisc_1 @ 
% 0.49/0.67         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.49/0.67      inference('demod', [status(thm)], ['78', '79'])).
% 0.49/0.67  thf(redefinition_r2_funct_2, axiom,
% 0.49/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.49/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.49/0.67         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.49/0.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.67       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.49/0.67  thf('226', plain,
% 0.49/0.67      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.67         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.49/0.67          | ~ (v1_funct_2 @ X28 @ X29 @ X30)
% 0.49/0.67          | ~ (v1_funct_1 @ X28)
% 0.49/0.67          | ~ (v1_funct_1 @ X31)
% 0.49/0.67          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.49/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.49/0.67          | (r2_funct_2 @ X29 @ X30 @ X28 @ X31)
% 0.49/0.67          | ((X28) != (X31)))),
% 0.49/0.67      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.49/0.67  thf('227', plain,
% 0.49/0.67      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.67         ((r2_funct_2 @ X29 @ X30 @ X31 @ X31)
% 0.49/0.67          | ~ (v1_funct_1 @ X31)
% 0.49/0.67          | ~ (v1_funct_2 @ X31 @ X29 @ X30)
% 0.49/0.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.49/0.67      inference('simplify', [status(thm)], ['226'])).
% 0.49/0.67  thf('228', plain,
% 0.49/0.67      ((~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.49/0.67        | ~ (v1_funct_1 @ sk_C)
% 0.49/0.67        | (r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C))),
% 0.49/0.67      inference('sup-', [status(thm)], ['225', '227'])).
% 0.49/0.67  thf('229', plain,
% 0.49/0.67      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.49/0.67      inference('demod', [status(thm)], ['94', '95'])).
% 0.49/0.67  thf('230', plain, ((v1_funct_1 @ sk_C)),
% 0.49/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.67  thf('231', plain,
% 0.49/0.67      ((r2_funct_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C @ sk_C)),
% 0.49/0.67      inference('demod', [status(thm)], ['228', '229', '230'])).
% 0.49/0.67  thf('232', plain, ($false),
% 0.49/0.67      inference('demod', [status(thm)], ['121', '224', '231'])).
% 0.49/0.67  
% 0.49/0.67  % SZS output end Refutation
% 0.49/0.67  
% 0.49/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
