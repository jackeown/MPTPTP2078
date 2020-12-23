%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UY6vBff5Rs

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:59 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  295 (10897 expanded)
%              Number of leaves         :   49 (3150 expanded)
%              Depth                    :   31
%              Number of atoms          : 2743 (275805 expanded)
%              Number of equality atoms :  190 (13860 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('2',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
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
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_B ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','27'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('32',plain,(
    ! [X36: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X36 ) )
      | ~ ( l1_struct_0 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('44',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
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
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('53',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

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

thf('57',plain,(
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

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('61',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['60','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('72',plain,(
    v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['30','37'])).

thf('73',plain,
    ( ( v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_partfun1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('77',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('79',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    v4_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','85'])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','86'])).

thf('88',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('90',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('91',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('96',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('97',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_relat_1 @ sk_C ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['89','97'])).

thf('99',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','85'])).

thf('102',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['58','59','87','88','102'])).

thf('104',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','85'])).

thf('106',plain,
    ( ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k1_relat_1 @ sk_C ) )
   <= ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','14','49','50','51','104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

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

thf('108',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('109',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','86'])).

thf('112',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('113',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( v1_partfun1 @ X27 @ X28 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('119',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('120',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','86'])).

thf('123',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('124',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['120','121','122','123','124'])).

thf('126',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('128',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v2_funct_1 @ X32 )
      | ( ( k2_relset_1 @ X34 @ X33 @ X32 )
       != X33 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X32 ) @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('129',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
     != ( k2_relat_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_C @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['70','86'])).

thf('132',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('133',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,(
    v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['117','126','135'])).

thf('137',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X30 )
      | ( ( k1_relat_1 @ X31 )
        = X30 )
      | ~ ( v4_relat_1 @ X31 @ X30 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('138',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('140',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('141',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('143',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('145',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v4_relat_1 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('146',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['138','143','146'])).

thf('148',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('149',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('150',plain,
    ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['103'])).

thf('152',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('153',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('154',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('155',plain,
    ( ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('156',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['156','157'])).

thf('159',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['153','158'])).

thf('160',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
       != ( k2_struct_0 @ sk_B ) )
      | ~ ( l1_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['152','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( k1_relset_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('166',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['77','78','85'])).

thf('167',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['40','45','48'])).

thf('168',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('169',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('170',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_tops_2 @ ( k1_relat_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['164','165','166','167','168','169'])).

thf('171',plain,
    ( ( ( k1_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['151','170'])).

thf('172',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
     != ( k2_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['150','171'])).

thf('173',plain,
    ( ( ( ( k2_relat_1 @ sk_C )
       != ( k2_relat_1 @ sk_C ) )
      | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['147','172'])).

thf('174',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('175',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('176',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('177',plain,(
    ! [X13: $i] :
      ( ( ( k1_relat_1 @ X13 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X13 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('178',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('180',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_relat_1 @ sk_C )
        = k1_xboole_0 ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['178','179'])).

thf('181',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('183',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['173'])).

thf('185',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('186',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['184','185'])).

thf('187',plain,
    ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['183','186'])).

thf('188',plain,
    ( ( ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_A ) )
    | ( ( k1_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('189',plain,(
    ( k2_relset_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['187','188'])).

thf('190',plain,(
    ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['106','189'])).

thf('191',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('192',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('193',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf(t155_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( ( k10_relat_1 @ B @ A )
          = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ) )).

thf('194',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k10_relat_1 @ X14 @ X15 )
        = ( k9_relat_1 @ ( k2_funct_1 @ X14 ) @ X15 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t155_funct_1])).

thf('195',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('196',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('197',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_funct_1 @ sk_C )
      = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('199',plain,
    ( ( k2_funct_1 @ sk_C )
    = ( k7_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('200',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('201',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['199','200'])).

thf('202',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('203',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k9_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['194','203'])).

thf('205',plain,(
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('206',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('207',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X11
        = ( k7_relat_1 @ X11 @ X12 ) )
      | ~ ( v4_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('208',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('210',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['208','209'])).

thf('211',plain,
    ( ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['205','210'])).

thf('212',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('215',plain,(
    ! [X8: $i] :
      ( ( ( k9_relat_1 @ X8 @ ( k1_relat_1 @ X8 ) )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('216',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('217',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['216'])).

thf(t164_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( v2_funct_1 @ B ) )
       => ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('218',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X16 @ ( k1_relat_1 @ X17 ) )
      | ~ ( v2_funct_1 @ X17 )
      | ( ( k10_relat_1 @ X17 @ ( k9_relat_1 @ X17 @ X16 ) )
        = X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t164_funct_1])).

thf('219',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['215','219'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ X0 ) )
        = ( k1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['214','221'])).

thf('223',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v2_funct_1 @ ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) @ ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) )
      = ( k1_relat_1 @ ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['213','222'])).

thf('224',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('225',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('228',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('230',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('231',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('232',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('233',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('234',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k7_relat_1 @ sk_C @ X0 ) )
      = ( k9_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['232','233'])).

thf('235',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['231','234'])).

thf('236',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('237',plain,
    ( ( k10_relat_1 @ sk_C @ ( k2_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['223','224','225','226','227','228','229','230','235','236'])).

thf('238',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['43','44'])).

thf('239',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['204','237','238','239','240'])).

thf('242',plain,
    ( ( k2_relset_1 @ ( k2_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_C ) @ ( k2_funct_1 @ sk_C ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['193','241'])).

thf('243',plain,(
    ( k1_relat_1 @ sk_C )
 != ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['190','242'])).

thf('244',plain,(
    $false ),
    inference(simplify,[status(thm)],['243'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UY6vBff5Rs
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 499 iterations in 0.335s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.79  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.79  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.59/0.79  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.59/0.79  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.59/0.79  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.59/0.79  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.59/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.79  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.59/0.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.79  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.79  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.59/0.79  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.59/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.79  thf(d3_struct_0, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.59/0.79  thf('0', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('1', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf(t62_tops_2, conjecture,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( l1_struct_0 @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.59/0.79           ( ![C:$i]:
% 0.59/0.79             ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.79                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.79                 ( m1_subset_1 @
% 0.59/0.79                   C @ 
% 0.59/0.79                   ( k1_zfmisc_1 @
% 0.59/0.79                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.79               ( ( ( ( k2_relset_1 @
% 0.59/0.79                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.59/0.79                     ( k2_struct_0 @ B ) ) & 
% 0.59/0.79                   ( v2_funct_1 @ C ) ) =>
% 0.59/0.79                 ( ( ( k1_relset_1 @
% 0.59/0.79                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.59/0.79                       ( k2_tops_2 @
% 0.59/0.79                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.59/0.79                     ( k2_struct_0 @ B ) ) & 
% 0.59/0.79                   ( ( k2_relset_1 @
% 0.59/0.79                       ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.59/0.79                       ( k2_tops_2 @
% 0.59/0.79                         ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.59/0.79                     ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i]:
% 0.59/0.79        ( ( l1_struct_0 @ A ) =>
% 0.59/0.79          ( ![B:$i]:
% 0.59/0.79            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.59/0.79              ( ![C:$i]:
% 0.59/0.79                ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.79                    ( v1_funct_2 @
% 0.59/0.79                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.79                    ( m1_subset_1 @
% 0.59/0.79                      C @ 
% 0.59/0.79                      ( k1_zfmisc_1 @
% 0.59/0.79                        ( k2_zfmisc_1 @
% 0.59/0.79                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.79                  ( ( ( ( k2_relset_1 @
% 0.59/0.79                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.59/0.79                        ( k2_struct_0 @ B ) ) & 
% 0.59/0.79                      ( v2_funct_1 @ C ) ) =>
% 0.59/0.79                    ( ( ( k1_relset_1 @
% 0.59/0.79                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.59/0.79                          ( k2_tops_2 @
% 0.59/0.79                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.59/0.79                        ( k2_struct_0 @ B ) ) & 
% 0.59/0.79                      ( ( k2_relset_1 @
% 0.59/0.79                          ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.59/0.79                          ( k2_tops_2 @
% 0.59/0.79                            ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) =
% 0.59/0.79                        ( k2_struct_0 @ A ) ) ) ) ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t62_tops_2])).
% 0.59/0.79  thf('2', plain,
% 0.59/0.79      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          != (k2_struct_0 @ sk_B))
% 0.59/0.79        | ((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79            != (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      ((((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          != (k2_struct_0 @ sk_A)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_A))))),
% 0.59/0.79      inference('split', [status(esa)], ['2'])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79           != (k2_struct_0 @ sk_A))
% 0.59/0.79         | ~ (l1_struct_0 @ sk_B)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['1', '3'])).
% 0.59/0.79  thf('5', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          != (k2_struct_0 @ sk_A)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_A))))),
% 0.59/0.79      inference('demod', [status(thm)], ['4', '5'])).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79           != (k2_struct_0 @ sk_A))
% 0.59/0.79         | ~ (l1_struct_0 @ sk_B)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['0', '6'])).
% 0.59/0.79  thf('8', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      ((((k2_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          != (k2_struct_0 @ sk_A)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_A))))),
% 0.59/0.79      inference('demod', [status(thm)], ['7', '8'])).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(redefinition_k2_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.79         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.59/0.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.59/0.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.79         = (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.79  thf('13', plain,
% 0.59/0.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.79         = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('14', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('15', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('16', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (((m1_subset_1 @ sk_C @ 
% 0.59/0.79         (k1_zfmisc_1 @ 
% 0.59/0.79          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['15', '16'])).
% 0.59/0.79  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.79  thf(cc5_funct_2, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.59/0.79       ( ![C:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.59/0.79             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.59/0.79          | (v1_partfun1 @ X27 @ X28)
% 0.59/0.79          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.59/0.79          | ~ (v1_funct_1 @ X27)
% 0.59/0.79          | (v1_xboole_0 @ X29))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.79        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.59/0.79        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.79  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['23', '24'])).
% 0.59/0.79  thf('26', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('27', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('demod', [status(thm)], ['25', '26'])).
% 0.59/0.79  thf('28', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k2_struct_0 @ sk_B))
% 0.59/0.79        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['21', '22', '27'])).
% 0.59/0.79  thf('29', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.59/0.79        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['28', '29'])).
% 0.59/0.79  thf('31', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf(fc5_struct_0, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.59/0.79       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      (![X36 : $i]:
% 0.59/0.79         (~ (v1_xboole_0 @ (k2_struct_0 @ X36))
% 0.59/0.79          | ~ (l1_struct_0 @ X36)
% 0.59/0.79          | (v2_struct_0 @ X36))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))
% 0.59/0.79        | (v2_struct_0 @ sk_B)
% 0.59/0.79        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.79  thf('34', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      ((~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)) | (v2_struct_0 @ sk_B))),
% 0.59/0.79      inference('demod', [status(thm)], ['33', '34'])).
% 0.59/0.79  thf('36', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('37', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('clc', [status(thm)], ['35', '36'])).
% 0.59/0.79  thf('38', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('clc', [status(thm)], ['30', '37'])).
% 0.59/0.79  thf(d4_partfun1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.59/0.79       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.59/0.79  thf('39', plain,
% 0.59/0.79      (![X30 : $i, X31 : $i]:
% 0.59/0.79         (~ (v1_partfun1 @ X31 @ X30)
% 0.59/0.79          | ((k1_relat_1 @ X31) = (X30))
% 0.59/0.79          | ~ (v4_relat_1 @ X31 @ X30)
% 0.59/0.79          | ~ (v1_relat_1 @ X31))),
% 0.59/0.79      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.79  thf('41', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(cc2_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.59/0.79  thf('42', plain,
% 0.59/0.79      (![X4 : $i, X5 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.59/0.79          | (v1_relat_1 @ X4)
% 0.59/0.79          | ~ (v1_relat_1 @ X5))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ 
% 0.59/0.79           (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))
% 0.59/0.79        | (v1_relat_1 @ sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['41', '42'])).
% 0.59/0.79  thf(fc6_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.79  thf('45', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('46', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(cc2_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.79  thf('47', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.79         ((v4_relat_1 @ X18 @ X19)
% 0.59/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.79  thf('48', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.59/0.79  thf('49', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['40', '45', '48'])).
% 0.59/0.79  thf('50', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['40', '45', '48'])).
% 0.59/0.79  thf('51', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['17', '18'])).
% 0.59/0.79  thf('53', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('54', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.79      inference('demod', [status(thm)], ['52', '53'])).
% 0.59/0.79  thf('55', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['40', '45', '48'])).
% 0.59/0.79  thf('56', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.79      inference('demod', [status(thm)], ['54', '55'])).
% 0.59/0.79  thf(d4_tops_2, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.79       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.59/0.79         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.59/0.79  thf('57', plain,
% 0.59/0.79      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.59/0.79         (((k2_relset_1 @ X38 @ X37 @ X39) != (X37))
% 0.59/0.79          | ~ (v2_funct_1 @ X39)
% 0.59/0.79          | ((k2_tops_2 @ X38 @ X37 @ X39) = (k2_funct_1 @ X39))
% 0.59/0.79          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.59/0.79          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 0.59/0.79          | ~ (v1_funct_1 @ X39))),
% 0.59/0.79      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.59/0.79  thf('58', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.59/0.79        | ((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79            = (k2_funct_1 @ sk_C))
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C)
% 0.59/0.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79            != (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['56', '57'])).
% 0.59/0.79  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('60', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('61', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('62', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('63', plain,
% 0.59/0.79      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['61', '62'])).
% 0.59/0.79  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('65', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.79      inference('demod', [status(thm)], ['63', '64'])).
% 0.59/0.79  thf('66', plain,
% 0.59/0.79      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['60', '65'])).
% 0.59/0.79  thf('67', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('68', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('demod', [status(thm)], ['66', '67'])).
% 0.59/0.79  thf('69', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('70', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['68', '69'])).
% 0.59/0.79  thf('71', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('72', plain, ((v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('clc', [status(thm)], ['30', '37'])).
% 0.59/0.79  thf('73', plain,
% 0.59/0.79      (((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['71', '72'])).
% 0.59/0.79  thf('74', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('75', plain, ((v1_partfun1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['73', '74'])).
% 0.59/0.79  thf('76', plain,
% 0.59/0.79      (![X30 : $i, X31 : $i]:
% 0.59/0.79         (~ (v1_partfun1 @ X31 @ X30)
% 0.59/0.79          | ((k1_relat_1 @ X31) = (X30))
% 0.59/0.79          | ~ (v4_relat_1 @ X31 @ X30)
% 0.59/0.79          | ~ (v1_relat_1 @ X31))),
% 0.59/0.79      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.59/0.79  thf('77', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ~ (v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))
% 0.59/0.79        | ((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['75', '76'])).
% 0.59/0.79  thf('78', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('79', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('80', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('81', plain,
% 0.59/0.79      (((m1_subset_1 @ sk_C @ 
% 0.59/0.79         (k1_zfmisc_1 @ 
% 0.59/0.79          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['79', '80'])).
% 0.59/0.79  thf('82', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('83', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.79  thf('84', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.79         ((v4_relat_1 @ X18 @ X19)
% 0.59/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.79  thf('85', plain, ((v4_relat_1 @ sk_C @ (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['83', '84'])).
% 0.59/0.79  thf('86', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['77', '78', '85'])).
% 0.59/0.79  thf('87', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['70', '86'])).
% 0.59/0.79  thf('88', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('89', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('90', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('91', plain,
% 0.59/0.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.59/0.79         = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('92', plain,
% 0.59/0.79      ((((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.59/0.79          = (k2_struct_0 @ sk_B))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['90', '91'])).
% 0.59/0.79  thf('93', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('94', plain,
% 0.59/0.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.59/0.79         = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('demod', [status(thm)], ['92', '93'])).
% 0.59/0.79  thf('95', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('96', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('97', plain,
% 0.59/0.79      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79         = (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.59/0.79  thf('98', plain,
% 0.59/0.79      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79          = (k2_relat_1 @ sk_C))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['89', '97'])).
% 0.59/0.79  thf('99', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('100', plain,
% 0.59/0.79      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79         = (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['98', '99'])).
% 0.59/0.79  thf('101', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['77', '78', '85'])).
% 0.59/0.79  thf('102', plain,
% 0.59/0.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79         = (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.79  thf('103', plain,
% 0.59/0.79      ((((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79          = (k2_funct_1 @ sk_C))
% 0.59/0.79        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('demod', [status(thm)], ['58', '59', '87', '88', '102'])).
% 0.59/0.79  thf('104', plain,
% 0.59/0.79      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79         = (k2_funct_1 @ sk_C))),
% 0.59/0.79      inference('simplify', [status(thm)], ['103'])).
% 0.59/0.79  thf('105', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['77', '78', '85'])).
% 0.59/0.79  thf('106', plain,
% 0.59/0.79      ((((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.79          (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_A))))),
% 0.59/0.79      inference('demod', [status(thm)],
% 0.59/0.79                ['9', '14', '49', '50', '51', '104', '105'])).
% 0.59/0.79  thf('107', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.79      inference('demod', [status(thm)], ['54', '55'])).
% 0.59/0.79  thf(t31_funct_2, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.79       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.59/0.79         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.59/0.79           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.59/0.79           ( m1_subset_1 @
% 0.59/0.79             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.59/0.79  thf('108', plain,
% 0.59/0.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X32)
% 0.59/0.79          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.59/0.79          | (m1_subset_1 @ (k2_funct_1 @ X32) @ 
% 0.59/0.79             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.59/0.79          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.59/0.79          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.59/0.79          | ~ (v1_funct_1 @ X32))),
% 0.59/0.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.59/0.79  thf('109', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.59/0.79        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.79           (k1_zfmisc_1 @ 
% 0.59/0.79            (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.59/0.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79            != (k2_relat_1 @ sk_C))
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['107', '108'])).
% 0.59/0.79  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('111', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['70', '86'])).
% 0.59/0.79  thf('112', plain,
% 0.59/0.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79         = (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.79  thf('113', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('114', plain,
% 0.59/0.79      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.79         (k1_zfmisc_1 @ 
% 0.59/0.79          (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))
% 0.59/0.79        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 0.59/0.79  thf('115', plain,
% 0.59/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['114'])).
% 0.59/0.79  thf('116', plain,
% 0.59/0.79      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.59/0.79          | (v1_partfun1 @ X27 @ X28)
% 0.59/0.79          | ~ (v1_funct_2 @ X27 @ X28 @ X29)
% 0.59/0.79          | ~ (v1_funct_1 @ X27)
% 0.59/0.79          | (v1_xboole_0 @ X29))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.59/0.79  thf('117', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.59/0.79        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.79        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.59/0.79             (k1_relat_1 @ sk_C))
% 0.59/0.79        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['115', '116'])).
% 0.59/0.79  thf('118', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.79      inference('demod', [status(thm)], ['54', '55'])).
% 0.59/0.79  thf('119', plain,
% 0.59/0.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X32)
% 0.59/0.79          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.59/0.79          | (v1_funct_1 @ (k2_funct_1 @ X32))
% 0.59/0.79          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.59/0.79          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.59/0.79          | ~ (v1_funct_1 @ X32))),
% 0.59/0.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.59/0.79  thf('120', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.59/0.79        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79            != (k2_relat_1 @ sk_C))
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['118', '119'])).
% 0.59/0.79  thf('121', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('122', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['70', '86'])).
% 0.59/0.79  thf('123', plain,
% 0.59/0.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79         = (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.79  thf('124', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('125', plain,
% 0.59/0.79      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.79        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('demod', [status(thm)], ['120', '121', '122', '123', '124'])).
% 0.59/0.79  thf('126', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.79      inference('simplify', [status(thm)], ['125'])).
% 0.59/0.79  thf('127', plain,
% 0.59/0.79      ((m1_subset_1 @ sk_C @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.79      inference('demod', [status(thm)], ['54', '55'])).
% 0.59/0.79  thf('128', plain,
% 0.59/0.79      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X32)
% 0.59/0.79          | ((k2_relset_1 @ X34 @ X33 @ X32) != (X33))
% 0.59/0.79          | (v1_funct_2 @ (k2_funct_1 @ X32) @ X33 @ X34)
% 0.59/0.79          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.59/0.79          | ~ (v1_funct_2 @ X32 @ X34 @ X33)
% 0.59/0.79          | ~ (v1_funct_1 @ X32))),
% 0.59/0.79      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.59/0.79  thf('129', plain,
% 0.59/0.79      ((~ (v1_funct_1 @ sk_C)
% 0.59/0.79        | ~ (v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.59/0.79        | (v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.59/0.79           (k1_relat_1 @ sk_C))
% 0.59/0.79        | ((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79            != (k2_relat_1 @ sk_C))
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['127', '128'])).
% 0.59/0.79  thf('130', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('131', plain,
% 0.59/0.79      ((v1_funct_2 @ sk_C @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['70', '86'])).
% 0.59/0.79  thf('132', plain,
% 0.59/0.79      (((k2_relset_1 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79         = (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['100', '101'])).
% 0.59/0.79  thf('133', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('134', plain,
% 0.59/0.79      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.59/0.79         (k1_relat_1 @ sk_C))
% 0.59/0.79        | ((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 0.59/0.79  thf('135', plain,
% 0.59/0.79      ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ 
% 0.59/0.79        (k1_relat_1 @ sk_C))),
% 0.59/0.79      inference('simplify', [status(thm)], ['134'])).
% 0.59/0.79  thf('136', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.59/0.79        | (v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('demod', [status(thm)], ['117', '126', '135'])).
% 0.59/0.79  thf('137', plain,
% 0.59/0.79      (![X30 : $i, X31 : $i]:
% 0.59/0.79         (~ (v1_partfun1 @ X31 @ X30)
% 0.59/0.79          | ((k1_relat_1 @ X31) = (X30))
% 0.59/0.79          | ~ (v4_relat_1 @ X31 @ X30)
% 0.59/0.79          | ~ (v1_relat_1 @ X31))),
% 0.59/0.79      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.59/0.79  thf('138', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.59/0.79        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.79        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))
% 0.59/0.79        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['136', '137'])).
% 0.59/0.79  thf('139', plain,
% 0.59/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['114'])).
% 0.59/0.79  thf('140', plain,
% 0.59/0.79      (![X4 : $i, X5 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.59/0.79          | (v1_relat_1 @ X4)
% 0.59/0.79          | ~ (v1_relat_1 @ X5))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.59/0.79  thf('141', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ 
% 0.59/0.79           (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C)))
% 0.59/0.79        | (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['139', '140'])).
% 0.59/0.79  thf('142', plain,
% 0.59/0.79      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.59/0.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.59/0.79  thf('143', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['141', '142'])).
% 0.59/0.79  thf('144', plain,
% 0.59/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['114'])).
% 0.59/0.79  thf('145', plain,
% 0.59/0.79      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.59/0.79         ((v4_relat_1 @ X18 @ X19)
% 0.59/0.79          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.59/0.79      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.79  thf('146', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['144', '145'])).
% 0.59/0.79  thf('147', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.59/0.79        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('demod', [status(thm)], ['138', '143', '146'])).
% 0.59/0.79  thf('148', plain,
% 0.59/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['114'])).
% 0.59/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.59/0.79  thf('149', plain,
% 0.59/0.79      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.79         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.59/0.79          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.59/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.59/0.79  thf('150', plain,
% 0.59/0.79      (((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.79         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['148', '149'])).
% 0.59/0.79  thf('151', plain,
% 0.59/0.79      (((k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C)
% 0.59/0.79         = (k2_funct_1 @ sk_C))),
% 0.59/0.79      inference('simplify', [status(thm)], ['103'])).
% 0.59/0.79  thf('152', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('153', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('154', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('155', plain,
% 0.59/0.79      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          != (k2_struct_0 @ sk_B)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('split', [status(esa)], ['2'])).
% 0.59/0.79  thf('156', plain,
% 0.59/0.79      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79           != (k2_struct_0 @ sk_B))
% 0.59/0.79         | ~ (l1_struct_0 @ sk_B)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['154', '155'])).
% 0.59/0.79  thf('157', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('158', plain,
% 0.59/0.79      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          != (k2_struct_0 @ sk_B)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['156', '157'])).
% 0.59/0.79  thf('159', plain,
% 0.59/0.79      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.79           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79           != (k2_struct_0 @ sk_B))
% 0.59/0.79         | ~ (l1_struct_0 @ sk_A)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['153', '158'])).
% 0.59/0.79  thf('160', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('161', plain,
% 0.59/0.79      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          != (k2_struct_0 @ sk_B)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['159', '160'])).
% 0.59/0.79  thf('162', plain,
% 0.59/0.79      (((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.79           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79           != (k2_struct_0 @ sk_B))
% 0.59/0.79         | ~ (l1_struct_0 @ sk_B)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['152', '161'])).
% 0.59/0.79  thf('163', plain, ((l1_struct_0 @ sk_B)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('164', plain,
% 0.59/0.79      ((((k1_relset_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          != (k2_struct_0 @ sk_B)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['162', '163'])).
% 0.59/0.79  thf('165', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('166', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['77', '78', '85'])).
% 0.59/0.79  thf('167', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['40', '45', '48'])).
% 0.59/0.79  thf('168', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('169', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.59/0.79      inference('sup+', [status(thm)], ['12', '13'])).
% 0.59/0.79  thf('170', plain,
% 0.59/0.79      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.79          (k2_tops_2 @ (k1_relat_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_C))
% 0.59/0.79          != (k2_relat_1 @ sk_C)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)],
% 0.59/0.79                ['164', '165', '166', '167', '168', '169'])).
% 0.59/0.79  thf('171', plain,
% 0.59/0.79      ((((k1_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.79          (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['151', '170'])).
% 0.59/0.79  thf('172', plain,
% 0.59/0.79      ((((k1_relat_1 @ (k2_funct_1 @ sk_C)) != (k2_relat_1 @ sk_C)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['150', '171'])).
% 0.59/0.79  thf('173', plain,
% 0.59/0.79      (((((k2_relat_1 @ sk_C) != (k2_relat_1 @ sk_C))
% 0.59/0.79         | (v1_xboole_0 @ (k1_relat_1 @ sk_C))))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['147', '172'])).
% 0.59/0.79  thf('174', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k1_relat_1 @ sk_C)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['173'])).
% 0.59/0.79  thf(l13_xboole_0, axiom,
% 0.59/0.79    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.79  thf('175', plain,
% 0.59/0.79      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.79      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.79  thf('176', plain,
% 0.59/0.79      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['174', '175'])).
% 0.59/0.79  thf(t65_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.79         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.79  thf('177', plain,
% 0.59/0.79      (![X13 : $i]:
% 0.59/0.79         (((k1_relat_1 @ X13) != (k1_xboole_0))
% 0.59/0.79          | ((k2_relat_1 @ X13) = (k1_xboole_0))
% 0.59/0.79          | ~ (v1_relat_1 @ X13))),
% 0.59/0.79      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.59/0.79  thf('178', plain,
% 0.59/0.79      (((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.79         | ~ (v1_relat_1 @ sk_C)
% 0.59/0.79         | ((k2_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['176', '177'])).
% 0.59/0.79  thf('179', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('180', plain,
% 0.59/0.79      (((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.79         | ((k2_relat_1 @ sk_C) = (k1_xboole_0))))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['178', '179'])).
% 0.59/0.79  thf('181', plain,
% 0.59/0.79      ((((k2_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['180'])).
% 0.59/0.79  thf('182', plain, (~ (v1_xboole_0 @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('clc', [status(thm)], ['35', '36'])).
% 0.59/0.79  thf('183', plain,
% 0.59/0.79      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['181', '182'])).
% 0.59/0.79  thf('184', plain,
% 0.59/0.79      (((v1_xboole_0 @ (k1_relat_1 @ sk_C)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['173'])).
% 0.59/0.79  thf('185', plain,
% 0.59/0.79      ((((k1_relat_1 @ sk_C) = (k1_xboole_0)))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['174', '175'])).
% 0.59/0.79  thf('186', plain,
% 0.59/0.79      (((v1_xboole_0 @ k1_xboole_0))
% 0.59/0.79         <= (~
% 0.59/0.79             (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79                (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79                = (k2_struct_0 @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['184', '185'])).
% 0.59/0.79  thf('187', plain,
% 0.59/0.79      ((((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          = (k2_struct_0 @ sk_B)))),
% 0.59/0.79      inference('demod', [status(thm)], ['183', '186'])).
% 0.59/0.79  thf('188', plain,
% 0.59/0.79      (~
% 0.59/0.79       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          = (k2_struct_0 @ sk_A))) | 
% 0.59/0.79       ~
% 0.59/0.79       (((k1_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          = (k2_struct_0 @ sk_B)))),
% 0.59/0.79      inference('split', [status(esa)], ['2'])).
% 0.59/0.79  thf('189', plain,
% 0.59/0.79      (~
% 0.59/0.79       (((k2_relset_1 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.59/0.79          (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C))
% 0.59/0.79          = (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sat_resolution*', [status(thm)], ['187', '188'])).
% 0.59/0.79  thf('190', plain,
% 0.59/0.79      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.79         (k2_funct_1 @ sk_C)) != (k1_relat_1 @ sk_C))),
% 0.59/0.79      inference('simpl_trail', [status(thm)], ['106', '189'])).
% 0.59/0.79  thf('191', plain,
% 0.59/0.79      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.59/0.79        (k1_zfmisc_1 @ 
% 0.59/0.79         (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['114'])).
% 0.59/0.79  thf('192', plain,
% 0.59/0.79      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.79         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 0.59/0.79          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.59/0.79      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.59/0.79  thf('193', plain,
% 0.59/0.79      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.79         (k2_funct_1 @ sk_C)) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['191', '192'])).
% 0.59/0.79  thf(t155_funct_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.79       ( ( v2_funct_1 @ B ) =>
% 0.59/0.79         ( ( k10_relat_1 @ B @ A ) = ( k9_relat_1 @ ( k2_funct_1 @ B ) @ A ) ) ) ))).
% 0.59/0.79  thf('194', plain,
% 0.59/0.79      (![X14 : $i, X15 : $i]:
% 0.59/0.79         (~ (v2_funct_1 @ X14)
% 0.59/0.79          | ((k10_relat_1 @ X14 @ X15)
% 0.59/0.79              = (k9_relat_1 @ (k2_funct_1 @ X14) @ X15))
% 0.59/0.79          | ~ (v1_funct_1 @ X14)
% 0.59/0.79          | ~ (v1_relat_1 @ X14))),
% 0.59/0.79      inference('cnf', [status(esa)], [t155_funct_1])).
% 0.59/0.79  thf('195', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))),
% 0.59/0.79      inference('sup-', [status(thm)], ['144', '145'])).
% 0.59/0.79  thf(t209_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.59/0.79       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.59/0.79  thf('196', plain,
% 0.59/0.79      (![X11 : $i, X12 : $i]:
% 0.59/0.79         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.59/0.79          | ~ (v4_relat_1 @ X11 @ X12)
% 0.59/0.79          | ~ (v1_relat_1 @ X11))),
% 0.59/0.79      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.59/0.79  thf('197', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.79        | ((k2_funct_1 @ sk_C)
% 0.59/0.79            = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['195', '196'])).
% 0.59/0.79  thf('198', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['141', '142'])).
% 0.59/0.79  thf('199', plain,
% 0.59/0.79      (((k2_funct_1 @ sk_C)
% 0.59/0.79         = (k7_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('demod', [status(thm)], ['197', '198'])).
% 0.59/0.79  thf(t148_relat_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ B ) =>
% 0.59/0.79       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.59/0.79  thf('200', plain,
% 0.59/0.79      (![X9 : $i, X10 : $i]:
% 0.59/0.79         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.59/0.79          | ~ (v1_relat_1 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.79  thf('201', plain,
% 0.59/0.79      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.79          = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))
% 0.59/0.79        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['199', '200'])).
% 0.59/0.79  thf('202', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['141', '142'])).
% 0.59/0.79  thf('203', plain,
% 0.59/0.79      (((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.79         = (k9_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C)))),
% 0.59/0.79      inference('demod', [status(thm)], ['201', '202'])).
% 0.59/0.79  thf('204', plain,
% 0.59/0.79      ((((k2_relat_1 @ (k2_funct_1 @ sk_C))
% 0.59/0.79          = (k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ~ (v1_funct_1 @ sk_C)
% 0.59/0.79        | ~ (v2_funct_1 @ sk_C))),
% 0.59/0.79      inference('sup+', [status(thm)], ['194', '203'])).
% 0.59/0.79  thf('205', plain,
% 0.59/0.79      (![X35 : $i]:
% 0.59/0.79         (((k2_struct_0 @ X35) = (u1_struct_0 @ X35)) | ~ (l1_struct_0 @ X35))),
% 0.59/0.79      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.59/0.79  thf('206', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.59/0.79  thf('207', plain,
% 0.59/0.79      (![X11 : $i, X12 : $i]:
% 0.59/0.79         (((X11) = (k7_relat_1 @ X11 @ X12))
% 0.59/0.79          | ~ (v4_relat_1 @ X11 @ X12)
% 0.59/0.79          | ~ (v1_relat_1 @ X11))),
% 0.59/0.79      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.59/0.79  thf('208', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['206', '207'])).
% 0.59/0.79  thf('209', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('210', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['208', '209'])).
% 0.59/0.79  thf('211', plain,
% 0.59/0.79      ((((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.59/0.79        | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.79      inference('sup+', [status(thm)], ['205', '210'])).
% 0.59/0.79  thf('212', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('213', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['211', '212'])).
% 0.59/0.79  thf('214', plain,
% 0.59/0.79      (![X9 : $i, X10 : $i]:
% 0.59/0.79         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.59/0.79          | ~ (v1_relat_1 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.79  thf(t146_relat_1, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( v1_relat_1 @ A ) =>
% 0.59/0.79       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.59/0.79  thf('215', plain,
% 0.59/0.79      (![X8 : $i]:
% 0.59/0.79         (((k9_relat_1 @ X8 @ (k1_relat_1 @ X8)) = (k2_relat_1 @ X8))
% 0.59/0.79          | ~ (v1_relat_1 @ X8))),
% 0.59/0.79      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.59/0.79  thf(d10_xboole_0, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.79  thf('216', plain,
% 0.59/0.79      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.79  thf('217', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.59/0.79      inference('simplify', [status(thm)], ['216'])).
% 0.59/0.79  thf(t164_funct_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.79       ( ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & ( v2_funct_1 @ B ) ) =>
% 0.59/0.79         ( ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.59/0.79  thf('218', plain,
% 0.59/0.79      (![X16 : $i, X17 : $i]:
% 0.59/0.79         (~ (r1_tarski @ X16 @ (k1_relat_1 @ X17))
% 0.59/0.79          | ~ (v2_funct_1 @ X17)
% 0.59/0.79          | ((k10_relat_1 @ X17 @ (k9_relat_1 @ X17 @ X16)) = (X16))
% 0.59/0.79          | ~ (v1_funct_1 @ X17)
% 0.59/0.79          | ~ (v1_relat_1 @ X17))),
% 0.59/0.79      inference('cnf', [status(esa)], [t164_funct_1])).
% 0.59/0.79  thf('219', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v1_funct_1 @ X0)
% 0.59/0.79          | ((k10_relat_1 @ X0 @ (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.59/0.79              = (k1_relat_1 @ X0))
% 0.59/0.79          | ~ (v2_funct_1 @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['217', '218'])).
% 0.59/0.79  thf('220', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0))
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ~ (v2_funct_1 @ X0)
% 0.59/0.79          | ~ (v1_funct_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0))),
% 0.59/0.79      inference('sup+', [status(thm)], ['215', '219'])).
% 0.59/0.79  thf('221', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         (~ (v1_funct_1 @ X0)
% 0.59/0.79          | ~ (v2_funct_1 @ X0)
% 0.59/0.79          | ~ (v1_relat_1 @ X0)
% 0.59/0.79          | ((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) = (k1_relat_1 @ X0)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['220'])).
% 0.59/0.79  thf('222', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i]:
% 0.59/0.79         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ (k9_relat_1 @ X1 @ X0))
% 0.59/0.79            = (k1_relat_1 @ (k7_relat_1 @ X1 @ X0)))
% 0.59/0.79          | ~ (v1_relat_1 @ X1)
% 0.59/0.79          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.59/0.79          | ~ (v2_funct_1 @ (k7_relat_1 @ X1 @ X0))
% 0.59/0.79          | ~ (v1_funct_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['214', '221'])).
% 0.59/0.79  thf('223', plain,
% 0.59/0.79      ((~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.59/0.79        | ~ (v2_funct_1 @ (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.59/0.79        | ~ (v1_relat_1 @ sk_C)
% 0.59/0.79        | ((k10_relat_1 @ (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)) @ 
% 0.59/0.79            (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))
% 0.59/0.79            = (k1_relat_1 @ (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['213', '222'])).
% 0.59/0.79  thf('224', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('225', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['211', '212'])).
% 0.59/0.79  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('227', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['211', '212'])).
% 0.59/0.79  thf('228', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('229', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('230', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['211', '212'])).
% 0.59/0.79  thf('231', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['211', '212'])).
% 0.59/0.79  thf('232', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('233', plain,
% 0.59/0.79      (![X9 : $i, X10 : $i]:
% 0.59/0.79         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.59/0.79          | ~ (v1_relat_1 @ X9))),
% 0.59/0.79      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.59/0.79  thf('234', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((k2_relat_1 @ (k7_relat_1 @ sk_C @ X0)) = (k9_relat_1 @ sk_C @ X0))),
% 0.59/0.79      inference('sup-', [status(thm)], ['232', '233'])).
% 0.59/0.79  thf('235', plain,
% 0.59/0.79      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['231', '234'])).
% 0.59/0.79  thf('236', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k2_struct_0 @ sk_A)))),
% 0.59/0.79      inference('demod', [status(thm)], ['211', '212'])).
% 0.59/0.79  thf('237', plain,
% 0.59/0.79      (((k10_relat_1 @ sk_C @ (k2_relat_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)],
% 0.59/0.79                ['223', '224', '225', '226', '227', '228', '229', '230', 
% 0.59/0.79                 '235', '236'])).
% 0.59/0.79  thf('238', plain, ((v1_relat_1 @ sk_C)),
% 0.59/0.79      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('239', plain, ((v1_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('240', plain, ((v2_funct_1 @ sk_C)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('241', plain,
% 0.59/0.79      (((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['204', '237', '238', '239', '240'])).
% 0.59/0.79  thf('242', plain,
% 0.59/0.79      (((k2_relset_1 @ (k2_relat_1 @ sk_C) @ (k1_relat_1 @ sk_C) @ 
% 0.59/0.79         (k2_funct_1 @ sk_C)) = (k1_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['193', '241'])).
% 0.59/0.79  thf('243', plain, (((k1_relat_1 @ sk_C) != (k1_relat_1 @ sk_C))),
% 0.59/0.79      inference('demod', [status(thm)], ['190', '242'])).
% 0.59/0.79  thf('244', plain, ($false), inference('simplify', [status(thm)], ['243'])).
% 0.59/0.79  
% 0.59/0.79  % SZS output end Refutation
% 0.59/0.79  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
