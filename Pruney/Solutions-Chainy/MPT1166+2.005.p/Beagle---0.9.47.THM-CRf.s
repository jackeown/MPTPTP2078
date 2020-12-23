%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:50 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.52s
% Verified   : 
% Statistics : Number of formulae       :  221 (2115 expanded)
%              Number of leaves         :   24 ( 823 expanded)
%              Depth                    :   16
%              Number of atoms          :  806 (12048 expanded)
%              Number of equality atoms :  131 (1555 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_orders_2,type,(
    k3_orders_2: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(m1_orders_2,type,(
    m1_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(r2_orders_2,type,(
    r2_orders_2: ( $i * $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_127,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v3_orders_2(A)
          & v4_orders_2(A)
          & v5_orders_2(A)
          & l1_orders_2(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( B != k1_xboole_0
                    & m1_orders_2(B,A,C)
                    & m1_orders_2(C,A,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( ( B != k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> ? [D] :
                        ( m1_subset_1(D,u1_struct_0(A))
                        & r2_hidden(D,B)
                        & C = k3_orders_2(A,B,D) ) ) )
                & ( B = k1_xboole_0
                 => ( m1_orders_2(C,A,B)
                  <=> C = k1_xboole_0 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & v4_orders_2(A)
        & v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                 => ( r2_hidden(B,k3_orders_2(A,D,C))
                  <=> ( r2_orders_2(A,B,C)
                      & r2_hidden(B,D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_75,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ~ ( r2_orders_2(A,B,C)
                  & r2_orders_2(A,C,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).

tff(c_24,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_22,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_12,plain,(
    ! [A_1,B_13,C_19] :
      ( m1_subset_1('#skF_1'(A_1,B_13,C_19),u1_struct_0(A_1))
      | ~ m1_orders_2(C_19,A_1,B_13)
      | k1_xboole_0 = B_13
      | ~ m1_subset_1(C_19,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_735,plain,(
    ! [A_146,B_147,C_148] :
      ( k3_orders_2(A_146,B_147,'#skF_1'(A_146,B_147,C_148)) = C_148
      | ~ m1_orders_2(C_148,A_146,B_147)
      | k1_xboole_0 = B_147
      | ~ m1_subset_1(C_148,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0(A_146)))
      | ~ l1_orders_2(A_146)
      | ~ v5_orders_2(A_146)
      | ~ v4_orders_2(A_146)
      | ~ v3_orders_2(A_146)
      | v2_struct_0(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_739,plain,(
    ! [B_147] :
      ( k3_orders_2('#skF_2',B_147,'#skF_1'('#skF_2',B_147,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_147)
      | k1_xboole_0 = B_147
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_735])).

tff(c_748,plain,(
    ! [B_147] :
      ( k3_orders_2('#skF_2',B_147,'#skF_1'('#skF_2',B_147,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_147)
      | k1_xboole_0 = B_147
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_739])).

tff(c_754,plain,(
    ! [B_149] :
      ( k3_orders_2('#skF_2',B_149,'#skF_1'('#skF_2',B_149,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_149)
      | k1_xboole_0 = B_149
      | ~ m1_subset_1(B_149,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_748])).

tff(c_760,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_754])).

tff(c_768,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_760])).

tff(c_769,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_768])).

tff(c_18,plain,(
    ! [B_38,D_44,A_30,C_42] :
      ( r2_hidden(B_38,D_44)
      | ~ r2_hidden(B_38,k3_orders_2(A_30,D_44,C_42))
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(C_42,u1_struct_0(A_30))
      | ~ m1_subset_1(B_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_774,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_18])).

tff(c_781,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_774])).

tff(c_782,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_781])).

tff(c_798,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_782])).

tff(c_801,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_798])).

tff(c_804,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_22,c_801])).

tff(c_806,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26,c_804])).

tff(c_808,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_782])).

tff(c_330,plain,(
    ! [A_92,B_93,C_94] :
      ( r2_hidden('#skF_1'(A_92,B_93,C_94),B_93)
      | ~ m1_orders_2(C_94,A_92,B_93)
      | k1_xboole_0 = B_93
      | ~ m1_subset_1(C_94,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0(A_92)))
      | ~ l1_orders_2(A_92)
      | ~ v5_orders_2(A_92)
      | ~ v4_orders_2(A_92)
      | ~ v3_orders_2(A_92)
      | v2_struct_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_334,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'('#skF_2',B_93,'#skF_4'),B_93)
      | ~ m1_orders_2('#skF_4','#skF_2',B_93)
      | k1_xboole_0 = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_330])).

tff(c_343,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'('#skF_2',B_93,'#skF_4'),B_93)
      | ~ m1_orders_2('#skF_4','#skF_2',B_93)
      | k1_xboole_0 = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_334])).

tff(c_352,plain,(
    ! [B_95] :
      ( r2_hidden('#skF_1'('#skF_2',B_95,'#skF_4'),B_95)
      | ~ m1_orders_2('#skF_4','#skF_2',B_95)
      | k1_xboole_0 = B_95
      | ~ m1_subset_1(B_95,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_343])).

tff(c_358,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_352])).

tff(c_363,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_358])).

tff(c_364,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_363])).

tff(c_418,plain,(
    ! [A_109,B_110,C_111] :
      ( k3_orders_2(A_109,B_110,'#skF_1'(A_109,B_110,C_111)) = C_111
      | ~ m1_orders_2(C_111,A_109,B_110)
      | k1_xboole_0 = B_110
      | ~ m1_subset_1(C_111,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0(A_109)))
      | ~ l1_orders_2(A_109)
      | ~ v5_orders_2(A_109)
      | ~ v4_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_422,plain,(
    ! [B_110] :
      ( k3_orders_2('#skF_2',B_110,'#skF_1'('#skF_2',B_110,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_110)
      | k1_xboole_0 = B_110
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_418])).

tff(c_431,plain,(
    ! [B_110] :
      ( k3_orders_2('#skF_2',B_110,'#skF_1'('#skF_2',B_110,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_110)
      | k1_xboole_0 = B_110
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_422])).

tff(c_437,plain,(
    ! [B_112] :
      ( k3_orders_2('#skF_2',B_112,'#skF_1'('#skF_2',B_112,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_112)
      | k1_xboole_0 = B_112
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_431])).

tff(c_443,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_437])).

tff(c_449,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_443])).

tff(c_450,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_449])).

tff(c_455,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_18])).

tff(c_462,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_455])).

tff(c_463,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_462])).

tff(c_465,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_463])).

tff(c_468,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_465])).

tff(c_471,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_22,c_468])).

tff(c_473,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26,c_471])).

tff(c_475,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_463])).

tff(c_360,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_4'),'#skF_4')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_352])).

tff(c_365,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_336,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'('#skF_2',B_93,'#skF_3'),B_93)
      | ~ m1_orders_2('#skF_3','#skF_2',B_93)
      | k1_xboole_0 = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_330])).

tff(c_347,plain,(
    ! [B_93] :
      ( r2_hidden('#skF_1'('#skF_2',B_93,'#skF_3'),B_93)
      | ~ m1_orders_2('#skF_3','#skF_2',B_93)
      | k1_xboole_0 = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_336])).

tff(c_366,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_2',B_96,'#skF_3'),B_96)
      | ~ m1_orders_2('#skF_3','#skF_2',B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_347])).

tff(c_370,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_366])).

tff(c_376,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_370])).

tff(c_380,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_376])).

tff(c_109,plain,(
    ! [A_71,B_72,C_73] :
      ( k3_orders_2(A_71,B_72,'#skF_1'(A_71,B_72,C_73)) = C_73
      | ~ m1_orders_2(C_73,A_71,B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(C_73,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0(A_71)))
      | ~ l1_orders_2(A_71)
      | ~ v5_orders_2(A_71)
      | ~ v4_orders_2(A_71)
      | ~ v3_orders_2(A_71)
      | v2_struct_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_111,plain,(
    ! [B_72] :
      ( k3_orders_2('#skF_2',B_72,'#skF_1'('#skF_2',B_72,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_109])).

tff(c_116,plain,(
    ! [B_72] :
      ( k3_orders_2('#skF_2',B_72,'#skF_1'('#skF_2',B_72,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_111])).

tff(c_122,plain,(
    ! [B_74] :
      ( k3_orders_2('#skF_2',B_74,'#skF_1'('#skF_2',B_74,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_74)
      | k1_xboole_0 = B_74
      | ~ m1_subset_1(B_74,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_116])).

tff(c_126,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_122])).

tff(c_131,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_126])).

tff(c_132,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_131])).

tff(c_137,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_18])).

tff(c_144,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_137])).

tff(c_145,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_144])).

tff(c_147,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_145])).

tff(c_163,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_147])).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_28,c_22,c_163])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26,c_166])).

tff(c_170,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_145])).

tff(c_57,plain,(
    ! [A_55,B_56,C_57] :
      ( r2_hidden('#skF_1'(A_55,B_56,C_57),B_56)
      | ~ m1_orders_2(C_57,A_55,B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(C_57,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0(A_55)))
      | ~ l1_orders_2(A_55)
      | ~ v5_orders_2(A_55)
      | ~ v4_orders_2(A_55)
      | ~ v3_orders_2(A_55)
      | v2_struct_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_59,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_1'('#skF_2',B_56,'#skF_4'),B_56)
      | ~ m1_orders_2('#skF_4','#skF_2',B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_57])).

tff(c_64,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_1'('#skF_2',B_56,'#skF_4'),B_56)
      | ~ m1_orders_2('#skF_4','#skF_2',B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_59])).

tff(c_70,plain,(
    ! [B_58] :
      ( r2_hidden('#skF_1'('#skF_2',B_58,'#skF_4'),B_58)
      | ~ m1_orders_2('#skF_4','#skF_2',B_58)
      | k1_xboole_0 = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_64])).

tff(c_74,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_78,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_74])).

tff(c_79,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_78])).

tff(c_61,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_1'('#skF_2',B_56,'#skF_3'),B_56)
      | ~ m1_orders_2('#skF_3','#skF_2',B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_68,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_1'('#skF_2',B_56,'#skF_3'),B_56)
      | ~ m1_orders_2('#skF_3','#skF_2',B_56)
      | k1_xboole_0 = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_61])).

tff(c_81,plain,(
    ! [B_59] :
      ( r2_hidden('#skF_1'('#skF_2',B_59,'#skF_3'),B_59)
      | ~ m1_orders_2('#skF_3','#skF_2',B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_68])).

tff(c_83,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_81])).

tff(c_88,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_83])).

tff(c_92,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_43,plain,(
    ! [C_53,A_54] :
      ( k1_xboole_0 = C_53
      | ~ m1_orders_2(C_53,A_54,k1_xboole_0)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_54)))
      | ~ l1_orders_2(A_54)
      | ~ v5_orders_2(A_54)
      | ~ v4_orders_2(A_54)
      | ~ v3_orders_2(A_54)
      | v2_struct_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_47,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_43])).

tff(c_54,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_47])).

tff(c_55,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_26,c_54])).

tff(c_56,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_96,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_56])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_96])).

tff(c_104,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_113,plain,(
    ! [B_72] :
      ( k3_orders_2('#skF_2',B_72,'#skF_1'('#skF_2',B_72,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_109])).

tff(c_120,plain,(
    ! [B_72] :
      ( k3_orders_2('#skF_2',B_72,'#skF_1'('#skF_2',B_72,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_72)
      | k1_xboole_0 = B_72
      | ~ m1_subset_1(B_72,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_113])).

tff(c_185,plain,(
    ! [B_80] :
      ( k3_orders_2('#skF_2',B_80,'#skF_1'('#skF_2',B_80,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_80)
      | k1_xboole_0 = B_80
      | ~ m1_subset_1(B_80,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_120])).

tff(c_187,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_185])).

tff(c_192,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_187])).

tff(c_193,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_192])).

tff(c_200,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_18])).

tff(c_207,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_200])).

tff(c_208,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_207])).

tff(c_210,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_213,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_210])).

tff(c_216,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_30,c_24,c_213])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_104,c_216])).

tff(c_240,plain,(
    ! [B_85] :
      ( r2_hidden(B_85,'#skF_4')
      | ~ r2_hidden(B_85,'#skF_3')
      | ~ m1_subset_1(B_85,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_246,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_240])).

tff(c_256,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_246])).

tff(c_20,plain,(
    ! [A_30,B_38,C_42,D_44] :
      ( r2_orders_2(A_30,B_38,C_42)
      | ~ r2_hidden(B_38,k3_orders_2(A_30,D_44,C_42))
      | ~ m1_subset_1(D_44,k1_zfmisc_1(u1_struct_0(A_30)))
      | ~ m1_subset_1(C_42,u1_struct_0(A_30))
      | ~ m1_subset_1(B_38,u1_struct_0(A_30))
      | ~ l1_orders_2(A_30)
      | ~ v5_orders_2(A_30)
      | ~ v4_orders_2(A_30)
      | ~ v3_orders_2(A_30)
      | v2_struct_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_135,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_20])).

tff(c_141,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_135])).

tff(c_142,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_141])).

tff(c_298,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_142])).

tff(c_299,plain,(
    ! [B_90] :
      ( r2_orders_2('#skF_2',B_90,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_90,'#skF_4')
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_142])).

tff(c_14,plain,(
    ! [A_23,C_29,B_27] :
      ( ~ r2_orders_2(A_23,C_29,B_27)
      | ~ r2_orders_2(A_23,B_27,C_29)
      | ~ m1_subset_1(C_29,u1_struct_0(A_23))
      | ~ m1_subset_1(B_27,u1_struct_0(A_23))
      | ~ l1_orders_2(A_23)
      | ~ v5_orders_2(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_301,plain,(
    ! [B_90] :
      ( ~ r2_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),B_90)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r2_hidden(B_90,'#skF_4')
      | ~ m1_subset_1(B_90,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_299,c_14])).

tff(c_305,plain,(
    ! [B_91] :
      ( ~ r2_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),B_91)
      | ~ r2_hidden(B_91,'#skF_4')
      | ~ m1_subset_1(B_91,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_170,c_301])).

tff(c_309,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_298,c_305])).

tff(c_313,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_256,c_309])).

tff(c_315,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_2,plain,(
    ! [A_1] :
      ( m1_orders_2(k1_xboole_0,A_1,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_1)))
      | ~ l1_orders_2(A_1)
      | ~ v5_orders_2(A_1)
      | ~ v4_orders_2(A_1)
      | ~ v3_orders_2(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_320,plain,
    ( m1_orders_2(k1_xboole_0,'#skF_2',k1_xboole_0)
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_315,c_2])).

tff(c_328,plain,
    ( m1_orders_2(k1_xboole_0,'#skF_2',k1_xboole_0)
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_320])).

tff(c_329,plain,(
    m1_orders_2(k1_xboole_0,'#skF_2',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_328])).

tff(c_385,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_380,c_329])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_365,c_385])).

tff(c_394,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_424,plain,(
    ! [B_110] :
      ( k3_orders_2('#skF_2',B_110,'#skF_1'('#skF_2',B_110,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_110)
      | k1_xboole_0 = B_110
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_418])).

tff(c_435,plain,(
    ! [B_110] :
      ( k3_orders_2('#skF_2',B_110,'#skF_1'('#skF_2',B_110,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_110)
      | k1_xboole_0 = B_110
      | ~ m1_subset_1(B_110,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_424])).

tff(c_490,plain,(
    ! [B_114] :
      ( k3_orders_2('#skF_2',B_114,'#skF_1'('#skF_2',B_114,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_114)
      | k1_xboole_0 = B_114
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_435])).

tff(c_494,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_490])).

tff(c_500,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_494])).

tff(c_501,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_394,c_500])).

tff(c_527,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_18])).

tff(c_534,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_527])).

tff(c_535,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_534])).

tff(c_537,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_540,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_537])).

tff(c_543,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_30,c_24,c_540])).

tff(c_545,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_394,c_543])).

tff(c_547,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_393,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_376])).

tff(c_525,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_4','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_20])).

tff(c_531,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_4','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_525])).

tff(c_532,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_4','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_531])).

tff(c_659,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_4','#skF_3'))
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_547,c_532])).

tff(c_453,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_20])).

tff(c_459,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_453])).

tff(c_460,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_459])).

tff(c_652,plain,(
    ! [B_130] :
      ( r2_orders_2('#skF_2',B_130,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_130,'#skF_4')
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_460])).

tff(c_654,plain,(
    ! [B_130] :
      ( ~ r2_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),B_130)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r2_hidden(B_130,'#skF_4')
      | ~ m1_subset_1(B_130,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_652,c_14])).

tff(c_666,plain,(
    ! [B_132] :
      ( ~ r2_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),B_132)
      | ~ r2_hidden(B_132,'#skF_4')
      | ~ m1_subset_1(B_132,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_475,c_654])).

tff(c_670,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_659,c_666])).

tff(c_678,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_364,c_547,c_393,c_670])).

tff(c_680,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_682,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_1'('#skF_2',B_133,'#skF_3'),B_133)
      | ~ m1_orders_2('#skF_3','#skF_2',B_133)
      | k1_xboole_0 = B_133
      | ~ m1_subset_1(B_133,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_347])).

tff(c_686,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_682])).

tff(c_692,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_686])).

tff(c_697,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_692])).

tff(c_45,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_50,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_45])).

tff(c_51,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50])).

tff(c_350,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_315,c_51])).

tff(c_351,plain,(
    ~ m1_orders_2('#skF_4','#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_350])).

tff(c_700,plain,(
    ~ m1_orders_2('#skF_4','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_351])).

tff(c_710,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_700])).

tff(c_712,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_692])).

tff(c_741,plain,(
    ! [B_147] :
      ( k3_orders_2('#skF_2',B_147,'#skF_1'('#skF_2',B_147,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_147)
      | k1_xboole_0 = B_147
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_735])).

tff(c_752,plain,(
    ! [B_147] :
      ( k3_orders_2('#skF_2',B_147,'#skF_1'('#skF_2',B_147,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_147)
      | k1_xboole_0 = B_147
      | ~ m1_subset_1(B_147,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_741])).

tff(c_842,plain,(
    ! [B_155] :
      ( k3_orders_2('#skF_2',B_155,'#skF_1'('#skF_2',B_155,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_155)
      | k1_xboole_0 = B_155
      | ~ m1_subset_1(B_155,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_752])).

tff(c_846,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_28,c_842])).

tff(c_852,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_846])).

tff(c_853,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_712,c_852])).

tff(c_875,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_853,c_18])).

tff(c_882,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_875])).

tff(c_883,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_882])).

tff(c_885,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_883])).

tff(c_888,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_885])).

tff(c_891,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_28,c_30,c_24,c_888])).

tff(c_893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_712,c_891])).

tff(c_918,plain,(
    ! [B_160] :
      ( r2_hidden(B_160,'#skF_4')
      | ~ r2_hidden(B_160,'#skF_3')
      | ~ m1_subset_1(B_160,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_883])).

tff(c_924,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_808,c_918])).

tff(c_934,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_924])).

tff(c_772,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_20])).

tff(c_778,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_34,c_32,c_30,c_772])).

tff(c_779,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_778])).

tff(c_992,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_779])).

tff(c_993,plain,(
    ! [B_167] :
      ( r2_orders_2('#skF_2',B_167,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_167,'#skF_4')
      | ~ m1_subset_1(B_167,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_779])).

tff(c_995,plain,(
    ! [B_167] :
      ( ~ r2_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),B_167)
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ r2_hidden(B_167,'#skF_4')
      | ~ m1_subset_1(B_167,u1_struct_0('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_993,c_14])).

tff(c_999,plain,(
    ! [B_168] :
      ( ~ r2_orders_2('#skF_2','#skF_1'('#skF_2','#skF_3','#skF_4'),B_168)
      | ~ r2_hidden(B_168,'#skF_4')
      | ~ m1_subset_1(B_168,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_808,c_995])).

tff(c_1003,plain,
    ( ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_992,c_999])).

tff(c_1007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_808,c_934,c_1003])).

tff(c_1008,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_350])).

tff(c_314,plain,(
    ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_1013,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_314])).

tff(c_1020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_1013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:55:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.11/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.63  
% 3.52/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.63  %$ r2_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.52/1.63  
% 3.52/1.63  %Foreground sorts:
% 3.52/1.63  
% 3.52/1.63  
% 3.52/1.63  %Background operators:
% 3.52/1.63  
% 3.52/1.63  
% 3.52/1.63  %Foreground operators:
% 3.52/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.52/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.52/1.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.63  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.52/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.52/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.52/1.63  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.52/1.63  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.52/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.52/1.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.63  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.52/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.63  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.52/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.63  
% 3.52/1.66  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 3.52/1.66  tff(f_60, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d15_orders_2)).
% 3.52/1.66  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t57_orders_2)).
% 3.52/1.66  tff(f_75, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ~(r2_orders_2(A, B, C) & r2_orders_2(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_orders_2)).
% 3.52/1.66  tff(c_24, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_38, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_36, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_34, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_32, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_22, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.52/1.66  tff(c_12, plain, (![A_1, B_13, C_19]: (m1_subset_1('#skF_1'(A_1, B_13, C_19), u1_struct_0(A_1)) | ~m1_orders_2(C_19, A_1, B_13) | k1_xboole_0=B_13 | ~m1_subset_1(C_19, k1_zfmisc_1(u1_struct_0(A_1))) | ~m1_subset_1(B_13, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.52/1.66  tff(c_735, plain, (![A_146, B_147, C_148]: (k3_orders_2(A_146, B_147, '#skF_1'(A_146, B_147, C_148))=C_148 | ~m1_orders_2(C_148, A_146, B_147) | k1_xboole_0=B_147 | ~m1_subset_1(C_148, k1_zfmisc_1(u1_struct_0(A_146))) | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0(A_146))) | ~l1_orders_2(A_146) | ~v5_orders_2(A_146) | ~v4_orders_2(A_146) | ~v3_orders_2(A_146) | v2_struct_0(A_146))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.52/1.66  tff(c_739, plain, (![B_147]: (k3_orders_2('#skF_2', B_147, '#skF_1'('#skF_2', B_147, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_147) | k1_xboole_0=B_147 | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_735])).
% 3.52/1.66  tff(c_748, plain, (![B_147]: (k3_orders_2('#skF_2', B_147, '#skF_1'('#skF_2', B_147, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_147) | k1_xboole_0=B_147 | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_739])).
% 3.52/1.66  tff(c_754, plain, (![B_149]: (k3_orders_2('#skF_2', B_149, '#skF_1'('#skF_2', B_149, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_149) | k1_xboole_0=B_149 | ~m1_subset_1(B_149, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_748])).
% 3.52/1.66  tff(c_760, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_754])).
% 3.52/1.66  tff(c_768, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_760])).
% 3.52/1.66  tff(c_769, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_768])).
% 3.52/1.66  tff(c_18, plain, (![B_38, D_44, A_30, C_42]: (r2_hidden(B_38, D_44) | ~r2_hidden(B_38, k3_orders_2(A_30, D_44, C_42)) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.52/1.66  tff(c_774, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_769, c_18])).
% 3.52/1.66  tff(c_781, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_774])).
% 3.52/1.66  tff(c_782, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_781])).
% 3.52/1.66  tff(c_798, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_782])).
% 3.52/1.66  tff(c_801, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_798])).
% 3.52/1.66  tff(c_804, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_22, c_801])).
% 3.52/1.66  tff(c_806, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_26, c_804])).
% 3.52/1.66  tff(c_808, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_782])).
% 3.52/1.66  tff(c_330, plain, (![A_92, B_93, C_94]: (r2_hidden('#skF_1'(A_92, B_93, C_94), B_93) | ~m1_orders_2(C_94, A_92, B_93) | k1_xboole_0=B_93 | ~m1_subset_1(C_94, k1_zfmisc_1(u1_struct_0(A_92))) | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0(A_92))) | ~l1_orders_2(A_92) | ~v5_orders_2(A_92) | ~v4_orders_2(A_92) | ~v3_orders_2(A_92) | v2_struct_0(A_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.52/1.66  tff(c_334, plain, (![B_93]: (r2_hidden('#skF_1'('#skF_2', B_93, '#skF_4'), B_93) | ~m1_orders_2('#skF_4', '#skF_2', B_93) | k1_xboole_0=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_330])).
% 3.52/1.66  tff(c_343, plain, (![B_93]: (r2_hidden('#skF_1'('#skF_2', B_93, '#skF_4'), B_93) | ~m1_orders_2('#skF_4', '#skF_2', B_93) | k1_xboole_0=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_334])).
% 3.52/1.66  tff(c_352, plain, (![B_95]: (r2_hidden('#skF_1'('#skF_2', B_95, '#skF_4'), B_95) | ~m1_orders_2('#skF_4', '#skF_2', B_95) | k1_xboole_0=B_95 | ~m1_subset_1(B_95, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_343])).
% 3.52/1.66  tff(c_358, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_352])).
% 3.52/1.66  tff(c_363, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_358])).
% 3.52/1.66  tff(c_364, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_363])).
% 3.52/1.66  tff(c_418, plain, (![A_109, B_110, C_111]: (k3_orders_2(A_109, B_110, '#skF_1'(A_109, B_110, C_111))=C_111 | ~m1_orders_2(C_111, A_109, B_110) | k1_xboole_0=B_110 | ~m1_subset_1(C_111, k1_zfmisc_1(u1_struct_0(A_109))) | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0(A_109))) | ~l1_orders_2(A_109) | ~v5_orders_2(A_109) | ~v4_orders_2(A_109) | ~v3_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.52/1.66  tff(c_422, plain, (![B_110]: (k3_orders_2('#skF_2', B_110, '#skF_1'('#skF_2', B_110, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_110) | k1_xboole_0=B_110 | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_418])).
% 3.52/1.66  tff(c_431, plain, (![B_110]: (k3_orders_2('#skF_2', B_110, '#skF_1'('#skF_2', B_110, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_110) | k1_xboole_0=B_110 | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_422])).
% 3.52/1.66  tff(c_437, plain, (![B_112]: (k3_orders_2('#skF_2', B_112, '#skF_1'('#skF_2', B_112, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_112) | k1_xboole_0=B_112 | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_431])).
% 3.52/1.66  tff(c_443, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_437])).
% 3.52/1.66  tff(c_449, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_443])).
% 3.52/1.66  tff(c_450, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_449])).
% 3.52/1.66  tff(c_455, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_450, c_18])).
% 3.52/1.66  tff(c_462, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_455])).
% 3.52/1.66  tff(c_463, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_462])).
% 3.52/1.66  tff(c_465, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_463])).
% 3.52/1.66  tff(c_468, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_465])).
% 3.52/1.66  tff(c_471, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_22, c_468])).
% 3.52/1.66  tff(c_473, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_26, c_471])).
% 3.52/1.66  tff(c_475, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_463])).
% 3.52/1.66  tff(c_360, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_4'), '#skF_4') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_352])).
% 3.52/1.66  tff(c_365, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_360])).
% 3.52/1.66  tff(c_336, plain, (![B_93]: (r2_hidden('#skF_1'('#skF_2', B_93, '#skF_3'), B_93) | ~m1_orders_2('#skF_3', '#skF_2', B_93) | k1_xboole_0=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_330])).
% 3.52/1.66  tff(c_347, plain, (![B_93]: (r2_hidden('#skF_1'('#skF_2', B_93, '#skF_3'), B_93) | ~m1_orders_2('#skF_3', '#skF_2', B_93) | k1_xboole_0=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_336])).
% 3.52/1.66  tff(c_366, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_2', B_96, '#skF_3'), B_96) | ~m1_orders_2('#skF_3', '#skF_2', B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_347])).
% 3.52/1.66  tff(c_370, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_366])).
% 3.52/1.66  tff(c_376, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_370])).
% 3.52/1.66  tff(c_380, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_376])).
% 3.52/1.66  tff(c_109, plain, (![A_71, B_72, C_73]: (k3_orders_2(A_71, B_72, '#skF_1'(A_71, B_72, C_73))=C_73 | ~m1_orders_2(C_73, A_71, B_72) | k1_xboole_0=B_72 | ~m1_subset_1(C_73, k1_zfmisc_1(u1_struct_0(A_71))) | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0(A_71))) | ~l1_orders_2(A_71) | ~v5_orders_2(A_71) | ~v4_orders_2(A_71) | ~v3_orders_2(A_71) | v2_struct_0(A_71))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.52/1.66  tff(c_111, plain, (![B_72]: (k3_orders_2('#skF_2', B_72, '#skF_1'('#skF_2', B_72, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_109])).
% 3.52/1.66  tff(c_116, plain, (![B_72]: (k3_orders_2('#skF_2', B_72, '#skF_1'('#skF_2', B_72, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_111])).
% 3.52/1.66  tff(c_122, plain, (![B_74]: (k3_orders_2('#skF_2', B_74, '#skF_1'('#skF_2', B_74, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_74) | k1_xboole_0=B_74 | ~m1_subset_1(B_74, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_116])).
% 3.52/1.66  tff(c_126, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_122])).
% 3.52/1.66  tff(c_131, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_126])).
% 3.52/1.66  tff(c_132, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_26, c_131])).
% 3.52/1.66  tff(c_137, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_18])).
% 3.52/1.66  tff(c_144, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_137])).
% 3.52/1.66  tff(c_145, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_144])).
% 3.52/1.66  tff(c_147, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_145])).
% 3.52/1.66  tff(c_163, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_147])).
% 3.52/1.66  tff(c_166, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_28, c_22, c_163])).
% 3.52/1.66  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_26, c_166])).
% 3.52/1.66  tff(c_170, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_145])).
% 3.52/1.66  tff(c_57, plain, (![A_55, B_56, C_57]: (r2_hidden('#skF_1'(A_55, B_56, C_57), B_56) | ~m1_orders_2(C_57, A_55, B_56) | k1_xboole_0=B_56 | ~m1_subset_1(C_57, k1_zfmisc_1(u1_struct_0(A_55))) | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0(A_55))) | ~l1_orders_2(A_55) | ~v5_orders_2(A_55) | ~v4_orders_2(A_55) | ~v3_orders_2(A_55) | v2_struct_0(A_55))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.52/1.66  tff(c_59, plain, (![B_56]: (r2_hidden('#skF_1'('#skF_2', B_56, '#skF_4'), B_56) | ~m1_orders_2('#skF_4', '#skF_2', B_56) | k1_xboole_0=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_57])).
% 3.52/1.66  tff(c_64, plain, (![B_56]: (r2_hidden('#skF_1'('#skF_2', B_56, '#skF_4'), B_56) | ~m1_orders_2('#skF_4', '#skF_2', B_56) | k1_xboole_0=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_59])).
% 3.52/1.66  tff(c_70, plain, (![B_58]: (r2_hidden('#skF_1'('#skF_2', B_58, '#skF_4'), B_58) | ~m1_orders_2('#skF_4', '#skF_2', B_58) | k1_xboole_0=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_64])).
% 3.52/1.66  tff(c_74, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_70])).
% 3.52/1.66  tff(c_78, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_74])).
% 3.52/1.66  tff(c_79, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_78])).
% 3.52/1.66  tff(c_61, plain, (![B_56]: (r2_hidden('#skF_1'('#skF_2', B_56, '#skF_3'), B_56) | ~m1_orders_2('#skF_3', '#skF_2', B_56) | k1_xboole_0=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_57])).
% 3.52/1.66  tff(c_68, plain, (![B_56]: (r2_hidden('#skF_1'('#skF_2', B_56, '#skF_3'), B_56) | ~m1_orders_2('#skF_3', '#skF_2', B_56) | k1_xboole_0=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_61])).
% 3.52/1.66  tff(c_81, plain, (![B_59]: (r2_hidden('#skF_1'('#skF_2', B_59, '#skF_3'), B_59) | ~m1_orders_2('#skF_3', '#skF_2', B_59) | k1_xboole_0=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_68])).
% 3.52/1.66  tff(c_83, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_81])).
% 3.52/1.66  tff(c_88, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_83])).
% 3.52/1.66  tff(c_92, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_88])).
% 3.52/1.66  tff(c_43, plain, (![C_53, A_54]: (k1_xboole_0=C_53 | ~m1_orders_2(C_53, A_54, k1_xboole_0) | ~m1_subset_1(C_53, k1_zfmisc_1(u1_struct_0(A_54))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_54))) | ~l1_orders_2(A_54) | ~v5_orders_2(A_54) | ~v4_orders_2(A_54) | ~v3_orders_2(A_54) | v2_struct_0(A_54))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.52/1.66  tff(c_47, plain, (k1_xboole_0='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_43])).
% 3.52/1.66  tff(c_54, plain, (k1_xboole_0='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_47])).
% 3.52/1.66  tff(c_55, plain, (~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_26, c_54])).
% 3.52/1.66  tff(c_56, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_55])).
% 3.52/1.66  tff(c_96, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_56])).
% 3.52/1.66  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_96])).
% 3.52/1.66  tff(c_104, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_88])).
% 3.52/1.66  tff(c_113, plain, (![B_72]: (k3_orders_2('#skF_2', B_72, '#skF_1'('#skF_2', B_72, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_109])).
% 3.52/1.66  tff(c_120, plain, (![B_72]: (k3_orders_2('#skF_2', B_72, '#skF_1'('#skF_2', B_72, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_72) | k1_xboole_0=B_72 | ~m1_subset_1(B_72, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_113])).
% 3.52/1.66  tff(c_185, plain, (![B_80]: (k3_orders_2('#skF_2', B_80, '#skF_1'('#skF_2', B_80, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_80) | k1_xboole_0=B_80 | ~m1_subset_1(B_80, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_120])).
% 3.52/1.66  tff(c_187, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_185])).
% 3.52/1.66  tff(c_192, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_187])).
% 3.52/1.66  tff(c_193, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_104, c_192])).
% 3.52/1.66  tff(c_200, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_18])).
% 3.52/1.66  tff(c_207, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_200])).
% 3.52/1.66  tff(c_208, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_207])).
% 3.52/1.66  tff(c_210, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_208])).
% 3.52/1.66  tff(c_213, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_210])).
% 3.52/1.66  tff(c_216, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_30, c_24, c_213])).
% 3.52/1.66  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_104, c_216])).
% 3.52/1.66  tff(c_240, plain, (![B_85]: (r2_hidden(B_85, '#skF_4') | ~r2_hidden(B_85, '#skF_3') | ~m1_subset_1(B_85, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_208])).
% 3.52/1.66  tff(c_246, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_170, c_240])).
% 3.52/1.66  tff(c_256, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_79, c_246])).
% 3.52/1.66  tff(c_20, plain, (![A_30, B_38, C_42, D_44]: (r2_orders_2(A_30, B_38, C_42) | ~r2_hidden(B_38, k3_orders_2(A_30, D_44, C_42)) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.52/1.66  tff(c_135, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_20])).
% 3.52/1.66  tff(c_141, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_135])).
% 3.52/1.66  tff(c_142, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_141])).
% 3.52/1.66  tff(c_298, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_142])).
% 3.52/1.66  tff(c_299, plain, (![B_90]: (r2_orders_2('#skF_2', B_90, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_90, '#skF_4') | ~m1_subset_1(B_90, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_142])).
% 3.52/1.66  tff(c_14, plain, (![A_23, C_29, B_27]: (~r2_orders_2(A_23, C_29, B_27) | ~r2_orders_2(A_23, B_27, C_29) | ~m1_subset_1(C_29, u1_struct_0(A_23)) | ~m1_subset_1(B_27, u1_struct_0(A_23)) | ~l1_orders_2(A_23) | ~v5_orders_2(A_23))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.52/1.66  tff(c_301, plain, (![B_90]: (~r2_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_4'), B_90) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~r2_hidden(B_90, '#skF_4') | ~m1_subset_1(B_90, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_299, c_14])).
% 3.52/1.66  tff(c_305, plain, (![B_91]: (~r2_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_4'), B_91) | ~r2_hidden(B_91, '#skF_4') | ~m1_subset_1(B_91, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_170, c_301])).
% 3.52/1.66  tff(c_309, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_298, c_305])).
% 3.52/1.66  tff(c_313, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_170, c_256, c_309])).
% 3.52/1.66  tff(c_315, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_55])).
% 3.52/1.66  tff(c_2, plain, (![A_1]: (m1_orders_2(k1_xboole_0, A_1, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_1))) | ~l1_orders_2(A_1) | ~v5_orders_2(A_1) | ~v4_orders_2(A_1) | ~v3_orders_2(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.52/1.66  tff(c_320, plain, (m1_orders_2(k1_xboole_0, '#skF_2', k1_xboole_0) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_315, c_2])).
% 3.52/1.66  tff(c_328, plain, (m1_orders_2(k1_xboole_0, '#skF_2', k1_xboole_0) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_320])).
% 3.52/1.66  tff(c_329, plain, (m1_orders_2(k1_xboole_0, '#skF_2', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_40, c_328])).
% 3.52/1.66  tff(c_385, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_380, c_380, c_329])).
% 3.52/1.66  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_365, c_385])).
% 3.52/1.66  tff(c_394, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_376])).
% 3.52/1.66  tff(c_424, plain, (![B_110]: (k3_orders_2('#skF_2', B_110, '#skF_1'('#skF_2', B_110, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_110) | k1_xboole_0=B_110 | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_418])).
% 3.52/1.66  tff(c_435, plain, (![B_110]: (k3_orders_2('#skF_2', B_110, '#skF_1'('#skF_2', B_110, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_110) | k1_xboole_0=B_110 | ~m1_subset_1(B_110, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_424])).
% 3.52/1.66  tff(c_490, plain, (![B_114]: (k3_orders_2('#skF_2', B_114, '#skF_1'('#skF_2', B_114, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_114) | k1_xboole_0=B_114 | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_435])).
% 3.52/1.66  tff(c_494, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_490])).
% 3.52/1.66  tff(c_500, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_494])).
% 3.52/1.66  tff(c_501, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_394, c_500])).
% 3.52/1.66  tff(c_527, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_501, c_18])).
% 3.52/1.66  tff(c_534, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_527])).
% 3.52/1.66  tff(c_535, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_534])).
% 3.52/1.66  tff(c_537, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_535])).
% 3.52/1.66  tff(c_540, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_537])).
% 3.52/1.66  tff(c_543, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_30, c_24, c_540])).
% 3.52/1.66  tff(c_545, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_394, c_543])).
% 3.52/1.66  tff(c_547, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_535])).
% 3.52/1.66  tff(c_393, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_376])).
% 3.52/1.66  tff(c_525, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_4', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_501, c_20])).
% 3.52/1.66  tff(c_531, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_4', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_525])).
% 3.52/1.66  tff(c_532, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_4', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_531])).
% 3.52/1.66  tff(c_659, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_4', '#skF_3')) | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_547, c_532])).
% 3.52/1.66  tff(c_453, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_450, c_20])).
% 3.52/1.66  tff(c_459, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_453])).
% 3.52/1.66  tff(c_460, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_459])).
% 3.52/1.66  tff(c_652, plain, (![B_130]: (r2_orders_2('#skF_2', B_130, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_130, '#skF_4') | ~m1_subset_1(B_130, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_475, c_460])).
% 3.52/1.66  tff(c_654, plain, (![B_130]: (~r2_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_4'), B_130) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~r2_hidden(B_130, '#skF_4') | ~m1_subset_1(B_130, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_652, c_14])).
% 3.52/1.66  tff(c_666, plain, (![B_132]: (~r2_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_4'), B_132) | ~r2_hidden(B_132, '#skF_4') | ~m1_subset_1(B_132, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_475, c_654])).
% 3.52/1.66  tff(c_670, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_659, c_666])).
% 3.52/1.66  tff(c_678, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_475, c_364, c_547, c_393, c_670])).
% 3.52/1.66  tff(c_680, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_360])).
% 3.52/1.66  tff(c_682, plain, (![B_133]: (r2_hidden('#skF_1'('#skF_2', B_133, '#skF_3'), B_133) | ~m1_orders_2('#skF_3', '#skF_2', B_133) | k1_xboole_0=B_133 | ~m1_subset_1(B_133, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_347])).
% 3.52/1.66  tff(c_686, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_682])).
% 3.52/1.66  tff(c_692, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_686])).
% 3.52/1.66  tff(c_697, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_692])).
% 3.52/1.66  tff(c_45, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_43])).
% 3.52/1.66  tff(c_50, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_45])).
% 3.52/1.66  tff(c_51, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_50])).
% 3.52/1.66  tff(c_350, plain, (k1_xboole_0='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_315, c_51])).
% 3.52/1.66  tff(c_351, plain, (~m1_orders_2('#skF_4', '#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_350])).
% 3.52/1.66  tff(c_700, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_697, c_351])).
% 3.52/1.66  tff(c_710, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_680, c_700])).
% 3.52/1.66  tff(c_712, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_692])).
% 3.52/1.66  tff(c_741, plain, (![B_147]: (k3_orders_2('#skF_2', B_147, '#skF_1'('#skF_2', B_147, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_147) | k1_xboole_0=B_147 | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_735])).
% 3.52/1.66  tff(c_752, plain, (![B_147]: (k3_orders_2('#skF_2', B_147, '#skF_1'('#skF_2', B_147, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_147) | k1_xboole_0=B_147 | ~m1_subset_1(B_147, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_741])).
% 3.52/1.66  tff(c_842, plain, (![B_155]: (k3_orders_2('#skF_2', B_155, '#skF_1'('#skF_2', B_155, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_155) | k1_xboole_0=B_155 | ~m1_subset_1(B_155, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_40, c_752])).
% 3.52/1.66  tff(c_846, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_28, c_842])).
% 3.52/1.66  tff(c_852, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_846])).
% 3.52/1.66  tff(c_853, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_712, c_852])).
% 3.52/1.66  tff(c_875, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_853, c_18])).
% 3.52/1.66  tff(c_882, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_875])).
% 3.52/1.66  tff(c_883, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_882])).
% 3.52/1.66  tff(c_885, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_883])).
% 3.52/1.66  tff(c_888, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_12, c_885])).
% 3.52/1.66  tff(c_891, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_28, c_30, c_24, c_888])).
% 3.52/1.66  tff(c_893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_712, c_891])).
% 3.52/1.66  tff(c_918, plain, (![B_160]: (r2_hidden(B_160, '#skF_4') | ~r2_hidden(B_160, '#skF_3') | ~m1_subset_1(B_160, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_883])).
% 3.52/1.66  tff(c_924, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_808, c_918])).
% 3.52/1.66  tff(c_934, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_924])).
% 3.52/1.66  tff(c_772, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_769, c_20])).
% 3.52/1.66  tff(c_778, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_34, c_32, c_30, c_772])).
% 3.52/1.66  tff(c_779, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_40, c_778])).
% 3.52/1.66  tff(c_992, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_779])).
% 3.52/1.66  tff(c_993, plain, (![B_167]: (r2_orders_2('#skF_2', B_167, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_167, '#skF_4') | ~m1_subset_1(B_167, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_808, c_779])).
% 3.52/1.66  tff(c_995, plain, (![B_167]: (~r2_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_4'), B_167) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~r2_hidden(B_167, '#skF_4') | ~m1_subset_1(B_167, u1_struct_0('#skF_2')))), inference(resolution, [status(thm)], [c_993, c_14])).
% 3.52/1.66  tff(c_999, plain, (![B_168]: (~r2_orders_2('#skF_2', '#skF_1'('#skF_2', '#skF_3', '#skF_4'), B_168) | ~r2_hidden(B_168, '#skF_4') | ~m1_subset_1(B_168, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_808, c_995])).
% 3.52/1.66  tff(c_1003, plain, (~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_992, c_999])).
% 3.52/1.66  tff(c_1007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_808, c_934, c_1003])).
% 3.52/1.66  tff(c_1008, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_350])).
% 3.52/1.66  tff(c_314, plain, (~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_55])).
% 3.52/1.66  tff(c_1013, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_314])).
% 3.52/1.66  tff(c_1020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_1013])).
% 3.52/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.52/1.66  
% 3.52/1.66  Inference rules
% 3.52/1.66  ----------------------
% 3.52/1.66  #Ref     : 0
% 3.52/1.66  #Sup     : 156
% 3.52/1.66  #Fact    : 0
% 3.52/1.66  #Define  : 0
% 3.52/1.66  #Split   : 21
% 3.52/1.66  #Chain   : 0
% 3.52/1.66  #Close   : 0
% 3.52/1.66  
% 3.52/1.66  Ordering : KBO
% 3.52/1.66  
% 3.52/1.66  Simplification rules
% 3.52/1.66  ----------------------
% 3.52/1.66  #Subsume      : 24
% 3.52/1.66  #Demod        : 493
% 3.52/1.66  #Tautology    : 49
% 3.52/1.66  #SimpNegUnit  : 100
% 3.52/1.66  #BackRed      : 34
% 3.52/1.66  
% 3.52/1.66  #Partial instantiations: 0
% 3.52/1.66  #Strategies tried      : 1
% 3.52/1.66  
% 3.52/1.66  Timing (in seconds)
% 3.52/1.66  ----------------------
% 3.52/1.67  Preprocessing        : 0.35
% 3.52/1.67  Parsing              : 0.18
% 3.52/1.67  CNF conversion       : 0.03
% 3.52/1.67  Main loop            : 0.42
% 3.52/1.67  Inferencing          : 0.14
% 3.52/1.67  Reduction            : 0.15
% 3.52/1.67  Demodulation         : 0.10
% 3.52/1.67  BG Simplification    : 0.02
% 3.52/1.67  Subsumption          : 0.08
% 3.52/1.67  Abstraction          : 0.02
% 3.52/1.67  MUC search           : 0.00
% 3.52/1.67  Cooper               : 0.00
% 3.52/1.67  Total                : 0.84
% 3.52/1.67  Index Insertion      : 0.00
% 3.52/1.67  Index Deletion       : 0.00
% 3.52/1.67  Index Matching       : 0.00
% 3.52/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
