%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:19:49 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  151 (1025 expanded)
%              Number of leaves         :   25 ( 407 expanded)
%              Depth                    :   15
%              Number of atoms          :  542 (5760 expanded)
%              Number of equality atoms :   93 ( 746 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_orders_2 > r1_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

tff(f_75,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

tff(f_40,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( r2_orders_2(A,B,C)
              <=> ( r1_orders_2(A,B,C)
                  & B != C ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_orders_2)).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_42,plain,(
    v3_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_40,plain,(
    v4_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_38,plain,(
    v5_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_36,plain,(
    l1_orders_2('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    m1_orders_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_18,plain,(
    ! [A_8,B_20,C_26] :
      ( m1_subset_1('#skF_1'(A_8,B_20,C_26),u1_struct_0(A_8))
      | ~ m1_orders_2(C_26,A_8,B_20)
      | k1_xboole_0 = B_20
      | ~ m1_subset_1(C_26,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ m1_subset_1(B_20,k1_zfmisc_1(u1_struct_0(A_8)))
      | ~ l1_orders_2(A_8)
      | ~ v5_orders_2(A_8)
      | ~ v4_orders_2(A_8)
      | ~ v3_orders_2(A_8)
      | v2_struct_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_439,plain,(
    ! [A_108,B_109,C_110] :
      ( k3_orders_2(A_108,B_109,'#skF_1'(A_108,B_109,C_110)) = C_110
      | ~ m1_orders_2(C_110,A_108,B_109)
      | k1_xboole_0 = B_109
      | ~ m1_subset_1(C_110,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0(A_108)))
      | ~ l1_orders_2(A_108)
      | ~ v5_orders_2(A_108)
      | ~ v4_orders_2(A_108)
      | ~ v3_orders_2(A_108)
      | v2_struct_0(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_445,plain,(
    ! [B_109] :
      ( k3_orders_2('#skF_2',B_109,'#skF_1'('#skF_2',B_109,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_109)
      | k1_xboole_0 = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_439])).

tff(c_456,plain,(
    ! [B_109] :
      ( k3_orders_2('#skF_2',B_109,'#skF_1'('#skF_2',B_109,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_109)
      | k1_xboole_0 = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_445])).

tff(c_472,plain,(
    ! [B_112] :
      ( k3_orders_2('#skF_2',B_112,'#skF_1'('#skF_2',B_112,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_112)
      | k1_xboole_0 = B_112
      | ~ m1_subset_1(B_112,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_456])).

tff(c_476,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_472])).

tff(c_482,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_476])).

tff(c_483,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_482])).

tff(c_22,plain,(
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

tff(c_504,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_483,c_22])).

tff(c_511,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_504])).

tff(c_512,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_511])).

tff(c_563,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_512])).

tff(c_566,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_563])).

tff(c_569,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_26,c_566])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_30,c_569])).

tff(c_573,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_512])).

tff(c_346,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden('#skF_1'(A_95,B_96,C_97),B_96)
      | ~ m1_orders_2(C_97,A_95,B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(C_97,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0(A_95)))
      | ~ l1_orders_2(A_95)
      | ~ v5_orders_2(A_95)
      | ~ v4_orders_2(A_95)
      | ~ v3_orders_2(A_95)
      | v2_struct_0(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_352,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_2',B_96,'#skF_4'),B_96)
      | ~ m1_orders_2('#skF_4','#skF_2',B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_346])).

tff(c_363,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_2',B_96,'#skF_4'),B_96)
      | ~ m1_orders_2('#skF_4','#skF_2',B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_352])).

tff(c_403,plain,(
    ! [B_102] :
      ( r2_hidden('#skF_1'('#skF_2',B_102,'#skF_4'),B_102)
      | ~ m1_orders_2('#skF_4','#skF_2',B_102)
      | k1_xboole_0 = B_102
      | ~ m1_subset_1(B_102,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_363])).

tff(c_407,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_403])).

tff(c_413,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_407])).

tff(c_414,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_413])).

tff(c_28,plain,(
    m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_350,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_2',B_96,'#skF_3'),B_96)
      | ~ m1_orders_2('#skF_3','#skF_2',B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_346])).

tff(c_359,plain,(
    ! [B_96] :
      ( r2_hidden('#skF_1'('#skF_2',B_96,'#skF_3'),B_96)
      | ~ m1_orders_2('#skF_3','#skF_2',B_96)
      | k1_xboole_0 = B_96
      | ~ m1_subset_1(B_96,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_350])).

tff(c_368,plain,(
    ! [B_98] :
      ( r2_hidden('#skF_1'('#skF_2',B_98,'#skF_3'),B_98)
      | ~ m1_orders_2('#skF_3','#skF_2',B_98)
      | k1_xboole_0 = B_98
      | ~ m1_subset_1(B_98,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_359])).

tff(c_374,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_368])).

tff(c_381,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_374])).

tff(c_382,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_119,plain,(
    ! [A_76,B_77,C_78] :
      ( k3_orders_2(A_76,B_77,'#skF_1'(A_76,B_77,C_78)) = C_78
      | ~ m1_orders_2(C_78,A_76,B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(C_78,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0(A_76)))
      | ~ l1_orders_2(A_76)
      | ~ v5_orders_2(A_76)
      | ~ v4_orders_2(A_76)
      | ~ v3_orders_2(A_76)
      | v2_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_123,plain,(
    ! [B_77] :
      ( k3_orders_2('#skF_2',B_77,'#skF_1'('#skF_2',B_77,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_119])).

tff(c_130,plain,(
    ! [B_77] :
      ( k3_orders_2('#skF_2',B_77,'#skF_1'('#skF_2',B_77,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_123])).

tff(c_181,plain,(
    ! [B_84] :
      ( k3_orders_2('#skF_2',B_84,'#skF_1'('#skF_2',B_84,'#skF_4')) = '#skF_4'
      | ~ m1_orders_2('#skF_4','#skF_2',B_84)
      | k1_xboole_0 = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_130])).

tff(c_183,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_181])).

tff(c_188,plain,
    ( k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_183])).

tff(c_189,plain,(
    k3_orders_2('#skF_2','#skF_3','#skF_1'('#skF_2','#skF_3','#skF_4')) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_188])).

tff(c_201,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_189,c_22])).

tff(c_208,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_201])).

tff(c_209,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_3')
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_208])).

tff(c_225,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_228,plain,
    ( ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_225])).

tff(c_231,plain,
    ( k1_xboole_0 = '#skF_3'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_32,c_26,c_228])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_30,c_231])).

tff(c_235,plain,(
    m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_64,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden('#skF_1'(A_64,B_65,C_66),B_65)
      | ~ m1_orders_2(C_66,A_64,B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(C_66,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_orders_2(A_64)
      | ~ v5_orders_2(A_64)
      | ~ v4_orders_2(A_64)
      | ~ v3_orders_2(A_64)
      | v2_struct_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_68,plain,(
    ! [B_65] :
      ( r2_hidden('#skF_1'('#skF_2',B_65,'#skF_4'),B_65)
      | ~ m1_orders_2('#skF_4','#skF_2',B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_64])).

tff(c_75,plain,(
    ! [B_65] :
      ( r2_hidden('#skF_1'('#skF_2',B_65,'#skF_4'),B_65)
      | ~ m1_orders_2('#skF_4','#skF_2',B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_68])).

tff(c_105,plain,(
    ! [B_71] :
      ( r2_hidden('#skF_1'('#skF_2',B_71,'#skF_4'),B_71)
      | ~ m1_orders_2('#skF_4','#skF_2',B_71)
      | k1_xboole_0 = B_71
      | ~ m1_subset_1(B_71,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_75])).

tff(c_107,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | ~ m1_orders_2('#skF_4','#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_105])).

tff(c_112,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_107])).

tff(c_113,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_112])).

tff(c_66,plain,(
    ! [B_65] :
      ( r2_hidden('#skF_1'('#skF_2',B_65,'#skF_3'),B_65)
      | ~ m1_orders_2('#skF_3','#skF_2',B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_64])).

tff(c_71,plain,(
    ! [B_65] :
      ( r2_hidden('#skF_1'('#skF_2',B_65,'#skF_3'),B_65)
      | ~ m1_orders_2('#skF_3','#skF_2',B_65)
      | k1_xboole_0 = B_65
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_66])).

tff(c_77,plain,(
    ! [B_67] :
      ( r2_hidden('#skF_1'('#skF_2',B_67,'#skF_3'),B_67)
      | ~ m1_orders_2('#skF_3','#skF_2',B_67)
      | k1_xboole_0 = B_67
      | ~ m1_subset_1(B_67,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_71])).

tff(c_81,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_77])).

tff(c_87,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_4','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_81])).

tff(c_88,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_49,plain,(
    ! [C_58,A_59] :
      ( k1_xboole_0 = C_58
      | ~ m1_orders_2(C_58,A_59,k1_xboole_0)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(A_59)))
      | ~ l1_orders_2(A_59)
      | ~ v5_orders_2(A_59)
      | ~ v4_orders_2(A_59)
      | ~ v3_orders_2(A_59)
      | v2_struct_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_49])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2')))
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_51])).

tff(c_57,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_30,c_56])).

tff(c_63,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_57])).

tff(c_91,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_63])).

tff(c_97,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_91])).

tff(c_99,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_121,plain,(
    ! [B_77] :
      ( k3_orders_2('#skF_2',B_77,'#skF_1'('#skF_2',B_77,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_119])).

tff(c_126,plain,(
    ! [B_77] :
      ( k3_orders_2('#skF_2',B_77,'#skF_1'('#skF_2',B_77,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_77)
      | k1_xboole_0 = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_121])).

tff(c_132,plain,(
    ! [B_79] :
      ( k3_orders_2('#skF_2',B_79,'#skF_1'('#skF_2',B_79,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_79)
      | k1_xboole_0 = B_79
      | ~ m1_subset_1(B_79,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_126])).

tff(c_136,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_141,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_136])).

tff(c_142,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_141])).

tff(c_160,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_142,c_22])).

tff(c_167,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_160])).

tff(c_168,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_167])).

tff(c_170,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_173,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_170])).

tff(c_176,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_34,c_28,c_173])).

tff(c_178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_99,c_176])).

tff(c_179,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_249,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_179])).

tff(c_254,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_249])).

tff(c_24,plain,(
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

tff(c_199,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_189,c_24])).

tff(c_205,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_199])).

tff(c_206,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_205])).

tff(c_317,plain,(
    ! [B_94] :
      ( r2_orders_2('#skF_2',B_94,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_94,'#skF_4')
      | ~ m1_subset_1(B_94,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_206])).

tff(c_4,plain,(
    ! [A_1,C_7] :
      ( ~ r2_orders_2(A_1,C_7,C_7)
      | ~ m1_subset_1(C_7,u1_struct_0(A_1))
      | ~ l1_orders_2(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_322,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_317,c_4])).

tff(c_329,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_254,c_36,c_322])).

tff(c_330,plain,(
    ~ m1_orders_2('#skF_3','#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_57])).

tff(c_388,plain,(
    ~ m1_orders_2('#skF_3','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_330])).

tff(c_395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_388])).

tff(c_397,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_443,plain,(
    ! [B_109] :
      ( k3_orders_2('#skF_2',B_109,'#skF_1'('#skF_2',B_109,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_109)
      | k1_xboole_0 = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_orders_2('#skF_2')
      | ~ v5_orders_2('#skF_2')
      | ~ v4_orders_2('#skF_2')
      | ~ v3_orders_2('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_34,c_439])).

tff(c_452,plain,(
    ! [B_109] :
      ( k3_orders_2('#skF_2',B_109,'#skF_1'('#skF_2',B_109,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_109)
      | k1_xboole_0 = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(u1_struct_0('#skF_2')))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_443])).

tff(c_458,plain,(
    ! [B_111] :
      ( k3_orders_2('#skF_2',B_111,'#skF_1'('#skF_2',B_111,'#skF_3')) = '#skF_3'
      | ~ m1_orders_2('#skF_3','#skF_2',B_111)
      | k1_xboole_0 = B_111
      | ~ m1_subset_1(B_111,k1_zfmisc_1(u1_struct_0('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_452])).

tff(c_464,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_458])).

tff(c_470,plain,
    ( k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_464])).

tff(c_471,plain,(
    k3_orders_2('#skF_2','#skF_4','#skF_1'('#skF_2','#skF_4','#skF_3')) = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_470])).

tff(c_490,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_471,c_22])).

tff(c_497,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_490])).

tff(c_498,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_497])).

tff(c_514,plain,(
    ~ m1_subset_1('#skF_1'('#skF_2','#skF_4','#skF_3'),u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_498])).

tff(c_517,plain,
    ( ~ m1_orders_2('#skF_3','#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_2')))
    | ~ l1_orders_2('#skF_2')
    | ~ v5_orders_2('#skF_2')
    | ~ v4_orders_2('#skF_2')
    | ~ v3_orders_2('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_514])).

tff(c_520,plain,
    ( k1_xboole_0 = '#skF_4'
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_32,c_34,c_28,c_517])).

tff(c_522,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_397,c_520])).

tff(c_523,plain,(
    ! [B_38] :
      ( r2_hidden(B_38,'#skF_4')
      | ~ r2_hidden(B_38,'#skF_3')
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(splitRight,[status(thm)],[c_498])).

tff(c_591,plain,
    ( r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_573,c_523])).

tff(c_596,plain,(
    r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_414,c_591])).

tff(c_502,plain,(
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
    inference(superposition,[status(thm),theory(equality)],[c_483,c_24])).

tff(c_508,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2'))
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_38,c_36,c_34,c_502])).

tff(c_509,plain,(
    ! [B_38] :
      ( r2_orders_2('#skF_2',B_38,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_38,'#skF_4')
      | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2'))
      | ~ m1_subset_1(B_38,u1_struct_0('#skF_2')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_508])).

tff(c_683,plain,(
    ! [B_129] :
      ( r2_orders_2('#skF_2',B_129,'#skF_1'('#skF_2','#skF_3','#skF_4'))
      | ~ r2_hidden(B_129,'#skF_4')
      | ~ m1_subset_1(B_129,u1_struct_0('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_509])).

tff(c_688,plain,
    ( ~ l1_orders_2('#skF_2')
    | ~ r2_hidden('#skF_1'('#skF_2','#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_1'('#skF_2','#skF_3','#skF_4'),u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_683,c_4])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_573,c_596,c_36,c_688])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:59 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.08/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  
% 3.08/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.47  %$ r2_orders_2 > r1_orders_2 > m1_orders_2 > r2_hidden > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > l1_orders_2 > k3_orders_2 > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.08/1.47  
% 3.08/1.47  %Foreground sorts:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Background operators:
% 3.08/1.47  
% 3.08/1.47  
% 3.08/1.47  %Foreground operators:
% 3.08/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.08/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.08/1.47  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.08/1.47  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.08/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.47  tff(k3_orders_2, type, k3_orders_2: ($i * $i * $i) > $i).
% 3.08/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.47  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.08/1.47  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.08/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.47  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.47  tff(m1_orders_2, type, m1_orders_2: ($i * $i * $i) > $o).
% 3.08/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.47  tff(r2_orders_2, type, r2_orders_2: ($i * $i * $i) > $o).
% 3.08/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.08/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.47  
% 3.21/1.50  tff(f_127, negated_conjecture, ~(![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~((~(B = k1_xboole_0) & m1_orders_2(B, A, C)) & m1_orders_2(C, A, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_orders_2)).
% 3.21/1.50  tff(f_75, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((~(B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (?[D]: ((m1_subset_1(D, u1_struct_0(A)) & r2_hidden(D, B)) & (C = k3_orders_2(A, B, D)))))) & ((B = k1_xboole_0) => (m1_orders_2(C, A, B) <=> (C = k1_xboole_0)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d15_orders_2)).
% 3.21/1.50  tff(f_101, axiom, (![A]: (((((~v2_struct_0(A) & v3_orders_2(A)) & v4_orders_2(A)) & v5_orders_2(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(B, k3_orders_2(A, D, C)) <=> (r2_orders_2(A, B, C) & r2_hidden(B, D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_orders_2)).
% 3.21/1.50  tff(f_40, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_orders_2(A, B, C) <=> (r1_orders_2(A, B, C) & ~(B = C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_orders_2)).
% 3.21/1.50  tff(c_44, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_30, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_42, plain, (v3_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_40, plain, (v4_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_38, plain, (v5_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_36, plain, (l1_orders_2('#skF_2')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_26, plain, (m1_orders_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_18, plain, (![A_8, B_20, C_26]: (m1_subset_1('#skF_1'(A_8, B_20, C_26), u1_struct_0(A_8)) | ~m1_orders_2(C_26, A_8, B_20) | k1_xboole_0=B_20 | ~m1_subset_1(C_26, k1_zfmisc_1(u1_struct_0(A_8))) | ~m1_subset_1(B_20, k1_zfmisc_1(u1_struct_0(A_8))) | ~l1_orders_2(A_8) | ~v5_orders_2(A_8) | ~v4_orders_2(A_8) | ~v3_orders_2(A_8) | v2_struct_0(A_8))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.50  tff(c_439, plain, (![A_108, B_109, C_110]: (k3_orders_2(A_108, B_109, '#skF_1'(A_108, B_109, C_110))=C_110 | ~m1_orders_2(C_110, A_108, B_109) | k1_xboole_0=B_109 | ~m1_subset_1(C_110, k1_zfmisc_1(u1_struct_0(A_108))) | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0(A_108))) | ~l1_orders_2(A_108) | ~v5_orders_2(A_108) | ~v4_orders_2(A_108) | ~v3_orders_2(A_108) | v2_struct_0(A_108))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.50  tff(c_445, plain, (![B_109]: (k3_orders_2('#skF_2', B_109, '#skF_1'('#skF_2', B_109, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_109) | k1_xboole_0=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_439])).
% 3.21/1.50  tff(c_456, plain, (![B_109]: (k3_orders_2('#skF_2', B_109, '#skF_1'('#skF_2', B_109, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_109) | k1_xboole_0=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_445])).
% 3.21/1.50  tff(c_472, plain, (![B_112]: (k3_orders_2('#skF_2', B_112, '#skF_1'('#skF_2', B_112, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_112) | k1_xboole_0=B_112 | ~m1_subset_1(B_112, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_456])).
% 3.21/1.50  tff(c_476, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_472])).
% 3.21/1.50  tff(c_482, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_476])).
% 3.21/1.50  tff(c_483, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_30, c_482])).
% 3.21/1.50  tff(c_22, plain, (![B_38, D_44, A_30, C_42]: (r2_hidden(B_38, D_44) | ~r2_hidden(B_38, k3_orders_2(A_30, D_44, C_42)) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.21/1.50  tff(c_504, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_22])).
% 3.21/1.50  tff(c_511, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_504])).
% 3.21/1.50  tff(c_512, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_511])).
% 3.21/1.50  tff(c_563, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_512])).
% 3.21/1.50  tff(c_566, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_563])).
% 3.21/1.50  tff(c_569, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_26, c_566])).
% 3.21/1.50  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_30, c_569])).
% 3.21/1.50  tff(c_573, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_512])).
% 3.21/1.50  tff(c_346, plain, (![A_95, B_96, C_97]: (r2_hidden('#skF_1'(A_95, B_96, C_97), B_96) | ~m1_orders_2(C_97, A_95, B_96) | k1_xboole_0=B_96 | ~m1_subset_1(C_97, k1_zfmisc_1(u1_struct_0(A_95))) | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0(A_95))) | ~l1_orders_2(A_95) | ~v5_orders_2(A_95) | ~v4_orders_2(A_95) | ~v3_orders_2(A_95) | v2_struct_0(A_95))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.50  tff(c_352, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_2', B_96, '#skF_4'), B_96) | ~m1_orders_2('#skF_4', '#skF_2', B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_346])).
% 3.21/1.50  tff(c_363, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_2', B_96, '#skF_4'), B_96) | ~m1_orders_2('#skF_4', '#skF_2', B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_352])).
% 3.21/1.50  tff(c_403, plain, (![B_102]: (r2_hidden('#skF_1'('#skF_2', B_102, '#skF_4'), B_102) | ~m1_orders_2('#skF_4', '#skF_2', B_102) | k1_xboole_0=B_102 | ~m1_subset_1(B_102, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_363])).
% 3.21/1.50  tff(c_407, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_403])).
% 3.21/1.50  tff(c_413, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_407])).
% 3.21/1.50  tff(c_414, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_413])).
% 3.21/1.50  tff(c_28, plain, (m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.21/1.50  tff(c_350, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_2', B_96, '#skF_3'), B_96) | ~m1_orders_2('#skF_3', '#skF_2', B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_346])).
% 3.21/1.50  tff(c_359, plain, (![B_96]: (r2_hidden('#skF_1'('#skF_2', B_96, '#skF_3'), B_96) | ~m1_orders_2('#skF_3', '#skF_2', B_96) | k1_xboole_0=B_96 | ~m1_subset_1(B_96, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_350])).
% 3.21/1.50  tff(c_368, plain, (![B_98]: (r2_hidden('#skF_1'('#skF_2', B_98, '#skF_3'), B_98) | ~m1_orders_2('#skF_3', '#skF_2', B_98) | k1_xboole_0=B_98 | ~m1_subset_1(B_98, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_359])).
% 3.21/1.50  tff(c_374, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_368])).
% 3.21/1.50  tff(c_381, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_374])).
% 3.21/1.50  tff(c_382, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_381])).
% 3.21/1.50  tff(c_119, plain, (![A_76, B_77, C_78]: (k3_orders_2(A_76, B_77, '#skF_1'(A_76, B_77, C_78))=C_78 | ~m1_orders_2(C_78, A_76, B_77) | k1_xboole_0=B_77 | ~m1_subset_1(C_78, k1_zfmisc_1(u1_struct_0(A_76))) | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0(A_76))) | ~l1_orders_2(A_76) | ~v5_orders_2(A_76) | ~v4_orders_2(A_76) | ~v3_orders_2(A_76) | v2_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.50  tff(c_123, plain, (![B_77]: (k3_orders_2('#skF_2', B_77, '#skF_1'('#skF_2', B_77, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_77) | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_119])).
% 3.21/1.50  tff(c_130, plain, (![B_77]: (k3_orders_2('#skF_2', B_77, '#skF_1'('#skF_2', B_77, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_77) | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_123])).
% 3.21/1.50  tff(c_181, plain, (![B_84]: (k3_orders_2('#skF_2', B_84, '#skF_1'('#skF_2', B_84, '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', B_84) | k1_xboole_0=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_130])).
% 3.21/1.50  tff(c_183, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_181])).
% 3.21/1.50  tff(c_188, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_183])).
% 3.21/1.50  tff(c_189, plain, (k3_orders_2('#skF_2', '#skF_3', '#skF_1'('#skF_2', '#skF_3', '#skF_4'))='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_30, c_188])).
% 3.21/1.50  tff(c_201, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_22])).
% 3.21/1.50  tff(c_208, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_201])).
% 3.21/1.50  tff(c_209, plain, (![B_38]: (r2_hidden(B_38, '#skF_3') | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_208])).
% 3.21/1.50  tff(c_225, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_209])).
% 3.21/1.50  tff(c_228, plain, (~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_225])).
% 3.21/1.50  tff(c_231, plain, (k1_xboole_0='#skF_3' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_32, c_26, c_228])).
% 3.21/1.50  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_30, c_231])).
% 3.21/1.50  tff(c_235, plain, (m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_209])).
% 3.21/1.50  tff(c_64, plain, (![A_64, B_65, C_66]: (r2_hidden('#skF_1'(A_64, B_65, C_66), B_65) | ~m1_orders_2(C_66, A_64, B_65) | k1_xboole_0=B_65 | ~m1_subset_1(C_66, k1_zfmisc_1(u1_struct_0(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_orders_2(A_64) | ~v5_orders_2(A_64) | ~v4_orders_2(A_64) | ~v3_orders_2(A_64) | v2_struct_0(A_64))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.50  tff(c_68, plain, (![B_65]: (r2_hidden('#skF_1'('#skF_2', B_65, '#skF_4'), B_65) | ~m1_orders_2('#skF_4', '#skF_2', B_65) | k1_xboole_0=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_64])).
% 3.21/1.50  tff(c_75, plain, (![B_65]: (r2_hidden('#skF_1'('#skF_2', B_65, '#skF_4'), B_65) | ~m1_orders_2('#skF_4', '#skF_2', B_65) | k1_xboole_0=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_68])).
% 3.21/1.50  tff(c_105, plain, (![B_71]: (r2_hidden('#skF_1'('#skF_2', B_71, '#skF_4'), B_71) | ~m1_orders_2('#skF_4', '#skF_2', B_71) | k1_xboole_0=B_71 | ~m1_subset_1(B_71, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_75])).
% 3.21/1.50  tff(c_107, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | ~m1_orders_2('#skF_4', '#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_105])).
% 3.21/1.50  tff(c_112, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_107])).
% 3.21/1.50  tff(c_113, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_30, c_112])).
% 3.21/1.50  tff(c_66, plain, (![B_65]: (r2_hidden('#skF_1'('#skF_2', B_65, '#skF_3'), B_65) | ~m1_orders_2('#skF_3', '#skF_2', B_65) | k1_xboole_0=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_64])).
% 3.21/1.50  tff(c_71, plain, (![B_65]: (r2_hidden('#skF_1'('#skF_2', B_65, '#skF_3'), B_65) | ~m1_orders_2('#skF_3', '#skF_2', B_65) | k1_xboole_0=B_65 | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_66])).
% 3.21/1.50  tff(c_77, plain, (![B_67]: (r2_hidden('#skF_1'('#skF_2', B_67, '#skF_3'), B_67) | ~m1_orders_2('#skF_3', '#skF_2', B_67) | k1_xboole_0=B_67 | ~m1_subset_1(B_67, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_71])).
% 3.21/1.50  tff(c_81, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_77])).
% 3.21/1.50  tff(c_87, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_4', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_81])).
% 3.21/1.50  tff(c_88, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_87])).
% 3.21/1.50  tff(c_49, plain, (![C_58, A_59]: (k1_xboole_0=C_58 | ~m1_orders_2(C_58, A_59, k1_xboole_0) | ~m1_subset_1(C_58, k1_zfmisc_1(u1_struct_0(A_59))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0(A_59))) | ~l1_orders_2(A_59) | ~v5_orders_2(A_59) | ~v4_orders_2(A_59) | ~v3_orders_2(A_59) | v2_struct_0(A_59))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.21/1.50  tff(c_51, plain, (k1_xboole_0='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_34, c_49])).
% 3.21/1.50  tff(c_56, plain, (k1_xboole_0='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_51])).
% 3.21/1.50  tff(c_57, plain, (~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_30, c_56])).
% 3.21/1.50  tff(c_63, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(splitLeft, [status(thm)], [c_57])).
% 3.21/1.50  tff(c_91, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_63])).
% 3.21/1.50  tff(c_97, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_91])).
% 3.21/1.50  tff(c_99, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_87])).
% 3.21/1.50  tff(c_121, plain, (![B_77]: (k3_orders_2('#skF_2', B_77, '#skF_1'('#skF_2', B_77, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_77) | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_119])).
% 3.21/1.50  tff(c_126, plain, (![B_77]: (k3_orders_2('#skF_2', B_77, '#skF_1'('#skF_2', B_77, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_77) | k1_xboole_0=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_121])).
% 3.21/1.50  tff(c_132, plain, (![B_79]: (k3_orders_2('#skF_2', B_79, '#skF_1'('#skF_2', B_79, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_79) | k1_xboole_0=B_79 | ~m1_subset_1(B_79, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_126])).
% 3.21/1.50  tff(c_136, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_132])).
% 3.21/1.50  tff(c_141, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_136])).
% 3.21/1.50  tff(c_142, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_99, c_141])).
% 3.21/1.50  tff(c_160, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_142, c_22])).
% 3.21/1.50  tff(c_167, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_160])).
% 3.21/1.50  tff(c_168, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_167])).
% 3.21/1.50  tff(c_170, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_168])).
% 3.21/1.50  tff(c_173, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_170])).
% 3.21/1.50  tff(c_176, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_34, c_28, c_173])).
% 3.21/1.50  tff(c_178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_99, c_176])).
% 3.21/1.50  tff(c_179, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_168])).
% 3.21/1.50  tff(c_249, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_235, c_179])).
% 3.21/1.50  tff(c_254, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_249])).
% 3.21/1.50  tff(c_24, plain, (![A_30, B_38, C_42, D_44]: (r2_orders_2(A_30, B_38, C_42) | ~r2_hidden(B_38, k3_orders_2(A_30, D_44, C_42)) | ~m1_subset_1(D_44, k1_zfmisc_1(u1_struct_0(A_30))) | ~m1_subset_1(C_42, u1_struct_0(A_30)) | ~m1_subset_1(B_38, u1_struct_0(A_30)) | ~l1_orders_2(A_30) | ~v5_orders_2(A_30) | ~v4_orders_2(A_30) | ~v3_orders_2(A_30) | v2_struct_0(A_30))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.21/1.50  tff(c_199, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_24])).
% 3.21/1.50  tff(c_205, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_199])).
% 3.21/1.50  tff(c_206, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_205])).
% 3.21/1.50  tff(c_317, plain, (![B_94]: (r2_orders_2('#skF_2', B_94, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_94, '#skF_4') | ~m1_subset_1(B_94, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_235, c_206])).
% 3.21/1.50  tff(c_4, plain, (![A_1, C_7]: (~r2_orders_2(A_1, C_7, C_7) | ~m1_subset_1(C_7, u1_struct_0(A_1)) | ~l1_orders_2(A_1))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.21/1.50  tff(c_322, plain, (~l1_orders_2('#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_317, c_4])).
% 3.21/1.50  tff(c_329, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_235, c_254, c_36, c_322])).
% 3.21/1.50  tff(c_330, plain, (~m1_orders_2('#skF_3', '#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_57])).
% 3.21/1.50  tff(c_388, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_382, c_330])).
% 3.21/1.50  tff(c_395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_388])).
% 3.21/1.50  tff(c_397, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_381])).
% 3.21/1.50  tff(c_443, plain, (![B_109]: (k3_orders_2('#skF_2', B_109, '#skF_1'('#skF_2', B_109, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_109) | k1_xboole_0=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_34, c_439])).
% 3.21/1.50  tff(c_452, plain, (![B_109]: (k3_orders_2('#skF_2', B_109, '#skF_1'('#skF_2', B_109, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_109) | k1_xboole_0=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(u1_struct_0('#skF_2'))) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_443])).
% 3.21/1.50  tff(c_458, plain, (![B_111]: (k3_orders_2('#skF_2', B_111, '#skF_1'('#skF_2', B_111, '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', B_111) | k1_xboole_0=B_111 | ~m1_subset_1(B_111, k1_zfmisc_1(u1_struct_0('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_44, c_452])).
% 3.21/1.50  tff(c_464, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | ~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_32, c_458])).
% 3.21/1.50  tff(c_470, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_464])).
% 3.21/1.50  tff(c_471, plain, (k3_orders_2('#skF_2', '#skF_4', '#skF_1'('#skF_2', '#skF_4', '#skF_3'))='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_397, c_470])).
% 3.21/1.50  tff(c_490, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_471, c_22])).
% 3.21/1.50  tff(c_497, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_490])).
% 3.21/1.50  tff(c_498, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_497])).
% 3.21/1.50  tff(c_514, plain, (~m1_subset_1('#skF_1'('#skF_2', '#skF_4', '#skF_3'), u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_498])).
% 3.21/1.50  tff(c_517, plain, (~m1_orders_2('#skF_3', '#skF_2', '#skF_4') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_18, c_514])).
% 3.21/1.50  tff(c_520, plain, (k1_xboole_0='#skF_4' | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_32, c_34, c_28, c_517])).
% 3.21/1.50  tff(c_522, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_397, c_520])).
% 3.21/1.50  tff(c_523, plain, (![B_38]: (r2_hidden(B_38, '#skF_4') | ~r2_hidden(B_38, '#skF_3') | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(splitRight, [status(thm)], [c_498])).
% 3.21/1.50  tff(c_591, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_573, c_523])).
% 3.21/1.50  tff(c_596, plain, (r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_414, c_591])).
% 3.21/1.50  tff(c_502, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | ~l1_orders_2('#skF_2') | ~v5_orders_2('#skF_2') | ~v4_orders_2('#skF_2') | ~v3_orders_2('#skF_2') | v2_struct_0('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_24])).
% 3.21/1.50  tff(c_508, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_38, c_36, c_34, c_502])).
% 3.21/1.50  tff(c_509, plain, (![B_38]: (r2_orders_2('#skF_2', B_38, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_38, '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2')) | ~m1_subset_1(B_38, u1_struct_0('#skF_2')))), inference(negUnitSimplification, [status(thm)], [c_44, c_508])).
% 3.21/1.50  tff(c_683, plain, (![B_129]: (r2_orders_2('#skF_2', B_129, '#skF_1'('#skF_2', '#skF_3', '#skF_4')) | ~r2_hidden(B_129, '#skF_4') | ~m1_subset_1(B_129, u1_struct_0('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_573, c_509])).
% 3.21/1.50  tff(c_688, plain, (~l1_orders_2('#skF_2') | ~r2_hidden('#skF_1'('#skF_2', '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_1'('#skF_2', '#skF_3', '#skF_4'), u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_683, c_4])).
% 3.21/1.50  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_573, c_596, c_36, c_688])).
% 3.21/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.50  
% 3.21/1.50  Inference rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Ref     : 0
% 3.21/1.50  #Sup     : 105
% 3.21/1.50  #Fact    : 0
% 3.21/1.50  #Define  : 0
% 3.21/1.50  #Split   : 14
% 3.21/1.50  #Chain   : 0
% 3.21/1.50  #Close   : 0
% 3.21/1.50  
% 3.21/1.50  Ordering : KBO
% 3.21/1.50  
% 3.21/1.50  Simplification rules
% 3.21/1.50  ----------------------
% 3.21/1.50  #Subsume      : 15
% 3.21/1.50  #Demod        : 318
% 3.21/1.50  #Tautology    : 30
% 3.21/1.50  #SimpNegUnit  : 67
% 3.21/1.50  #BackRed      : 15
% 3.21/1.50  
% 3.21/1.50  #Partial instantiations: 0
% 3.21/1.50  #Strategies tried      : 1
% 3.21/1.50  
% 3.21/1.50  Timing (in seconds)
% 3.21/1.50  ----------------------
% 3.21/1.50  Preprocessing        : 0.32
% 3.21/1.50  Parsing              : 0.16
% 3.21/1.50  CNF conversion       : 0.03
% 3.21/1.50  Main loop            : 0.35
% 3.21/1.50  Inferencing          : 0.12
% 3.21/1.50  Reduction            : 0.13
% 3.21/1.50  Demodulation         : 0.09
% 3.21/1.50  BG Simplification    : 0.02
% 3.21/1.50  Subsumption          : 0.07
% 3.21/1.50  Abstraction          : 0.02
% 3.21/1.50  MUC search           : 0.00
% 3.21/1.50  Cooper               : 0.00
% 3.21/1.50  Total                : 0.73
% 3.21/1.50  Index Insertion      : 0.00
% 3.21/1.50  Index Deletion       : 0.00
% 3.21/1.50  Index Matching       : 0.00
% 3.21/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
