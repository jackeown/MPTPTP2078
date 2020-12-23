%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:24:07 EST 2020

% Result     : Theorem 4.95s
% Output     : CNFRefutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 234 expanded)
%              Number of leaves         :   29 (  94 expanded)
%              Depth                    :   12
%              Number of atoms          :  204 ( 920 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_tops_1,type,(
    k1_tops_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_175,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
               => ~ ( m1_connsp_2(C,A,B)
                    & ! [D] :
                        ( ( ~ v1_xboole_0(D)
                          & m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A))) )
                       => ~ ( m1_connsp_2(D,A,B)
                            & v3_pre_topc(D,A)
                            & r1_tarski(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

tff(f_112,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> r2_hidden(B,k1_tops_1(A,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => r1_tarski(k1_tops_1(A,B),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( l1_pre_topc(A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A))) )
     => k1_tops_1(A,k1_tops_1(A,B)) = k1_tops_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(B)))
                 => ( ( v3_pre_topc(D,B)
                     => k1_tops_1(B,D) = D )
                    & ( k1_tops_1(A,C) = C
                     => v3_pre_topc(C,A) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_48,plain,(
    m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_56,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_54,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1395,plain,(
    ! [B_203,A_204,C_205] :
      ( r2_hidden(B_203,k1_tops_1(A_204,C_205))
      | ~ m1_connsp_2(C_205,A_204,B_203)
      | ~ m1_subset_1(C_205,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ m1_subset_1(B_203,u1_struct_0(A_204))
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204)
      | v2_struct_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1403,plain,(
    ! [B_203] :
      ( r2_hidden(B_203,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_203)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_50,c_1395])).

tff(c_1408,plain,(
    ! [B_203] :
      ( r2_hidden(B_203,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_203)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1403])).

tff(c_1409,plain,(
    ! [B_203] :
      ( r2_hidden(B_203,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_203)
      | ~ m1_subset_1(B_203,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1408])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1410,plain,(
    ! [B_206] :
      ( r2_hidden(B_206,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_connsp_2('#skF_5','#skF_3',B_206)
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1408])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_131,plain,(
    ! [C_86,B_87,A_88] :
      ( ~ v1_xboole_0(C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    ! [B_12,A_88,A_11] :
      ( ~ v1_xboole_0(B_12)
      | ~ r2_hidden(A_88,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_24,c_131])).

tff(c_1424,plain,(
    ! [B_12,B_206] :
      ( ~ v1_xboole_0(B_12)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_12)
      | ~ m1_connsp_2('#skF_5','#skF_3',B_206)
      | ~ m1_subset_1(B_206,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1410,c_136])).

tff(c_1426,plain,(
    ! [B_207] :
      ( ~ m1_connsp_2('#skF_5','#skF_3',B_207)
      | ~ m1_subset_1(B_207,u1_struct_0('#skF_3')) ) ),
    inference(splitLeft,[status(thm)],[c_1424])).

tff(c_1442,plain,(
    ~ m1_connsp_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1426])).

tff(c_1450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1442])).

tff(c_1481,plain,(
    ! [B_210] :
      ( ~ v1_xboole_0(B_210)
      | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),B_210) ) ),
    inference(splitRight,[status(thm)],[c_1424])).

tff(c_1515,plain,(
    ~ v1_xboole_0(k1_tops_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_6,c_1481])).

tff(c_213,plain,(
    ! [A_113,B_114] :
      ( r1_tarski(k1_tops_1(A_113,B_114),B_114)
      | ~ m1_subset_1(B_114,k1_zfmisc_1(u1_struct_0(A_113)))
      | ~ l1_pre_topc(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_218,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_213])).

tff(c_222,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_218])).

tff(c_471,plain,(
    ! [A_144,B_145] :
      ( k1_tops_1(A_144,k1_tops_1(A_144,B_145)) = k1_tops_1(A_144,B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(u1_struct_0(A_144)))
      | ~ l1_pre_topc(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_476,plain,
    ( k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_5')) = k1_tops_1('#skF_3','#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_471])).

tff(c_480,plain,(
    k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_5')) = k1_tops_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_476])).

tff(c_81,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_89,plain,(
    r1_tarski('#skF_5',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_81])).

tff(c_101,plain,(
    ! [A_81,C_82,B_83] :
      ( r1_tarski(A_81,C_82)
      | ~ r1_tarski(B_83,C_82)
      | ~ r1_tarski(A_81,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_120,plain,(
    ! [A_85] :
      ( r1_tarski(A_85,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_89,c_101])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_129,plain,(
    ! [A_3,A_85] :
      ( r1_tarski(A_3,u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_3,A_85)
      | ~ r1_tarski(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_120,c_8])).

tff(c_226,plain,
    ( r1_tarski(k1_tops_1('#skF_3','#skF_5'),u1_struct_0('#skF_3'))
    | ~ r1_tarski('#skF_5','#skF_5') ),
    inference(resolution,[status(thm)],[c_222,c_129])).

tff(c_234,plain,(
    r1_tarski(k1_tops_1('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_226])).

tff(c_34,plain,(
    ! [C_36,A_24,D_38,B_32] :
      ( v3_pre_topc(C_36,A_24)
      | k1_tops_1(A_24,C_36) != C_36
      | ~ m1_subset_1(D_38,k1_zfmisc_1(u1_struct_0(B_32)))
      | ~ m1_subset_1(C_36,k1_zfmisc_1(u1_struct_0(A_24)))
      | ~ l1_pre_topc(B_32)
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1128,plain,(
    ! [D_191,B_192] :
      ( ~ m1_subset_1(D_191,k1_zfmisc_1(u1_struct_0(B_192)))
      | ~ l1_pre_topc(B_192) ) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_1139,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1128])).

tff(c_1145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1139])).

tff(c_1147,plain,(
    ! [C_193,A_194] :
      ( v3_pre_topc(C_193,A_194)
      | k1_tops_1(A_194,C_193) != C_193
      | ~ m1_subset_1(C_193,k1_zfmisc_1(u1_struct_0(A_194)))
      | ~ l1_pre_topc(A_194)
      | ~ v2_pre_topc(A_194) ) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_1204,plain,(
    ! [A_197,A_198] :
      ( v3_pre_topc(A_197,A_198)
      | k1_tops_1(A_198,A_197) != A_197
      | ~ l1_pre_topc(A_198)
      | ~ v2_pre_topc(A_198)
      | ~ r1_tarski(A_197,u1_struct_0(A_198)) ) ),
    inference(resolution,[status(thm)],[c_24,c_1147])).

tff(c_1249,plain,
    ( v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3')
    | k1_tops_1('#skF_3',k1_tops_1('#skF_3','#skF_5')) != k1_tops_1('#skF_3','#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_234,c_1204])).

tff(c_1286,plain,(
    v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_480,c_1249])).

tff(c_1546,plain,(
    ! [C_213,A_214,B_215] :
      ( m1_connsp_2(C_213,A_214,B_215)
      | ~ r2_hidden(B_215,k1_tops_1(A_214,C_213))
      | ~ m1_subset_1(C_213,k1_zfmisc_1(u1_struct_0(A_214)))
      | ~ m1_subset_1(B_215,u1_struct_0(A_214))
      | ~ l1_pre_topc(A_214)
      | ~ v2_pre_topc(A_214)
      | v2_struct_0(A_214) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1557,plain,(
    ! [B_215] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_215)
      | ~ r2_hidden(B_215,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_1546])).

tff(c_1573,plain,(
    ! [B_215] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_215)
      | ~ r2_hidden(B_215,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_3'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_1557])).

tff(c_1574,plain,(
    ! [B_215] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_215)
      | ~ r2_hidden(B_215,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ m1_subset_1(B_215,u1_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1573])).

tff(c_1711,plain,(
    ~ m1_subset_1(k1_tops_1('#skF_3','#skF_5'),k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1574])).

tff(c_1714,plain,(
    ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_1711])).

tff(c_1718,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_234,c_1714])).

tff(c_1840,plain,(
    ! [B_223] :
      ( m1_connsp_2(k1_tops_1('#skF_3','#skF_5'),'#skF_3',B_223)
      | ~ r2_hidden(B_223,k1_tops_1('#skF_3','#skF_5'))
      | ~ m1_subset_1(B_223,u1_struct_0('#skF_3')) ) ),
    inference(splitRight,[status(thm)],[c_1574])).

tff(c_75,plain,(
    ! [A_75,B_76] :
      ( m1_subset_1(A_75,k1_zfmisc_1(B_76))
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_46,plain,(
    ! [D_68] :
      ( ~ r1_tarski(D_68,'#skF_5')
      | ~ v3_pre_topc(D_68,'#skF_3')
      | ~ m1_connsp_2(D_68,'#skF_3','#skF_4')
      | ~ m1_subset_1(D_68,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | v1_xboole_0(D_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_80,plain,(
    ! [A_75] :
      ( ~ r1_tarski(A_75,'#skF_5')
      | ~ v3_pre_topc(A_75,'#skF_3')
      | ~ m1_connsp_2(A_75,'#skF_3','#skF_4')
      | v1_xboole_0(A_75)
      | ~ r1_tarski(A_75,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_75,c_46])).

tff(c_128,plain,(
    ! [A_85] :
      ( ~ v3_pre_topc(A_85,'#skF_3')
      | ~ m1_connsp_2(A_85,'#skF_3','#skF_4')
      | v1_xboole_0(A_85)
      | ~ r1_tarski(A_85,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_120,c_80])).

tff(c_1846,plain,
    ( ~ v3_pre_topc(k1_tops_1('#skF_3','#skF_5'),'#skF_3')
    | v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
    | ~ r1_tarski(k1_tops_1('#skF_3','#skF_5'),'#skF_5')
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5'))
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1840,c_128])).

tff(c_1853,plain,
    ( v1_xboole_0(k1_tops_1('#skF_3','#skF_5'))
    | ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_222,c_1286,c_1846])).

tff(c_1854,plain,(
    ~ r2_hidden('#skF_4',k1_tops_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_1515,c_1853])).

tff(c_1886,plain,
    ( ~ m1_connsp_2('#skF_5','#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1409,c_1854])).

tff(c_1890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1886])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.95/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.86  
% 4.95/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.87  %$ m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_pre_topc > k1_tops_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.95/1.87  
% 4.95/1.87  %Foreground sorts:
% 4.95/1.87  
% 4.95/1.87  
% 4.95/1.87  %Background operators:
% 4.95/1.87  
% 4.95/1.87  
% 4.95/1.87  %Foreground operators:
% 4.95/1.87  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.95/1.87  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.95/1.87  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.95/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.95/1.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.95/1.87  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.95/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.95/1.87  tff('#skF_5', type, '#skF_5': $i).
% 4.95/1.87  tff(k1_tops_1, type, k1_tops_1: ($i * $i) > $i).
% 4.95/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.95/1.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.95/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.95/1.87  tff('#skF_4', type, '#skF_4': $i).
% 4.95/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.95/1.87  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.95/1.87  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.95/1.87  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.95/1.87  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.95/1.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.95/1.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.95/1.87  
% 4.95/1.90  tff(f_175, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ~(m1_connsp_2(C, A, B) & (![D]: ((~v1_xboole_0(D) & m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A)))) => ~((m1_connsp_2(D, A, B) & v3_pre_topc(D, A)) & r1_tarski(D, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_connsp_2)).
% 4.95/1.90  tff(f_112, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> r2_hidden(B, k1_tops_1(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_connsp_2)).
% 4.95/1.90  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.95/1.90  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.95/1.90  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.95/1.90  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => r1_tarski(k1_tops_1(A, B), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_tops_1)).
% 4.95/1.90  tff(f_67, axiom, (![A, B]: ((l1_pre_topc(A) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) => (k1_tops_1(A, k1_tops_1(A, B)) = k1_tops_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', projectivity_k1_tops_1)).
% 4.95/1.90  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.95/1.90  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (l1_pre_topc(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(B))) => ((v3_pre_topc(D, B) => (k1_tops_1(B, D) = D)) & ((k1_tops_1(A, C) = C) => v3_pre_topc(C, A))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_tops_1)).
% 4.95/1.90  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.95/1.90  tff(c_48, plain, (m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.95/1.90  tff(c_58, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.95/1.90  tff(c_56, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.95/1.90  tff(c_54, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.95/1.90  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.95/1.90  tff(c_1395, plain, (![B_203, A_204, C_205]: (r2_hidden(B_203, k1_tops_1(A_204, C_205)) | ~m1_connsp_2(C_205, A_204, B_203) | ~m1_subset_1(C_205, k1_zfmisc_1(u1_struct_0(A_204))) | ~m1_subset_1(B_203, u1_struct_0(A_204)) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204) | v2_struct_0(A_204))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.95/1.90  tff(c_1403, plain, (![B_203]: (r2_hidden(B_203, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_203) | ~m1_subset_1(B_203, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_1395])).
% 4.95/1.90  tff(c_1408, plain, (![B_203]: (r2_hidden(B_203, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_203) | ~m1_subset_1(B_203, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1403])).
% 4.95/1.90  tff(c_1409, plain, (![B_203]: (r2_hidden(B_203, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_203) | ~m1_subset_1(B_203, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1408])).
% 4.95/1.90  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.95/1.90  tff(c_1410, plain, (![B_206]: (r2_hidden(B_206, k1_tops_1('#skF_3', '#skF_5')) | ~m1_connsp_2('#skF_5', '#skF_3', B_206) | ~m1_subset_1(B_206, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1408])).
% 4.95/1.90  tff(c_24, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.95/1.90  tff(c_131, plain, (![C_86, B_87, A_88]: (~v1_xboole_0(C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.95/1.90  tff(c_136, plain, (![B_12, A_88, A_11]: (~v1_xboole_0(B_12) | ~r2_hidden(A_88, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_24, c_131])).
% 4.95/1.90  tff(c_1424, plain, (![B_12, B_206]: (~v1_xboole_0(B_12) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_12) | ~m1_connsp_2('#skF_5', '#skF_3', B_206) | ~m1_subset_1(B_206, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1410, c_136])).
% 4.95/1.90  tff(c_1426, plain, (![B_207]: (~m1_connsp_2('#skF_5', '#skF_3', B_207) | ~m1_subset_1(B_207, u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1424])).
% 4.95/1.90  tff(c_1442, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1426])).
% 4.95/1.90  tff(c_1450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1442])).
% 4.95/1.90  tff(c_1481, plain, (![B_210]: (~v1_xboole_0(B_210) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), B_210))), inference(splitRight, [status(thm)], [c_1424])).
% 4.95/1.90  tff(c_1515, plain, (~v1_xboole_0(k1_tops_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_6, c_1481])).
% 4.95/1.90  tff(c_213, plain, (![A_113, B_114]: (r1_tarski(k1_tops_1(A_113, B_114), B_114) | ~m1_subset_1(B_114, k1_zfmisc_1(u1_struct_0(A_113))) | ~l1_pre_topc(A_113))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.95/1.90  tff(c_218, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_213])).
% 4.95/1.90  tff(c_222, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_218])).
% 4.95/1.90  tff(c_471, plain, (![A_144, B_145]: (k1_tops_1(A_144, k1_tops_1(A_144, B_145))=k1_tops_1(A_144, B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(u1_struct_0(A_144))) | ~l1_pre_topc(A_144))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.95/1.90  tff(c_476, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_5'))=k1_tops_1('#skF_3', '#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_471])).
% 4.95/1.90  tff(c_480, plain, (k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_5'))=k1_tops_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_476])).
% 4.95/1.90  tff(c_81, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(B_78)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.95/1.90  tff(c_89, plain, (r1_tarski('#skF_5', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_50, c_81])).
% 4.95/1.90  tff(c_101, plain, (![A_81, C_82, B_83]: (r1_tarski(A_81, C_82) | ~r1_tarski(B_83, C_82) | ~r1_tarski(A_81, B_83))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.95/1.90  tff(c_120, plain, (![A_85]: (r1_tarski(A_85, u1_struct_0('#skF_3')) | ~r1_tarski(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_89, c_101])).
% 4.95/1.90  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.95/1.90  tff(c_129, plain, (![A_3, A_85]: (r1_tarski(A_3, u1_struct_0('#skF_3')) | ~r1_tarski(A_3, A_85) | ~r1_tarski(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_120, c_8])).
% 4.95/1.90  tff(c_226, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), u1_struct_0('#skF_3')) | ~r1_tarski('#skF_5', '#skF_5')), inference(resolution, [status(thm)], [c_222, c_129])).
% 4.95/1.90  tff(c_234, plain, (r1_tarski(k1_tops_1('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_226])).
% 4.95/1.90  tff(c_34, plain, (![C_36, A_24, D_38, B_32]: (v3_pre_topc(C_36, A_24) | k1_tops_1(A_24, C_36)!=C_36 | ~m1_subset_1(D_38, k1_zfmisc_1(u1_struct_0(B_32))) | ~m1_subset_1(C_36, k1_zfmisc_1(u1_struct_0(A_24))) | ~l1_pre_topc(B_32) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.95/1.90  tff(c_1128, plain, (![D_191, B_192]: (~m1_subset_1(D_191, k1_zfmisc_1(u1_struct_0(B_192))) | ~l1_pre_topc(B_192))), inference(splitLeft, [status(thm)], [c_34])).
% 4.95/1.90  tff(c_1139, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1128])).
% 4.95/1.90  tff(c_1145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_1139])).
% 4.95/1.90  tff(c_1147, plain, (![C_193, A_194]: (v3_pre_topc(C_193, A_194) | k1_tops_1(A_194, C_193)!=C_193 | ~m1_subset_1(C_193, k1_zfmisc_1(u1_struct_0(A_194))) | ~l1_pre_topc(A_194) | ~v2_pre_topc(A_194))), inference(splitRight, [status(thm)], [c_34])).
% 4.95/1.90  tff(c_1204, plain, (![A_197, A_198]: (v3_pre_topc(A_197, A_198) | k1_tops_1(A_198, A_197)!=A_197 | ~l1_pre_topc(A_198) | ~v2_pre_topc(A_198) | ~r1_tarski(A_197, u1_struct_0(A_198)))), inference(resolution, [status(thm)], [c_24, c_1147])).
% 4.95/1.90  tff(c_1249, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3') | k1_tops_1('#skF_3', k1_tops_1('#skF_3', '#skF_5'))!=k1_tops_1('#skF_3', '#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_234, c_1204])).
% 4.95/1.90  tff(c_1286, plain, (v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_480, c_1249])).
% 4.95/1.90  tff(c_1546, plain, (![C_213, A_214, B_215]: (m1_connsp_2(C_213, A_214, B_215) | ~r2_hidden(B_215, k1_tops_1(A_214, C_213)) | ~m1_subset_1(C_213, k1_zfmisc_1(u1_struct_0(A_214))) | ~m1_subset_1(B_215, u1_struct_0(A_214)) | ~l1_pre_topc(A_214) | ~v2_pre_topc(A_214) | v2_struct_0(A_214))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.95/1.90  tff(c_1557, plain, (![B_215]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_215) | ~r2_hidden(B_215, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_215, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_480, c_1546])).
% 4.95/1.90  tff(c_1573, plain, (![B_215]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_215) | ~r2_hidden(B_215, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_215, u1_struct_0('#skF_3')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_1557])).
% 4.95/1.90  tff(c_1574, plain, (![B_215]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_215) | ~r2_hidden(B_215, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~m1_subset_1(B_215, u1_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1573])).
% 4.95/1.90  tff(c_1711, plain, (~m1_subset_1(k1_tops_1('#skF_3', '#skF_5'), k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_1574])).
% 4.95/1.90  tff(c_1714, plain, (~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_1711])).
% 4.95/1.90  tff(c_1718, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_234, c_1714])).
% 4.95/1.90  tff(c_1840, plain, (![B_223]: (m1_connsp_2(k1_tops_1('#skF_3', '#skF_5'), '#skF_3', B_223) | ~r2_hidden(B_223, k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1(B_223, u1_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_1574])).
% 4.95/1.90  tff(c_75, plain, (![A_75, B_76]: (m1_subset_1(A_75, k1_zfmisc_1(B_76)) | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.95/1.90  tff(c_46, plain, (![D_68]: (~r1_tarski(D_68, '#skF_5') | ~v3_pre_topc(D_68, '#skF_3') | ~m1_connsp_2(D_68, '#skF_3', '#skF_4') | ~m1_subset_1(D_68, k1_zfmisc_1(u1_struct_0('#skF_3'))) | v1_xboole_0(D_68))), inference(cnfTransformation, [status(thm)], [f_175])).
% 4.95/1.90  tff(c_80, plain, (![A_75]: (~r1_tarski(A_75, '#skF_5') | ~v3_pre_topc(A_75, '#skF_3') | ~m1_connsp_2(A_75, '#skF_3', '#skF_4') | v1_xboole_0(A_75) | ~r1_tarski(A_75, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_75, c_46])).
% 4.95/1.90  tff(c_128, plain, (![A_85]: (~v3_pre_topc(A_85, '#skF_3') | ~m1_connsp_2(A_85, '#skF_3', '#skF_4') | v1_xboole_0(A_85) | ~r1_tarski(A_85, '#skF_5'))), inference(resolution, [status(thm)], [c_120, c_80])).
% 4.95/1.90  tff(c_1846, plain, (~v3_pre_topc(k1_tops_1('#skF_3', '#skF_5'), '#skF_3') | v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~r1_tarski(k1_tops_1('#skF_3', '#skF_5'), '#skF_5') | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5')) | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1840, c_128])).
% 4.95/1.90  tff(c_1853, plain, (v1_xboole_0(k1_tops_1('#skF_3', '#skF_5')) | ~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_222, c_1286, c_1846])).
% 4.95/1.90  tff(c_1854, plain, (~r2_hidden('#skF_4', k1_tops_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_1515, c_1853])).
% 4.95/1.90  tff(c_1886, plain, (~m1_connsp_2('#skF_5', '#skF_3', '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1409, c_1854])).
% 4.95/1.90  tff(c_1890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1886])).
% 4.95/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.95/1.90  
% 4.95/1.90  Inference rules
% 4.95/1.90  ----------------------
% 4.95/1.90  #Ref     : 0
% 4.95/1.90  #Sup     : 400
% 4.95/1.90  #Fact    : 0
% 4.95/1.90  #Define  : 0
% 4.95/1.90  #Split   : 12
% 4.95/1.90  #Chain   : 0
% 4.95/1.90  #Close   : 0
% 4.95/1.90  
% 4.95/1.90  Ordering : KBO
% 4.95/1.90  
% 4.95/1.90  Simplification rules
% 4.95/1.90  ----------------------
% 4.95/1.90  #Subsume      : 73
% 4.95/1.90  #Demod        : 176
% 4.95/1.90  #Tautology    : 60
% 4.95/1.90  #SimpNegUnit  : 14
% 4.95/1.90  #BackRed      : 0
% 4.95/1.90  
% 4.95/1.90  #Partial instantiations: 0
% 4.95/1.90  #Strategies tried      : 1
% 4.95/1.90  
% 4.95/1.90  Timing (in seconds)
% 4.95/1.90  ----------------------
% 4.95/1.90  Preprocessing        : 0.33
% 4.95/1.90  Parsing              : 0.18
% 4.95/1.90  CNF conversion       : 0.03
% 4.95/1.90  Main loop            : 0.77
% 4.95/1.90  Inferencing          : 0.24
% 4.95/1.90  Reduction            : 0.22
% 4.95/1.90  Demodulation         : 0.15
% 4.95/1.90  BG Simplification    : 0.03
% 4.95/1.90  Subsumption          : 0.22
% 4.95/1.90  Abstraction          : 0.04
% 4.95/1.90  MUC search           : 0.00
% 4.95/1.90  Cooper               : 0.00
% 4.95/1.90  Total                : 1.16
% 4.95/1.90  Index Insertion      : 0.00
% 4.95/1.90  Index Deletion       : 0.00
% 4.95/1.90  Index Matching       : 0.00
% 4.95/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
