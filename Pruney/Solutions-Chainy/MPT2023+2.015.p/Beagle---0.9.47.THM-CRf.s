%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:31:14 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 447 expanded)
%              Number of leaves         :   30 ( 185 expanded)
%              Depth                    :   17
%              Number of atoms          :  239 (1728 expanded)
%              Number of equality atoms :   17 (  81 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k9_yellow_6,type,(
    k9_yellow_6: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
               => ! [D] :
                    ( m1_subset_1(D,u1_struct_0(k9_yellow_6(A,B)))
                   => m1_subset_1(k3_xboole_0(C,D),u1_struct_0(k9_yellow_6(A,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

tff(f_86,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k9_yellow_6(A,B)))
             => ? [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                  & D = C
                  & r2_hidden(B,D)
                  & v3_pre_topc(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A)
        & v3_pre_topc(B,A)
        & m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
        & v3_pre_topc(C,A)
        & m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) )
     => v3_pre_topc(k3_xboole_0(B,C),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

tff(f_105,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( r2_hidden(C,u1_struct_0(k9_yellow_6(A,B)))
              <=> ( r2_hidden(B,C)
                  & v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_56,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_353,plain,(
    ! [A_129,B_130,C_131] :
      ( '#skF_3'(A_129,B_130,C_131) = C_131
      | ~ m1_subset_1(C_131,u1_struct_0(k9_yellow_6(A_129,B_130)))
      | ~ m1_subset_1(B_130,u1_struct_0(A_129))
      | ~ l1_pre_topc(A_129)
      | ~ v2_pre_topc(A_129)
      | v2_struct_0(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_364,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_353])).

tff(c_372,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_364])).

tff(c_373,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_372])).

tff(c_410,plain,(
    ! [B_134,A_135,C_136] :
      ( r2_hidden(B_134,'#skF_3'(A_135,B_134,C_136))
      | ~ m1_subset_1(C_136,u1_struct_0(k9_yellow_6(A_135,B_134)))
      | ~ m1_subset_1(B_134,u1_struct_0(A_135))
      | ~ l1_pre_topc(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_418,plain,
    ( r2_hidden('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_6'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_410])).

tff(c_425,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_373,c_418])).

tff(c_426,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_425])).

tff(c_48,plain,(
    m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_367,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_353])).

tff(c_376,plain,
    ( '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_367])).

tff(c_377,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_7') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_376])).

tff(c_420,plain,
    ( r2_hidden('#skF_5','#skF_3'('#skF_4','#skF_5','#skF_7'))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_410])).

tff(c_429,plain,
    ( r2_hidden('#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_377,c_420])).

tff(c_430,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_429])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k3_xboole_0(A_1,B_2))
      | ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_271,plain,(
    ! [A_116,B_117,C_118] :
      ( ~ r2_hidden('#skF_1'(A_116,B_117,C_118),C_118)
      | r2_hidden('#skF_2'(A_116,B_117,C_118),C_118)
      | k3_xboole_0(A_116,B_117) = C_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_285,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k3_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_271])).

tff(c_485,plain,(
    ! [A_147,B_148,C_149] :
      ( r2_hidden('#skF_1'(A_147,B_148,C_149),A_147)
      | ~ r2_hidden('#skF_2'(A_147,B_148,C_149),B_148)
      | ~ r2_hidden('#skF_2'(A_147,B_148,C_149),A_147)
      | k3_xboole_0(A_147,B_148) = C_149 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_675,plain,(
    ! [A_165,C_166] :
      ( ~ r2_hidden('#skF_2'(A_165,C_166,C_166),A_165)
      | r2_hidden('#skF_1'(A_165,C_166,C_166),A_165)
      | k3_xboole_0(A_165,C_166) = C_166 ) ),
    inference(resolution,[status(thm)],[c_18,c_485])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_699,plain,(
    ! [A_167] :
      ( ~ r2_hidden('#skF_2'(A_167,A_167,A_167),A_167)
      | k3_xboole_0(A_167,A_167) = A_167 ) ),
    inference(resolution,[status(thm)],[c_675,c_8])).

tff(c_755,plain,(
    ! [B_171] : k3_xboole_0(B_171,B_171) = B_171 ),
    inference(resolution,[status(thm)],[c_285,c_699])).

tff(c_20,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_884,plain,(
    ! [B_171] : r1_tarski(B_171,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_755,c_20])).

tff(c_1231,plain,(
    ! [A_191,B_192,C_193] :
      ( m1_subset_1('#skF_3'(A_191,B_192,C_193),k1_zfmisc_1(u1_struct_0(A_191)))
      | ~ m1_subset_1(C_193,u1_struct_0(k9_yellow_6(A_191,B_192)))
      | ~ m1_subset_1(B_192,u1_struct_0(A_191))
      | ~ l1_pre_topc(A_191)
      | ~ v2_pre_topc(A_191)
      | v2_struct_0(A_191) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1240,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_6',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_1231])).

tff(c_1246,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_50,c_1240])).

tff(c_1247,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1246])).

tff(c_26,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,B_15)
      | ~ m1_subset_1(A_14,k1_zfmisc_1(B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1258,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1247,c_26])).

tff(c_22,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1266,plain,(
    ! [A_195] :
      ( r1_tarski(A_195,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_195,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1258,c_22])).

tff(c_1322,plain,(
    ! [A_200,A_201] :
      ( r1_tarski(A_200,u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_200,A_201)
      | ~ r1_tarski(A_201,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1266,c_22])).

tff(c_1366,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(k3_xboole_0(A_7,B_8),u1_struct_0('#skF_4'))
      | ~ r1_tarski(A_7,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_20,c_1322])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(A_14,k1_zfmisc_1(B_15))
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_463,plain,(
    ! [A_144,B_145,C_146] :
      ( v3_pre_topc('#skF_3'(A_144,B_145,C_146),A_144)
      | ~ m1_subset_1(C_146,u1_struct_0(k9_yellow_6(A_144,B_145)))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_pre_topc(A_144)
      | ~ v2_pre_topc(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_471,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_463])).

tff(c_478,plain,
    ( v3_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_373,c_471])).

tff(c_479,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_478])).

tff(c_473,plain,
    ( v3_pre_topc('#skF_3'('#skF_4','#skF_5','#skF_7'),'#skF_4')
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_463])).

tff(c_482,plain,
    ( v3_pre_topc('#skF_7','#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_377,c_473])).

tff(c_483,plain,(
    v3_pre_topc('#skF_7','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_482])).

tff(c_1237,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_7',u1_struct_0(k9_yellow_6('#skF_4','#skF_5')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_1231])).

tff(c_1243,plain,
    ( m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_48,c_1237])).

tff(c_1244,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1243])).

tff(c_1367,plain,(
    ! [B_202,C_203,A_204] :
      ( v3_pre_topc(k3_xboole_0(B_202,C_203),A_204)
      | ~ m1_subset_1(C_203,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ v3_pre_topc(C_203,A_204)
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0(A_204)))
      | ~ v3_pre_topc(B_202,A_204)
      | ~ l1_pre_topc(A_204)
      | ~ v2_pre_topc(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1371,plain,(
    ! [B_202] :
      ( v3_pre_topc(k3_xboole_0(B_202,'#skF_7'),'#skF_4')
      | ~ v3_pre_topc('#skF_7','#skF_4')
      | ~ m1_subset_1(B_202,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_202,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1244,c_1367])).

tff(c_1653,plain,(
    ! [B_221] :
      ( v3_pre_topc(k3_xboole_0(B_221,'#skF_7'),'#skF_4')
      | ~ m1_subset_1(B_221,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ v3_pre_topc(B_221,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_483,c_1371])).

tff(c_1656,plain,
    ( v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_1247,c_1653])).

tff(c_1710,plain,(
    v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_479,c_1656])).

tff(c_1729,plain,(
    ! [C_222,A_223,B_224] :
      ( r2_hidden(C_222,u1_struct_0(k9_yellow_6(A_223,B_224)))
      | ~ v3_pre_topc(C_222,A_223)
      | ~ r2_hidden(B_224,C_222)
      | ~ m1_subset_1(C_222,k1_zfmisc_1(u1_struct_0(A_223)))
      | ~ m1_subset_1(B_224,u1_struct_0(A_223))
      | ~ l1_pre_topc(A_223)
      | ~ v2_pre_topc(A_223)
      | v2_struct_0(A_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(A_12,B_13)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_6528,plain,(
    ! [C_507,A_508,B_509] :
      ( m1_subset_1(C_507,u1_struct_0(k9_yellow_6(A_508,B_509)))
      | ~ v3_pre_topc(C_507,A_508)
      | ~ r2_hidden(B_509,C_507)
      | ~ m1_subset_1(C_507,k1_zfmisc_1(u1_struct_0(A_508)))
      | ~ m1_subset_1(B_509,u1_struct_0(A_508))
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(resolution,[status(thm)],[c_1729,c_24])).

tff(c_46,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0(k9_yellow_6('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_6538,plain,
    ( ~ v3_pre_topc(k3_xboole_0('#skF_6','#skF_7'),'#skF_4')
    | ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | ~ m1_subset_1('#skF_5',u1_struct_0('#skF_4'))
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_6528,c_46])).

tff(c_6544,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4')))
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_1710,c_6538])).

tff(c_6545,plain,
    ( ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7'))
    | ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_6544])).

tff(c_6546,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_6','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_6545])).

tff(c_6550,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_6','#skF_7'),u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_28,c_6546])).

tff(c_6553,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_1366,c_6550])).

tff(c_6566,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_6553])).

tff(c_6567,plain,(
    ~ r2_hidden('#skF_5',k3_xboole_0('#skF_6','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_6545])).

tff(c_6571,plain,
    ( ~ r2_hidden('#skF_5','#skF_7')
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_6567])).

tff(c_6575,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_426,c_430,c_6571])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.26  % Computer   : n001.cluster.edu
% 0.07/0.26  % Model      : x86_64 x86_64
% 0.07/0.26  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.26  % Memory     : 8042.1875MB
% 0.07/0.26  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.26  % CPULimit   : 60
% 0.07/0.26  % DateTime   : Tue Dec  1 18:53:15 EST 2020
% 0.07/0.26  % CPUTime    : 
% 0.07/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.90/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/2.55  
% 7.90/2.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/2.56  %$ v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > l1_pre_topc > k9_yellow_6 > k3_xboole_0 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 7.90/2.56  
% 7.90/2.56  %Foreground sorts:
% 7.90/2.56  
% 7.90/2.56  
% 7.90/2.56  %Background operators:
% 7.90/2.56  
% 7.90/2.56  
% 7.90/2.56  %Foreground operators:
% 7.90/2.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.90/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.90/2.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.90/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.90/2.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.90/2.56  tff('#skF_7', type, '#skF_7': $i).
% 7.90/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.90/2.56  tff('#skF_5', type, '#skF_5': $i).
% 7.90/2.56  tff('#skF_6', type, '#skF_6': $i).
% 7.90/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.90/2.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.90/2.56  tff(k9_yellow_6, type, k9_yellow_6: ($i * $i) > $i).
% 7.90/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/2.56  tff('#skF_4', type, '#skF_4': $i).
% 7.90/2.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.90/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/2.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.90/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.90/2.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.90/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.90/2.56  
% 7.90/2.57  tff(f_124, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (![D]: (m1_subset_1(D, u1_struct_0(k9_yellow_6(A, B))) => m1_subset_1(k3_xboole_0(C, D), u1_struct_0(k9_yellow_6(A, B))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_waybel_9)).
% 7.90/2.57  tff(f_86, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(k9_yellow_6(A, B))) => (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & (D = C)) & r2_hidden(B, D)) & v3_pre_topc(D, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_yellow_6)).
% 7.90/2.57  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.90/2.57  tff(f_36, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.90/2.57  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.90/2.57  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.90/2.57  tff(f_64, axiom, (![A, B, C]: ((((((v2_pre_topc(A) & l1_pre_topc(A)) & v3_pre_topc(B, A)) & m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A)))) & v3_pre_topc(C, A)) & m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A)))) => v3_pre_topc(k3_xboole_0(B, C), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_tops_1)).
% 7.90/2.57  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(C, u1_struct_0(k9_yellow_6(A, B))) <=> (r2_hidden(B, C) & v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_yellow_6)).
% 7.90/2.57  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.90/2.57  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.90/2.57  tff(c_56, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.90/2.57  tff(c_54, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.90/2.57  tff(c_52, plain, (m1_subset_1('#skF_5', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.90/2.57  tff(c_50, plain, (m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.90/2.57  tff(c_353, plain, (![A_129, B_130, C_131]: ('#skF_3'(A_129, B_130, C_131)=C_131 | ~m1_subset_1(C_131, u1_struct_0(k9_yellow_6(A_129, B_130))) | ~m1_subset_1(B_130, u1_struct_0(A_129)) | ~l1_pre_topc(A_129) | ~v2_pre_topc(A_129) | v2_struct_0(A_129))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.90/2.57  tff(c_364, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_353])).
% 7.90/2.57  tff(c_372, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_364])).
% 7.90/2.57  tff(c_373, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_58, c_372])).
% 7.90/2.57  tff(c_410, plain, (![B_134, A_135, C_136]: (r2_hidden(B_134, '#skF_3'(A_135, B_134, C_136)) | ~m1_subset_1(C_136, u1_struct_0(k9_yellow_6(A_135, B_134))) | ~m1_subset_1(B_134, u1_struct_0(A_135)) | ~l1_pre_topc(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.90/2.57  tff(c_418, plain, (r2_hidden('#skF_5', '#skF_3'('#skF_4', '#skF_5', '#skF_6')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_410])).
% 7.90/2.57  tff(c_425, plain, (r2_hidden('#skF_5', '#skF_6') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_373, c_418])).
% 7.90/2.57  tff(c_426, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_58, c_425])).
% 7.90/2.57  tff(c_48, plain, (m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.90/2.57  tff(c_367, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_353])).
% 7.90/2.57  tff(c_376, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_367])).
% 7.90/2.57  tff(c_377, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_7')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_58, c_376])).
% 7.90/2.57  tff(c_420, plain, (r2_hidden('#skF_5', '#skF_3'('#skF_4', '#skF_5', '#skF_7')) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_410])).
% 7.90/2.57  tff(c_429, plain, (r2_hidden('#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_377, c_420])).
% 7.90/2.57  tff(c_430, plain, (r2_hidden('#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_58, c_429])).
% 7.90/2.57  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k3_xboole_0(A_1, B_2)) | ~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.90/2.57  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.90/2.57  tff(c_271, plain, (![A_116, B_117, C_118]: (~r2_hidden('#skF_1'(A_116, B_117, C_118), C_118) | r2_hidden('#skF_2'(A_116, B_117, C_118), C_118) | k3_xboole_0(A_116, B_117)=C_118)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.90/2.57  tff(c_285, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k3_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_271])).
% 7.90/2.57  tff(c_485, plain, (![A_147, B_148, C_149]: (r2_hidden('#skF_1'(A_147, B_148, C_149), A_147) | ~r2_hidden('#skF_2'(A_147, B_148, C_149), B_148) | ~r2_hidden('#skF_2'(A_147, B_148, C_149), A_147) | k3_xboole_0(A_147, B_148)=C_149)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.90/2.57  tff(c_675, plain, (![A_165, C_166]: (~r2_hidden('#skF_2'(A_165, C_166, C_166), A_165) | r2_hidden('#skF_1'(A_165, C_166, C_166), A_165) | k3_xboole_0(A_165, C_166)=C_166)), inference(resolution, [status(thm)], [c_18, c_485])).
% 7.90/2.57  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.90/2.57  tff(c_699, plain, (![A_167]: (~r2_hidden('#skF_2'(A_167, A_167, A_167), A_167) | k3_xboole_0(A_167, A_167)=A_167)), inference(resolution, [status(thm)], [c_675, c_8])).
% 7.90/2.57  tff(c_755, plain, (![B_171]: (k3_xboole_0(B_171, B_171)=B_171)), inference(resolution, [status(thm)], [c_285, c_699])).
% 7.90/2.57  tff(c_20, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.90/2.57  tff(c_884, plain, (![B_171]: (r1_tarski(B_171, B_171))), inference(superposition, [status(thm), theory('equality')], [c_755, c_20])).
% 7.90/2.57  tff(c_1231, plain, (![A_191, B_192, C_193]: (m1_subset_1('#skF_3'(A_191, B_192, C_193), k1_zfmisc_1(u1_struct_0(A_191))) | ~m1_subset_1(C_193, u1_struct_0(k9_yellow_6(A_191, B_192))) | ~m1_subset_1(B_192, u1_struct_0(A_191)) | ~l1_pre_topc(A_191) | ~v2_pre_topc(A_191) | v2_struct_0(A_191))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.90/2.57  tff(c_1240, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_373, c_1231])).
% 7.90/2.57  tff(c_1246, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_50, c_1240])).
% 7.90/2.57  tff(c_1247, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1246])).
% 7.90/2.57  tff(c_26, plain, (![A_14, B_15]: (r1_tarski(A_14, B_15) | ~m1_subset_1(A_14, k1_zfmisc_1(B_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.90/2.57  tff(c_1258, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1247, c_26])).
% 7.90/2.57  tff(c_22, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.90/2.57  tff(c_1266, plain, (![A_195]: (r1_tarski(A_195, u1_struct_0('#skF_4')) | ~r1_tarski(A_195, '#skF_6'))), inference(resolution, [status(thm)], [c_1258, c_22])).
% 7.90/2.57  tff(c_1322, plain, (![A_200, A_201]: (r1_tarski(A_200, u1_struct_0('#skF_4')) | ~r1_tarski(A_200, A_201) | ~r1_tarski(A_201, '#skF_6'))), inference(resolution, [status(thm)], [c_1266, c_22])).
% 7.90/2.57  tff(c_1366, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), u1_struct_0('#skF_4')) | ~r1_tarski(A_7, '#skF_6'))), inference(resolution, [status(thm)], [c_20, c_1322])).
% 7.90/2.57  tff(c_28, plain, (![A_14, B_15]: (m1_subset_1(A_14, k1_zfmisc_1(B_15)) | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 7.90/2.57  tff(c_463, plain, (![A_144, B_145, C_146]: (v3_pre_topc('#skF_3'(A_144, B_145, C_146), A_144) | ~m1_subset_1(C_146, u1_struct_0(k9_yellow_6(A_144, B_145))) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l1_pre_topc(A_144) | ~v2_pre_topc(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.90/2.57  tff(c_471, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_6'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_50, c_463])).
% 7.90/2.57  tff(c_478, plain, (v3_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_373, c_471])).
% 7.90/2.57  tff(c_479, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_478])).
% 7.90/2.57  tff(c_473, plain, (v3_pre_topc('#skF_3'('#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_463])).
% 7.90/2.57  tff(c_482, plain, (v3_pre_topc('#skF_7', '#skF_4') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_377, c_473])).
% 7.90/2.57  tff(c_483, plain, (v3_pre_topc('#skF_7', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_482])).
% 7.90/2.57  tff(c_1237, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_7', u1_struct_0(k9_yellow_6('#skF_4', '#skF_5'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_377, c_1231])).
% 7.90/2.57  tff(c_1243, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_48, c_1237])).
% 7.90/2.57  tff(c_1244, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1243])).
% 7.90/2.57  tff(c_1367, plain, (![B_202, C_203, A_204]: (v3_pre_topc(k3_xboole_0(B_202, C_203), A_204) | ~m1_subset_1(C_203, k1_zfmisc_1(u1_struct_0(A_204))) | ~v3_pre_topc(C_203, A_204) | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0(A_204))) | ~v3_pre_topc(B_202, A_204) | ~l1_pre_topc(A_204) | ~v2_pre_topc(A_204))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.90/2.57  tff(c_1371, plain, (![B_202]: (v3_pre_topc(k3_xboole_0(B_202, '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_7', '#skF_4') | ~m1_subset_1(B_202, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_202, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_1244, c_1367])).
% 7.90/2.57  tff(c_1653, plain, (![B_221]: (v3_pre_topc(k3_xboole_0(B_221, '#skF_7'), '#skF_4') | ~m1_subset_1(B_221, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~v3_pre_topc(B_221, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_483, c_1371])).
% 7.90/2.57  tff(c_1656, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_1247, c_1653])).
% 7.90/2.57  tff(c_1710, plain, (v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_479, c_1656])).
% 7.90/2.57  tff(c_1729, plain, (![C_222, A_223, B_224]: (r2_hidden(C_222, u1_struct_0(k9_yellow_6(A_223, B_224))) | ~v3_pre_topc(C_222, A_223) | ~r2_hidden(B_224, C_222) | ~m1_subset_1(C_222, k1_zfmisc_1(u1_struct_0(A_223))) | ~m1_subset_1(B_224, u1_struct_0(A_223)) | ~l1_pre_topc(A_223) | ~v2_pre_topc(A_223) | v2_struct_0(A_223))), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.90/2.57  tff(c_24, plain, (![A_12, B_13]: (m1_subset_1(A_12, B_13) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.90/2.57  tff(c_6528, plain, (![C_507, A_508, B_509]: (m1_subset_1(C_507, u1_struct_0(k9_yellow_6(A_508, B_509))) | ~v3_pre_topc(C_507, A_508) | ~r2_hidden(B_509, C_507) | ~m1_subset_1(C_507, k1_zfmisc_1(u1_struct_0(A_508))) | ~m1_subset_1(B_509, u1_struct_0(A_508)) | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(resolution, [status(thm)], [c_1729, c_24])).
% 7.90/2.57  tff(c_46, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0(k9_yellow_6('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.90/2.57  tff(c_6538, plain, (~v3_pre_topc(k3_xboole_0('#skF_6', '#skF_7'), '#skF_4') | ~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_5', u1_struct_0('#skF_4')) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_6528, c_46])).
% 7.90/2.57  tff(c_6544, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_1710, c_6538])).
% 7.90/2.57  tff(c_6545, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7')) | ~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_6544])).
% 7.90/2.57  tff(c_6546, plain, (~m1_subset_1(k3_xboole_0('#skF_6', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(splitLeft, [status(thm)], [c_6545])).
% 7.90/2.57  tff(c_6550, plain, (~r1_tarski(k3_xboole_0('#skF_6', '#skF_7'), u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_28, c_6546])).
% 7.90/2.57  tff(c_6553, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_1366, c_6550])).
% 7.90/2.57  tff(c_6566, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_884, c_6553])).
% 7.90/2.57  tff(c_6567, plain, (~r2_hidden('#skF_5', k3_xboole_0('#skF_6', '#skF_7'))), inference(splitRight, [status(thm)], [c_6545])).
% 7.90/2.57  tff(c_6571, plain, (~r2_hidden('#skF_5', '#skF_7') | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_6567])).
% 7.90/2.57  tff(c_6575, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_426, c_430, c_6571])).
% 7.90/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/2.57  
% 7.90/2.57  Inference rules
% 7.90/2.57  ----------------------
% 7.90/2.57  #Ref     : 0
% 7.90/2.57  #Sup     : 1392
% 7.90/2.57  #Fact    : 0
% 7.90/2.57  #Define  : 0
% 7.90/2.57  #Split   : 1
% 7.90/2.57  #Chain   : 0
% 7.90/2.57  #Close   : 0
% 7.90/2.57  
% 7.90/2.57  Ordering : KBO
% 7.90/2.57  
% 7.90/2.57  Simplification rules
% 7.90/2.57  ----------------------
% 7.90/2.57  #Subsume      : 255
% 7.90/2.57  #Demod        : 304
% 7.90/2.57  #Tautology    : 127
% 7.90/2.57  #SimpNegUnit  : 13
% 7.90/2.57  #BackRed      : 0
% 7.90/2.57  
% 7.90/2.57  #Partial instantiations: 0
% 7.90/2.57  #Strategies tried      : 1
% 7.90/2.57  
% 7.90/2.57  Timing (in seconds)
% 7.90/2.57  ----------------------
% 7.90/2.58  Preprocessing        : 0.33
% 7.90/2.58  Parsing              : 0.17
% 7.90/2.58  CNF conversion       : 0.03
% 7.90/2.58  Main loop            : 1.58
% 7.90/2.58  Inferencing          : 0.56
% 7.90/2.58  Reduction            : 0.39
% 7.90/2.58  Demodulation         : 0.28
% 7.90/2.58  BG Simplification    : 0.07
% 7.90/2.58  Subsumption          : 0.44
% 7.90/2.58  Abstraction          : 0.11
% 7.90/2.58  MUC search           : 0.00
% 7.90/2.58  Cooper               : 0.00
% 7.90/2.58  Total                : 1.95
% 7.90/2.58  Index Insertion      : 0.00
% 7.90/2.58  Index Deletion       : 0.00
% 7.90/2.58  Index Matching       : 0.00
% 7.90/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
