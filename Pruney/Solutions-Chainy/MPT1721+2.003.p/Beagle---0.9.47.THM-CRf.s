%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:44 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.76s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 109 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :   16
%              Number of atoms          :  280 ( 674 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_tsep_1,type,(
    k2_tsep_1: ( $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,A) )
                   => ( ( m1_pre_topc(B,D)
                        & m1_pre_topc(C,D) )
                     => ( r1_tsep_1(B,C)
                        | m1_pre_topc(k2_tsep_1(A,B,C),D) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & m1_pre_topc(B,A)
        & ~ v2_struct_0(C)
        & m1_pre_topc(C,A) )
     => ( ~ v2_struct_0(k2_tsep_1(A,B,C))
        & v1_pre_topc(k2_tsep_1(A,B,C))
        & m1_pre_topc(k2_tsep_1(A,B,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( ~ r1_tsep_1(B,C)
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & v1_pre_topc(D)
                      & m1_pre_topc(D,A) )
                   => ( D = k2_tsep_1(A,B,C)
                    <=> u1_struct_0(D) = k3_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_113,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_36,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_24,plain,(
    ~ r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_38,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_34,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_28,plain,(
    m1_pre_topc('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_26,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_42,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_pre_topc(k2_tsep_1(A_22,B_23,C_24),A_22)
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_30,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_48,plain,(
    ! [B_45,A_46] :
      ( l1_pre_topc(B_45)
      | ~ m1_pre_topc(B_45,A_46)
      | ~ l1_pre_topc(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_60,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_48])).

tff(c_72,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_60])).

tff(c_44,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_79,plain,(
    ! [B_47,A_48] :
      ( v2_pre_topc(B_47)
      | ~ m1_pre_topc(B_47,A_48)
      | ~ l1_pre_topc(A_48)
      | ~ v2_pre_topc(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_91,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_79])).

tff(c_103,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_91])).

tff(c_12,plain,(
    ! [A_22,B_23,C_24] :
      ( v1_pre_topc(k2_tsep_1(A_22,B_23,C_24))
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_194,plain,(
    ! [A_85,B_86,C_87] :
      ( u1_struct_0(k2_tsep_1(A_85,B_86,C_87)) = k3_xboole_0(u1_struct_0(B_86),u1_struct_0(C_87))
      | ~ m1_pre_topc(k2_tsep_1(A_85,B_86,C_87),A_85)
      | ~ v1_pre_topc(k2_tsep_1(A_85,B_86,C_87))
      | v2_struct_0(k2_tsep_1(A_85,B_86,C_87))
      | r1_tsep_1(B_86,C_87)
      | ~ m1_pre_topc(C_87,A_85)
      | v2_struct_0(C_87)
      | ~ m1_pre_topc(B_86,A_85)
      | v2_struct_0(B_86)
      | ~ l1_pre_topc(A_85)
      | v2_struct_0(A_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_198,plain,(
    ! [A_88,B_89,C_90] :
      ( u1_struct_0(k2_tsep_1(A_88,B_89,C_90)) = k3_xboole_0(u1_struct_0(B_89),u1_struct_0(C_90))
      | ~ v1_pre_topc(k2_tsep_1(A_88,B_89,C_90))
      | v2_struct_0(k2_tsep_1(A_88,B_89,C_90))
      | r1_tsep_1(B_89,C_90)
      | ~ m1_pre_topc(C_90,A_88)
      | v2_struct_0(C_90)
      | ~ m1_pre_topc(B_89,A_88)
      | v2_struct_0(B_89)
      | ~ l1_pre_topc(A_88)
      | v2_struct_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_10,c_194])).

tff(c_14,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ v2_struct_0(k2_tsep_1(A_22,B_23,C_24))
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_268,plain,(
    ! [A_91,B_92,C_93] :
      ( u1_struct_0(k2_tsep_1(A_91,B_92,C_93)) = k3_xboole_0(u1_struct_0(B_92),u1_struct_0(C_93))
      | ~ v1_pre_topc(k2_tsep_1(A_91,B_92,C_93))
      | r1_tsep_1(B_92,C_93)
      | ~ m1_pre_topc(C_93,A_91)
      | v2_struct_0(C_93)
      | ~ m1_pre_topc(B_92,A_91)
      | v2_struct_0(B_92)
      | ~ l1_pre_topc(A_91)
      | v2_struct_0(A_91) ) ),
    inference(resolution,[status(thm)],[c_198,c_14])).

tff(c_272,plain,(
    ! [A_94,B_95,C_96] :
      ( u1_struct_0(k2_tsep_1(A_94,B_95,C_96)) = k3_xboole_0(u1_struct_0(B_95),u1_struct_0(C_96))
      | r1_tsep_1(B_95,C_96)
      | ~ m1_pre_topc(C_96,A_94)
      | v2_struct_0(C_96)
      | ~ m1_pre_topc(B_95,A_94)
      | v2_struct_0(B_95)
      | ~ l1_pre_topc(A_94)
      | v2_struct_0(A_94) ) ),
    inference(resolution,[status(thm)],[c_12,c_268])).

tff(c_16,plain,(
    ! [A_25] :
      ( m1_pre_topc(A_25,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_117,plain,(
    ! [B_49,C_50,A_51] :
      ( r1_tarski(u1_struct_0(B_49),u1_struct_0(C_50))
      | ~ m1_pre_topc(B_49,C_50)
      | ~ m1_pre_topc(C_50,A_51)
      | ~ m1_pre_topc(B_49,A_51)
      | ~ l1_pre_topc(A_51)
      | ~ v2_pre_topc(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_130,plain,(
    ! [B_49,A_25] :
      ( r1_tarski(u1_struct_0(B_49),u1_struct_0(A_25))
      | ~ m1_pre_topc(B_49,A_25)
      | ~ v2_pre_topc(A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(resolution,[status(thm)],[c_16,c_117])).

tff(c_346,plain,(
    ! [B_101,C_102,A_103,A_104] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_101),u1_struct_0(C_102)),u1_struct_0(A_103))
      | ~ m1_pre_topc(k2_tsep_1(A_104,B_101,C_102),A_103)
      | ~ v2_pre_topc(A_103)
      | ~ l1_pre_topc(A_103)
      | r1_tsep_1(B_101,C_102)
      | ~ m1_pre_topc(C_102,A_104)
      | v2_struct_0(C_102)
      | ~ m1_pre_topc(B_101,A_104)
      | v2_struct_0(B_101)
      | ~ l1_pre_topc(A_104)
      | v2_struct_0(A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_130])).

tff(c_352,plain,(
    ! [B_23,C_24,A_22] :
      ( r1_tarski(k3_xboole_0(u1_struct_0(B_23),u1_struct_0(C_24)),u1_struct_0(A_22))
      | ~ v2_pre_topc(A_22)
      | r1_tsep_1(B_23,C_24)
      | ~ m1_pre_topc(C_24,A_22)
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,A_22)
      | v2_struct_0(B_23)
      | ~ l1_pre_topc(A_22)
      | v2_struct_0(A_22) ) ),
    inference(resolution,[status(thm)],[c_10,c_346])).

tff(c_20,plain,(
    ! [B_30,C_32,A_26] :
      ( m1_pre_topc(B_30,C_32)
      | ~ r1_tarski(u1_struct_0(B_30),u1_struct_0(C_32))
      | ~ m1_pre_topc(C_32,A_26)
      | ~ m1_pre_topc(B_30,A_26)
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_753,plain,(
    ! [A_152,B_155,A_154,C_156,C_153] :
      ( m1_pre_topc(k2_tsep_1(A_152,B_155,C_156),C_153)
      | ~ r1_tarski(k3_xboole_0(u1_struct_0(B_155),u1_struct_0(C_156)),u1_struct_0(C_153))
      | ~ m1_pre_topc(C_153,A_154)
      | ~ m1_pre_topc(k2_tsep_1(A_152,B_155,C_156),A_154)
      | ~ l1_pre_topc(A_154)
      | ~ v2_pre_topc(A_154)
      | r1_tsep_1(B_155,C_156)
      | ~ m1_pre_topc(C_156,A_152)
      | v2_struct_0(C_156)
      | ~ m1_pre_topc(B_155,A_152)
      | v2_struct_0(B_155)
      | ~ l1_pre_topc(A_152)
      | v2_struct_0(A_152) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_20])).

tff(c_900,plain,(
    ! [B_194,A_190,A_193,A_192,C_191] :
      ( m1_pre_topc(k2_tsep_1(A_192,B_194,C_191),A_190)
      | ~ m1_pre_topc(A_190,A_193)
      | ~ m1_pre_topc(k2_tsep_1(A_192,B_194,C_191),A_193)
      | ~ l1_pre_topc(A_193)
      | ~ v2_pre_topc(A_193)
      | ~ m1_pre_topc(C_191,A_192)
      | ~ m1_pre_topc(B_194,A_192)
      | ~ l1_pre_topc(A_192)
      | v2_struct_0(A_192)
      | ~ v2_pre_topc(A_190)
      | r1_tsep_1(B_194,C_191)
      | ~ m1_pre_topc(C_191,A_190)
      | v2_struct_0(C_191)
      | ~ m1_pre_topc(B_194,A_190)
      | v2_struct_0(B_194)
      | ~ l1_pre_topc(A_190)
      | v2_struct_0(A_190) ) ),
    inference(resolution,[status(thm)],[c_352,c_753])).

tff(c_910,plain,(
    ! [A_192,B_194,C_191] :
      ( m1_pre_topc(k2_tsep_1(A_192,B_194,C_191),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_192,B_194,C_191),'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | ~ m1_pre_topc(C_191,A_192)
      | ~ m1_pre_topc(B_194,A_192)
      | ~ l1_pre_topc(A_192)
      | v2_struct_0(A_192)
      | ~ v2_pre_topc('#skF_4')
      | r1_tsep_1(B_194,C_191)
      | ~ m1_pre_topc(C_191,'#skF_4')
      | v2_struct_0(C_191)
      | ~ m1_pre_topc(B_194,'#skF_4')
      | v2_struct_0(B_194)
      | ~ l1_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_900])).

tff(c_927,plain,(
    ! [A_192,B_194,C_191] :
      ( m1_pre_topc(k2_tsep_1(A_192,B_194,C_191),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_192,B_194,C_191),'#skF_1')
      | ~ m1_pre_topc(C_191,A_192)
      | ~ m1_pre_topc(B_194,A_192)
      | ~ l1_pre_topc(A_192)
      | v2_struct_0(A_192)
      | r1_tsep_1(B_194,C_191)
      | ~ m1_pre_topc(C_191,'#skF_4')
      | v2_struct_0(C_191)
      | ~ m1_pre_topc(B_194,'#skF_4')
      | v2_struct_0(B_194)
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_103,c_44,c_42,c_910])).

tff(c_1153,plain,(
    ! [A_227,B_228,C_229] :
      ( m1_pre_topc(k2_tsep_1(A_227,B_228,C_229),'#skF_4')
      | ~ m1_pre_topc(k2_tsep_1(A_227,B_228,C_229),'#skF_1')
      | ~ m1_pre_topc(C_229,A_227)
      | ~ m1_pre_topc(B_228,A_227)
      | ~ l1_pre_topc(A_227)
      | v2_struct_0(A_227)
      | r1_tsep_1(B_228,C_229)
      | ~ m1_pre_topc(C_229,'#skF_4')
      | v2_struct_0(C_229)
      | ~ m1_pre_topc(B_228,'#skF_4')
      | v2_struct_0(B_228) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_927])).

tff(c_1157,plain,(
    ! [B_23,C_24] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_23,C_24),'#skF_4')
      | r1_tsep_1(B_23,C_24)
      | ~ m1_pre_topc(C_24,'#skF_4')
      | ~ m1_pre_topc(B_23,'#skF_4')
      | ~ m1_pre_topc(C_24,'#skF_1')
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,'#skF_1')
      | v2_struct_0(B_23)
      | ~ l1_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10,c_1153])).

tff(c_1160,plain,(
    ! [B_23,C_24] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_23,C_24),'#skF_4')
      | r1_tsep_1(B_23,C_24)
      | ~ m1_pre_topc(C_24,'#skF_4')
      | ~ m1_pre_topc(B_23,'#skF_4')
      | ~ m1_pre_topc(C_24,'#skF_1')
      | v2_struct_0(C_24)
      | ~ m1_pre_topc(B_23,'#skF_1')
      | v2_struct_0(B_23)
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1157])).

tff(c_1162,plain,(
    ! [B_230,C_231] :
      ( m1_pre_topc(k2_tsep_1('#skF_1',B_230,C_231),'#skF_4')
      | r1_tsep_1(B_230,C_231)
      | ~ m1_pre_topc(C_231,'#skF_4')
      | ~ m1_pre_topc(B_230,'#skF_4')
      | ~ m1_pre_topc(C_231,'#skF_1')
      | v2_struct_0(C_231)
      | ~ m1_pre_topc(B_230,'#skF_1')
      | v2_struct_0(B_230) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1160])).

tff(c_22,plain,(
    ~ m1_pre_topc(k2_tsep_1('#skF_1','#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_1189,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_2','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1162,c_22])).

tff(c_1225,plain,
    ( r1_tsep_1('#skF_2','#skF_3')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_28,c_26,c_1189])).

tff(c_1227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_36,c_24,c_1225])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.83  
% 4.76/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.83  %$ r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > l1_pre_topc > k2_tsep_1 > k3_xboole_0 > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.76/1.83  
% 4.76/1.83  %Foreground sorts:
% 4.76/1.83  
% 4.76/1.83  
% 4.76/1.83  %Background operators:
% 4.76/1.83  
% 4.76/1.83  
% 4.76/1.83  %Foreground operators:
% 4.76/1.83  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.76/1.83  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.76/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.76/1.83  tff('#skF_2', type, '#skF_2': $i).
% 4.76/1.83  tff('#skF_3', type, '#skF_3': $i).
% 4.76/1.83  tff('#skF_1', type, '#skF_1': $i).
% 4.76/1.83  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.76/1.83  tff('#skF_4', type, '#skF_4': $i).
% 4.76/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.76/1.83  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.76/1.83  tff(k2_tsep_1, type, k2_tsep_1: ($i * $i * $i) > $i).
% 4.76/1.83  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.76/1.83  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 4.76/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.76/1.83  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.76/1.83  
% 4.76/1.85  tff(f_147, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => ((m1_pre_topc(B, D) & m1_pre_topc(C, D)) => (r1_tsep_1(B, C) | m1_pre_topc(k2_tsep_1(A, B, C), D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_tmap_1)).
% 4.76/1.85  tff(f_95, axiom, (![A, B, C]: ((((((~v2_struct_0(A) & l1_pre_topc(A)) & ~v2_struct_0(B)) & m1_pre_topc(B, A)) & ~v2_struct_0(C)) & m1_pre_topc(C, A)) => ((~v2_struct_0(k2_tsep_1(A, B, C)) & v1_pre_topc(k2_tsep_1(A, B, C))) & m1_pre_topc(k2_tsep_1(A, B, C), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_tsep_1)).
% 4.76/1.85  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.76/1.85  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.76/1.85  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (~r1_tsep_1(B, C) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k2_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k3_xboole_0(u1_struct_0(B), u1_struct_0(C))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tsep_1)).
% 4.76/1.85  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.76/1.85  tff(f_113, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.76/1.85  tff(c_40, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_36, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_24, plain, (~r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_38, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_34, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_28, plain, (m1_pre_topc('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_26, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_46, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_42, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_10, plain, (![A_22, B_23, C_24]: (m1_pre_topc(k2_tsep_1(A_22, B_23, C_24), A_22) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.76/1.85  tff(c_32, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_30, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_48, plain, (![B_45, A_46]: (l1_pre_topc(B_45) | ~m1_pre_topc(B_45, A_46) | ~l1_pre_topc(A_46))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.76/1.85  tff(c_60, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_48])).
% 4.76/1.85  tff(c_72, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_60])).
% 4.76/1.85  tff(c_44, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_79, plain, (![B_47, A_48]: (v2_pre_topc(B_47) | ~m1_pre_topc(B_47, A_48) | ~l1_pre_topc(A_48) | ~v2_pre_topc(A_48))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.76/1.85  tff(c_91, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_30, c_79])).
% 4.76/1.85  tff(c_103, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_91])).
% 4.76/1.85  tff(c_12, plain, (![A_22, B_23, C_24]: (v1_pre_topc(k2_tsep_1(A_22, B_23, C_24)) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.76/1.85  tff(c_194, plain, (![A_85, B_86, C_87]: (u1_struct_0(k2_tsep_1(A_85, B_86, C_87))=k3_xboole_0(u1_struct_0(B_86), u1_struct_0(C_87)) | ~m1_pre_topc(k2_tsep_1(A_85, B_86, C_87), A_85) | ~v1_pre_topc(k2_tsep_1(A_85, B_86, C_87)) | v2_struct_0(k2_tsep_1(A_85, B_86, C_87)) | r1_tsep_1(B_86, C_87) | ~m1_pre_topc(C_87, A_85) | v2_struct_0(C_87) | ~m1_pre_topc(B_86, A_85) | v2_struct_0(B_86) | ~l1_pre_topc(A_85) | v2_struct_0(A_85))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.76/1.85  tff(c_198, plain, (![A_88, B_89, C_90]: (u1_struct_0(k2_tsep_1(A_88, B_89, C_90))=k3_xboole_0(u1_struct_0(B_89), u1_struct_0(C_90)) | ~v1_pre_topc(k2_tsep_1(A_88, B_89, C_90)) | v2_struct_0(k2_tsep_1(A_88, B_89, C_90)) | r1_tsep_1(B_89, C_90) | ~m1_pre_topc(C_90, A_88) | v2_struct_0(C_90) | ~m1_pre_topc(B_89, A_88) | v2_struct_0(B_89) | ~l1_pre_topc(A_88) | v2_struct_0(A_88))), inference(resolution, [status(thm)], [c_10, c_194])).
% 4.76/1.85  tff(c_14, plain, (![A_22, B_23, C_24]: (~v2_struct_0(k2_tsep_1(A_22, B_23, C_24)) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.76/1.85  tff(c_268, plain, (![A_91, B_92, C_93]: (u1_struct_0(k2_tsep_1(A_91, B_92, C_93))=k3_xboole_0(u1_struct_0(B_92), u1_struct_0(C_93)) | ~v1_pre_topc(k2_tsep_1(A_91, B_92, C_93)) | r1_tsep_1(B_92, C_93) | ~m1_pre_topc(C_93, A_91) | v2_struct_0(C_93) | ~m1_pre_topc(B_92, A_91) | v2_struct_0(B_92) | ~l1_pre_topc(A_91) | v2_struct_0(A_91))), inference(resolution, [status(thm)], [c_198, c_14])).
% 4.76/1.85  tff(c_272, plain, (![A_94, B_95, C_96]: (u1_struct_0(k2_tsep_1(A_94, B_95, C_96))=k3_xboole_0(u1_struct_0(B_95), u1_struct_0(C_96)) | r1_tsep_1(B_95, C_96) | ~m1_pre_topc(C_96, A_94) | v2_struct_0(C_96) | ~m1_pre_topc(B_95, A_94) | v2_struct_0(B_95) | ~l1_pre_topc(A_94) | v2_struct_0(A_94))), inference(resolution, [status(thm)], [c_12, c_268])).
% 4.76/1.85  tff(c_16, plain, (![A_25]: (m1_pre_topc(A_25, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.76/1.85  tff(c_117, plain, (![B_49, C_50, A_51]: (r1_tarski(u1_struct_0(B_49), u1_struct_0(C_50)) | ~m1_pre_topc(B_49, C_50) | ~m1_pre_topc(C_50, A_51) | ~m1_pre_topc(B_49, A_51) | ~l1_pre_topc(A_51) | ~v2_pre_topc(A_51))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.76/1.85  tff(c_130, plain, (![B_49, A_25]: (r1_tarski(u1_struct_0(B_49), u1_struct_0(A_25)) | ~m1_pre_topc(B_49, A_25) | ~v2_pre_topc(A_25) | ~l1_pre_topc(A_25))), inference(resolution, [status(thm)], [c_16, c_117])).
% 4.76/1.85  tff(c_346, plain, (![B_101, C_102, A_103, A_104]: (r1_tarski(k3_xboole_0(u1_struct_0(B_101), u1_struct_0(C_102)), u1_struct_0(A_103)) | ~m1_pre_topc(k2_tsep_1(A_104, B_101, C_102), A_103) | ~v2_pre_topc(A_103) | ~l1_pre_topc(A_103) | r1_tsep_1(B_101, C_102) | ~m1_pre_topc(C_102, A_104) | v2_struct_0(C_102) | ~m1_pre_topc(B_101, A_104) | v2_struct_0(B_101) | ~l1_pre_topc(A_104) | v2_struct_0(A_104))), inference(superposition, [status(thm), theory('equality')], [c_272, c_130])).
% 4.76/1.85  tff(c_352, plain, (![B_23, C_24, A_22]: (r1_tarski(k3_xboole_0(u1_struct_0(B_23), u1_struct_0(C_24)), u1_struct_0(A_22)) | ~v2_pre_topc(A_22) | r1_tsep_1(B_23, C_24) | ~m1_pre_topc(C_24, A_22) | v2_struct_0(C_24) | ~m1_pre_topc(B_23, A_22) | v2_struct_0(B_23) | ~l1_pre_topc(A_22) | v2_struct_0(A_22))), inference(resolution, [status(thm)], [c_10, c_346])).
% 4.76/1.85  tff(c_20, plain, (![B_30, C_32, A_26]: (m1_pre_topc(B_30, C_32) | ~r1_tarski(u1_struct_0(B_30), u1_struct_0(C_32)) | ~m1_pre_topc(C_32, A_26) | ~m1_pre_topc(B_30, A_26) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.76/1.85  tff(c_753, plain, (![A_152, B_155, A_154, C_156, C_153]: (m1_pre_topc(k2_tsep_1(A_152, B_155, C_156), C_153) | ~r1_tarski(k3_xboole_0(u1_struct_0(B_155), u1_struct_0(C_156)), u1_struct_0(C_153)) | ~m1_pre_topc(C_153, A_154) | ~m1_pre_topc(k2_tsep_1(A_152, B_155, C_156), A_154) | ~l1_pre_topc(A_154) | ~v2_pre_topc(A_154) | r1_tsep_1(B_155, C_156) | ~m1_pre_topc(C_156, A_152) | v2_struct_0(C_156) | ~m1_pre_topc(B_155, A_152) | v2_struct_0(B_155) | ~l1_pre_topc(A_152) | v2_struct_0(A_152))), inference(superposition, [status(thm), theory('equality')], [c_272, c_20])).
% 4.76/1.85  tff(c_900, plain, (![B_194, A_190, A_193, A_192, C_191]: (m1_pre_topc(k2_tsep_1(A_192, B_194, C_191), A_190) | ~m1_pre_topc(A_190, A_193) | ~m1_pre_topc(k2_tsep_1(A_192, B_194, C_191), A_193) | ~l1_pre_topc(A_193) | ~v2_pre_topc(A_193) | ~m1_pre_topc(C_191, A_192) | ~m1_pre_topc(B_194, A_192) | ~l1_pre_topc(A_192) | v2_struct_0(A_192) | ~v2_pre_topc(A_190) | r1_tsep_1(B_194, C_191) | ~m1_pre_topc(C_191, A_190) | v2_struct_0(C_191) | ~m1_pre_topc(B_194, A_190) | v2_struct_0(B_194) | ~l1_pre_topc(A_190) | v2_struct_0(A_190))), inference(resolution, [status(thm)], [c_352, c_753])).
% 4.76/1.85  tff(c_910, plain, (![A_192, B_194, C_191]: (m1_pre_topc(k2_tsep_1(A_192, B_194, C_191), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_192, B_194, C_191), '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | ~m1_pre_topc(C_191, A_192) | ~m1_pre_topc(B_194, A_192) | ~l1_pre_topc(A_192) | v2_struct_0(A_192) | ~v2_pre_topc('#skF_4') | r1_tsep_1(B_194, C_191) | ~m1_pre_topc(C_191, '#skF_4') | v2_struct_0(C_191) | ~m1_pre_topc(B_194, '#skF_4') | v2_struct_0(B_194) | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_900])).
% 4.76/1.85  tff(c_927, plain, (![A_192, B_194, C_191]: (m1_pre_topc(k2_tsep_1(A_192, B_194, C_191), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_192, B_194, C_191), '#skF_1') | ~m1_pre_topc(C_191, A_192) | ~m1_pre_topc(B_194, A_192) | ~l1_pre_topc(A_192) | v2_struct_0(A_192) | r1_tsep_1(B_194, C_191) | ~m1_pre_topc(C_191, '#skF_4') | v2_struct_0(C_191) | ~m1_pre_topc(B_194, '#skF_4') | v2_struct_0(B_194) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_103, c_44, c_42, c_910])).
% 4.76/1.85  tff(c_1153, plain, (![A_227, B_228, C_229]: (m1_pre_topc(k2_tsep_1(A_227, B_228, C_229), '#skF_4') | ~m1_pre_topc(k2_tsep_1(A_227, B_228, C_229), '#skF_1') | ~m1_pre_topc(C_229, A_227) | ~m1_pre_topc(B_228, A_227) | ~l1_pre_topc(A_227) | v2_struct_0(A_227) | r1_tsep_1(B_228, C_229) | ~m1_pre_topc(C_229, '#skF_4') | v2_struct_0(C_229) | ~m1_pre_topc(B_228, '#skF_4') | v2_struct_0(B_228))), inference(negUnitSimplification, [status(thm)], [c_32, c_927])).
% 4.76/1.85  tff(c_1157, plain, (![B_23, C_24]: (m1_pre_topc(k2_tsep_1('#skF_1', B_23, C_24), '#skF_4') | r1_tsep_1(B_23, C_24) | ~m1_pre_topc(C_24, '#skF_4') | ~m1_pre_topc(B_23, '#skF_4') | ~m1_pre_topc(C_24, '#skF_1') | v2_struct_0(C_24) | ~m1_pre_topc(B_23, '#skF_1') | v2_struct_0(B_23) | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_10, c_1153])).
% 4.76/1.85  tff(c_1160, plain, (![B_23, C_24]: (m1_pre_topc(k2_tsep_1('#skF_1', B_23, C_24), '#skF_4') | r1_tsep_1(B_23, C_24) | ~m1_pre_topc(C_24, '#skF_4') | ~m1_pre_topc(B_23, '#skF_4') | ~m1_pre_topc(C_24, '#skF_1') | v2_struct_0(C_24) | ~m1_pre_topc(B_23, '#skF_1') | v2_struct_0(B_23) | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1157])).
% 4.76/1.85  tff(c_1162, plain, (![B_230, C_231]: (m1_pre_topc(k2_tsep_1('#skF_1', B_230, C_231), '#skF_4') | r1_tsep_1(B_230, C_231) | ~m1_pre_topc(C_231, '#skF_4') | ~m1_pre_topc(B_230, '#skF_4') | ~m1_pre_topc(C_231, '#skF_1') | v2_struct_0(C_231) | ~m1_pre_topc(B_230, '#skF_1') | v2_struct_0(B_230))), inference(negUnitSimplification, [status(thm)], [c_46, c_1160])).
% 4.76/1.85  tff(c_22, plain, (~m1_pre_topc(k2_tsep_1('#skF_1', '#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.76/1.85  tff(c_1189, plain, (r1_tsep_1('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_2', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1162, c_22])).
% 4.76/1.85  tff(c_1225, plain, (r1_tsep_1('#skF_2', '#skF_3') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_28, c_26, c_1189])).
% 4.76/1.85  tff(c_1227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_36, c_24, c_1225])).
% 4.76/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.76/1.85  
% 4.76/1.85  Inference rules
% 4.76/1.85  ----------------------
% 4.76/1.85  #Ref     : 0
% 4.76/1.85  #Sup     : 315
% 4.76/1.85  #Fact    : 0
% 4.76/1.85  #Define  : 0
% 4.76/1.85  #Split   : 0
% 4.76/1.85  #Chain   : 0
% 4.76/1.85  #Close   : 0
% 4.76/1.85  
% 4.76/1.85  Ordering : KBO
% 4.76/1.85  
% 4.76/1.85  Simplification rules
% 4.76/1.85  ----------------------
% 4.76/1.85  #Subsume      : 53
% 4.76/1.85  #Demod        : 134
% 4.76/1.85  #Tautology    : 20
% 4.76/1.85  #SimpNegUnit  : 21
% 4.76/1.85  #BackRed      : 0
% 4.76/1.85  
% 4.76/1.85  #Partial instantiations: 0
% 4.76/1.85  #Strategies tried      : 1
% 4.76/1.85  
% 4.76/1.85  Timing (in seconds)
% 4.76/1.85  ----------------------
% 4.76/1.85  Preprocessing        : 0.30
% 4.76/1.85  Parsing              : 0.16
% 4.76/1.85  CNF conversion       : 0.03
% 4.76/1.85  Main loop            : 0.74
% 4.76/1.85  Inferencing          : 0.26
% 4.76/1.85  Reduction            : 0.18
% 4.76/1.85  Demodulation         : 0.12
% 4.76/1.85  BG Simplification    : 0.03
% 4.76/1.85  Subsumption          : 0.24
% 4.76/1.85  Abstraction          : 0.03
% 4.76/1.85  MUC search           : 0.00
% 4.76/1.85  Cooper               : 0.00
% 4.76/1.85  Total                : 1.08
% 4.76/1.85  Index Insertion      : 0.00
% 4.76/1.85  Index Deletion       : 0.00
% 4.76/1.85  Index Matching       : 0.00
% 4.76/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
