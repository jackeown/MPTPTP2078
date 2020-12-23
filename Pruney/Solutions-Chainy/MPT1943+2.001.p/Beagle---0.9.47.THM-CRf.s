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
% DateTime   : Thu Dec  3 10:30:53 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  115 (1207 expanded)
%              Number of leaves         :   37 ( 491 expanded)
%              Depth                    :   34
%              Number of atoms          :  439 (6236 expanded)
%              Number of equality atoms :    1 (   5 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k6_subset_1 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(r2_waybel_0,type,(
    r2_waybel_0: ( $i * $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_yellow_6,type,(
    k10_yellow_6: ( $i * $i ) > $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v7_waybel_0,type,(
    v7_waybel_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_waybel_0,type,(
    r1_waybel_0: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(l1_waybel_0,type,(
    l1_waybel_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_181,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & v4_orders_2(B)
              & v7_waybel_0(B)
              & l1_waybel_0(B,A) )
           => ! [C] :
                ( m2_yellow_6(C,A,B)
               => r1_tarski(k10_yellow_6(A,B),k10_yellow_6(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_yellow_6)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_109,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => m1_subset_1(k10_yellow_6(A,B),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_yellow_6)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A)
        & ~ v2_struct_0(B)
        & v4_orders_2(B)
        & v7_waybel_0(B)
        & l1_waybel_0(B,A) )
     => ! [C] :
          ( m2_yellow_6(C,A,B)
         => ( ~ v2_struct_0(C)
            & v4_orders_2(C)
            & v7_waybel_0(C)
            & l1_waybel_0(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_yellow_6)).

tff(f_59,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( r1_waybel_0(A,B,C)
            <=> ~ r2_waybel_0(A,B,k6_subset_1(u1_struct_0(A),C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_waybel_0)).

tff(f_158,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m2_yellow_6(C,A,B)
             => ! [D] :
                  ( r2_waybel_0(A,C,D)
                 => r2_waybel_0(A,B,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_yellow_6)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v4_orders_2(B)
            & v7_waybel_0(B)
            & l1_waybel_0(B,A) )
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = k10_yellow_6(A,B)
              <=> ! [D] :
                    ( m1_subset_1(D,u1_struct_0(A))
                   => ( r2_hidden(D,C)
                    <=> ! [E] :
                          ( m1_connsp_2(E,A,D)
                         => r1_waybel_0(A,B,E) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_yellow_6)).

tff(c_48,plain,(
    ~ r1_tarski(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_62,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_60,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_56,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_54,plain,(
    v7_waybel_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_52,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_140,plain,(
    ! [A_163,B_164] :
      ( m1_subset_1(k10_yellow_6(A_163,B_164),k1_zfmisc_1(u1_struct_0(A_163)))
      | ~ l1_waybel_0(B_164,A_163)
      | ~ v7_waybel_0(B_164)
      | ~ v4_orders_2(B_164)
      | v2_struct_0(B_164)
      | ~ l1_pre_topc(A_163)
      | ~ v2_pre_topc(A_163)
      | v2_struct_0(A_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( m1_subset_1(A_6,C_8)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(C_8))
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_144,plain,(
    ! [A_165,A_166,B_167] :
      ( m1_subset_1(A_165,u1_struct_0(A_166))
      | ~ r2_hidden(A_165,k10_yellow_6(A_166,B_167))
      | ~ l1_waybel_0(B_167,A_166)
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166) ) ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_154,plain,(
    ! [A_166,B_167,B_2] :
      ( m1_subset_1('#skF_1'(k10_yellow_6(A_166,B_167),B_2),u1_struct_0(A_166))
      | ~ l1_waybel_0(B_167,A_166)
      | ~ v7_waybel_0(B_167)
      | ~ v4_orders_2(B_167)
      | v2_struct_0(B_167)
      | ~ l1_pre_topc(A_166)
      | ~ v2_pre_topc(A_166)
      | v2_struct_0(A_166)
      | r1_tarski(k10_yellow_6(A_166,B_167),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_144])).

tff(c_36,plain,(
    ! [A_101,B_102] :
      ( m1_subset_1(k10_yellow_6(A_101,B_102),k1_zfmisc_1(u1_struct_0(A_101)))
      | ~ l1_waybel_0(B_102,A_101)
      | ~ v7_waybel_0(B_102)
      | ~ v4_orders_2(B_102)
      | v2_struct_0(B_102)
      | ~ l1_pre_topc(A_101)
      | ~ v2_pre_topc(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_10,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_50,plain,(
    m2_yellow_6('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_181])).

tff(c_79,plain,(
    ! [C_138,A_139,B_140] :
      ( v7_waybel_0(C_138)
      | ~ m2_yellow_6(C_138,A_139,B_140)
      | ~ l1_waybel_0(B_140,A_139)
      | ~ v7_waybel_0(B_140)
      | ~ v4_orders_2(B_140)
      | v2_struct_0(B_140)
      | ~ l1_struct_0(A_139)
      | v2_struct_0(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_82,plain,
    ( v7_waybel_0('#skF_7')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_79])).

tff(c_85,plain,
    ( v7_waybel_0('#skF_7')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_82])).

tff(c_86,plain,
    ( v7_waybel_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_85])).

tff(c_87,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_90,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_10,c_87])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_90])).

tff(c_96,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_118,plain,(
    ! [C_151,A_152,B_153] :
      ( ~ v2_struct_0(C_151)
      | ~ m2_yellow_6(C_151,A_152,B_153)
      | ~ l1_waybel_0(B_153,A_152)
      | ~ v7_waybel_0(B_153)
      | ~ v4_orders_2(B_153)
      | v2_struct_0(B_153)
      | ~ l1_struct_0(A_152)
      | v2_struct_0(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_121,plain,
    ( ~ v2_struct_0('#skF_7')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_118])).

tff(c_124,plain,
    ( ~ v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_56,c_54,c_52,c_121])).

tff(c_125,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_124])).

tff(c_110,plain,(
    ! [C_148,A_149,B_150] :
      ( v4_orders_2(C_148)
      | ~ m2_yellow_6(C_148,A_149,B_150)
      | ~ l1_waybel_0(B_150,A_149)
      | ~ v7_waybel_0(B_150)
      | ~ v4_orders_2(B_150)
      | v2_struct_0(B_150)
      | ~ l1_struct_0(A_149)
      | v2_struct_0(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_113,plain,
    ( v4_orders_2('#skF_7')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_110])).

tff(c_116,plain,
    ( v4_orders_2('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_56,c_54,c_52,c_113])).

tff(c_117,plain,(
    v4_orders_2('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_116])).

tff(c_95,plain,(
    v7_waybel_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_126,plain,(
    ! [C_154,A_155,B_156] :
      ( l1_waybel_0(C_154,A_155)
      | ~ m2_yellow_6(C_154,A_155,B_156)
      | ~ l1_waybel_0(B_156,A_155)
      | ~ v7_waybel_0(B_156)
      | ~ v4_orders_2(B_156)
      | v2_struct_0(B_156)
      | ~ l1_struct_0(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_129,plain,
    ( l1_waybel_0('#skF_7','#skF_5')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_50,c_126])).

tff(c_132,plain,
    ( l1_waybel_0('#skF_7','#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_56,c_54,c_52,c_129])).

tff(c_133,plain,(
    l1_waybel_0('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_132])).

tff(c_14,plain,(
    ! [A_10,B_14,C_16] :
      ( r1_waybel_0(A_10,B_14,C_16)
      | r2_waybel_0(A_10,B_14,k6_subset_1(u1_struct_0(A_10),C_16))
      | ~ l1_waybel_0(B_14,A_10)
      | v2_struct_0(B_14)
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_155,plain,(
    ! [A_168,B_169,D_170,C_171] :
      ( r2_waybel_0(A_168,B_169,D_170)
      | ~ r2_waybel_0(A_168,C_171,D_170)
      | ~ m2_yellow_6(C_171,A_168,B_169)
      | ~ l1_waybel_0(B_169,A_168)
      | ~ v7_waybel_0(B_169)
      | ~ v4_orders_2(B_169)
      | v2_struct_0(B_169)
      | ~ l1_struct_0(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_158])).

tff(c_166,plain,(
    ! [A_182,B_183,C_184,B_185] :
      ( r2_waybel_0(A_182,B_183,k6_subset_1(u1_struct_0(A_182),C_184))
      | ~ m2_yellow_6(B_185,A_182,B_183)
      | ~ l1_waybel_0(B_183,A_182)
      | ~ v7_waybel_0(B_183)
      | ~ v4_orders_2(B_183)
      | v2_struct_0(B_183)
      | r1_waybel_0(A_182,B_185,C_184)
      | ~ l1_waybel_0(B_185,A_182)
      | v2_struct_0(B_185)
      | ~ l1_struct_0(A_182)
      | v2_struct_0(A_182) ) ),
    inference(resolution,[status(thm)],[c_14,c_155])).

tff(c_168,plain,(
    ! [C_184] :
      ( r2_waybel_0('#skF_5','#skF_6',k6_subset_1(u1_struct_0('#skF_5'),C_184))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | r1_waybel_0('#skF_5','#skF_7',C_184)
      | ~ l1_waybel_0('#skF_7','#skF_5')
      | v2_struct_0('#skF_7')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_50,c_166])).

tff(c_171,plain,(
    ! [C_184] :
      ( r2_waybel_0('#skF_5','#skF_6',k6_subset_1(u1_struct_0('#skF_5'),C_184))
      | v2_struct_0('#skF_6')
      | r1_waybel_0('#skF_5','#skF_7',C_184)
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_133,c_56,c_54,c_52,c_168])).

tff(c_173,plain,(
    ! [C_186] :
      ( r2_waybel_0('#skF_5','#skF_6',k6_subset_1(u1_struct_0('#skF_5'),C_186))
      | r1_waybel_0('#skF_5','#skF_7',C_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_125,c_58,c_171])).

tff(c_12,plain,(
    ! [A_10,B_14,C_16] :
      ( ~ r2_waybel_0(A_10,B_14,k6_subset_1(u1_struct_0(A_10),C_16))
      | ~ r1_waybel_0(A_10,B_14,C_16)
      | ~ l1_waybel_0(B_14,A_10)
      | v2_struct_0(B_14)
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_178,plain,(
    ! [C_186] :
      ( ~ r1_waybel_0('#skF_5','#skF_6',C_186)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_waybel_0('#skF_5','#skF_7',C_186) ) ),
    inference(resolution,[status(thm)],[c_173,c_12])).

tff(c_185,plain,(
    ! [C_186] :
      ( ~ r1_waybel_0('#skF_5','#skF_6',C_186)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | r1_waybel_0('#skF_5','#skF_7',C_186) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_52,c_178])).

tff(c_186,plain,(
    ! [C_186] :
      ( ~ r1_waybel_0('#skF_5','#skF_6',C_186)
      | r1_waybel_0('#skF_5','#skF_7',C_186) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_185])).

tff(c_230,plain,(
    ! [A_206,B_207,D_208] :
      ( ~ r1_waybel_0(A_206,B_207,'#skF_2'(A_206,B_207,k10_yellow_6(A_206,B_207),D_208))
      | r2_hidden(D_208,k10_yellow_6(A_206,B_207))
      | ~ m1_subset_1(D_208,u1_struct_0(A_206))
      | ~ m1_subset_1(k10_yellow_6(A_206,B_207),k1_zfmisc_1(u1_struct_0(A_206)))
      | ~ l1_waybel_0(B_207,A_206)
      | ~ v7_waybel_0(B_207)
      | ~ v4_orders_2(B_207)
      | v2_struct_0(B_207)
      | ~ l1_pre_topc(A_206)
      | ~ v2_pre_topc(A_206)
      | v2_struct_0(A_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_233,plain,(
    ! [D_208] :
      ( r2_hidden(D_208,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_208,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0('#skF_7','#skF_5')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_waybel_0('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_208)) ) ),
    inference(resolution,[status(thm)],[c_186,c_230])).

tff(c_236,plain,(
    ! [D_208] :
      ( r2_hidden(D_208,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_208,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | ~ r1_waybel_0('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_208)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_117,c_95,c_133,c_233])).

tff(c_237,plain,(
    ! [D_208] :
      ( r2_hidden(D_208,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_208,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_waybel_0('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_208)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_125,c_236])).

tff(c_238,plain,(
    ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_241,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_5')
    | ~ v7_waybel_0('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_238])).

tff(c_244,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_117,c_95,c_133,c_241])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_125,c_244])).

tff(c_248,plain,(
    m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_270,plain,(
    ! [A_218,B_219,D_220] :
      ( m1_connsp_2('#skF_2'(A_218,B_219,k10_yellow_6(A_218,B_219),D_220),A_218,D_220)
      | r2_hidden(D_220,k10_yellow_6(A_218,B_219))
      | ~ m1_subset_1(D_220,u1_struct_0(A_218))
      | ~ m1_subset_1(k10_yellow_6(A_218,B_219),k1_zfmisc_1(u1_struct_0(A_218)))
      | ~ l1_waybel_0(B_219,A_218)
      | ~ v7_waybel_0(B_219)
      | ~ v4_orders_2(B_219)
      | v2_struct_0(B_219)
      | ~ l1_pre_topc(A_218)
      | ~ v2_pre_topc(A_218)
      | v2_struct_0(A_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_272,plain,(
    ! [D_220] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_220),'#skF_5',D_220)
      | r2_hidden(D_220,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_220,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_7','#skF_5')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_248,c_270])).

tff(c_277,plain,(
    ! [D_220] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_220),'#skF_5',D_220)
      | r2_hidden(D_220,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_220,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_117,c_95,c_133,c_272])).

tff(c_280,plain,(
    ! [D_221] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_221),'#skF_5',D_221)
      | r2_hidden(D_221,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_221,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_125,c_277])).

tff(c_30,plain,(
    ! [A_17,B_61,E_97,D_94] :
      ( r1_waybel_0(A_17,B_61,E_97)
      | ~ m1_connsp_2(E_97,A_17,D_94)
      | ~ r2_hidden(D_94,k10_yellow_6(A_17,B_61))
      | ~ m1_subset_1(D_94,u1_struct_0(A_17))
      | ~ m1_subset_1(k10_yellow_6(A_17,B_61),k1_zfmisc_1(u1_struct_0(A_17)))
      | ~ l1_waybel_0(B_61,A_17)
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17)
      | v2_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_285,plain,(
    ! [B_61,D_221] :
      ( r1_waybel_0('#skF_5',B_61,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_221))
      | ~ r2_hidden(D_221,k10_yellow_6('#skF_5',B_61))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_61),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_61,'#skF_5')
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | r2_hidden(D_221,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_221,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_280,c_30])).

tff(c_292,plain,(
    ! [B_61,D_221] :
      ( r1_waybel_0('#skF_5',B_61,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_221))
      | ~ r2_hidden(D_221,k10_yellow_6('#skF_5',B_61))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_61),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_61,'#skF_5')
      | ~ v7_waybel_0(B_61)
      | ~ v4_orders_2(B_61)
      | v2_struct_0(B_61)
      | v2_struct_0('#skF_5')
      | r2_hidden(D_221,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_221,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_285])).

tff(c_302,plain,(
    ! [B_225,D_226] :
      ( r1_waybel_0('#skF_5',B_225,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_226))
      | ~ r2_hidden(D_226,k10_yellow_6('#skF_5',B_225))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_225),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_225,'#skF_5')
      | ~ v7_waybel_0(B_225)
      | ~ v4_orders_2(B_225)
      | v2_struct_0(B_225)
      | r2_hidden(D_226,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_226,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_292])).

tff(c_307,plain,(
    ! [B_102,D_226] :
      ( r1_waybel_0('#skF_5',B_102,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_226))
      | ~ r2_hidden(D_226,k10_yellow_6('#skF_5',B_102))
      | r2_hidden(D_226,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_226,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_102,'#skF_5')
      | ~ v7_waybel_0(B_102)
      | ~ v4_orders_2(B_102)
      | v2_struct_0(B_102)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_36,c_302])).

tff(c_314,plain,(
    ! [B_102,D_226] :
      ( r1_waybel_0('#skF_5',B_102,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_226))
      | ~ r2_hidden(D_226,k10_yellow_6('#skF_5',B_102))
      | r2_hidden(D_226,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_226,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_102,'#skF_5')
      | ~ v7_waybel_0(B_102)
      | ~ v4_orders_2(B_102)
      | v2_struct_0(B_102)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_307])).

tff(c_316,plain,(
    ! [B_227,D_228] :
      ( r1_waybel_0('#skF_5',B_227,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_228))
      | ~ r2_hidden(D_228,k10_yellow_6('#skF_5',B_227))
      | r2_hidden(D_228,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_228,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_227,'#skF_5')
      | ~ v7_waybel_0(B_227)
      | ~ v4_orders_2(B_227)
      | v2_struct_0(B_227) ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_314])).

tff(c_247,plain,(
    ! [D_208] :
      ( r2_hidden(D_208,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_208,u1_struct_0('#skF_5'))
      | ~ r1_waybel_0('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_208)) ) ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_320,plain,(
    ! [D_228] :
      ( ~ r2_hidden(D_228,k10_yellow_6('#skF_5','#skF_6'))
      | r2_hidden(D_228,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_228,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_316,c_247])).

tff(c_328,plain,(
    ! [D_228] :
      ( ~ r2_hidden(D_228,k10_yellow_6('#skF_5','#skF_6'))
      | r2_hidden(D_228,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_228,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_52,c_320])).

tff(c_335,plain,(
    ! [D_229] :
      ( ~ r2_hidden(D_229,k10_yellow_6('#skF_5','#skF_6'))
      | r2_hidden(D_229,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_229,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_328])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_367,plain,(
    ! [A_232] :
      ( r1_tarski(A_232,k10_yellow_6('#skF_5','#skF_7'))
      | ~ r2_hidden('#skF_1'(A_232,k10_yellow_6('#skF_5','#skF_7')),k10_yellow_6('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'(A_232,k10_yellow_6('#skF_5','#skF_7')),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_335,c_4])).

tff(c_375,plain,
    ( ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')),u1_struct_0('#skF_5'))
    | r1_tarski(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_6,c_367])).

tff(c_379,plain,(
    ~ m1_subset_1('#skF_1'(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')),u1_struct_0('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_48,c_375])).

tff(c_385,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | r1_tarski(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')) ),
    inference(resolution,[status(thm)],[c_154,c_379])).

tff(c_390,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | r1_tarski(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_56,c_54,c_52,c_385])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_64,c_58,c_390])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:29:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.43  
% 2.77/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.43  %$ r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k6_subset_1 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 2.77/1.43  
% 2.77/1.43  %Foreground sorts:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Background operators:
% 2.77/1.43  
% 2.77/1.43  
% 2.77/1.43  %Foreground operators:
% 2.77/1.43  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.77/1.43  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 2.77/1.43  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.77/1.43  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.77/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.77/1.43  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.77/1.43  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.77/1.43  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.77/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_7', type, '#skF_7': $i).
% 2.77/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.77/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.77/1.43  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.77/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.77/1.43  tff('#skF_6', type, '#skF_6': $i).
% 2.77/1.43  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.77/1.43  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.77/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.77/1.43  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.77/1.43  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.77/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.77/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.77/1.43  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.77/1.43  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.77/1.43  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.77/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.77/1.43  
% 2.77/1.45  tff(f_181, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => r1_tarski(k10_yellow_6(A, B), k10_yellow_6(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_yellow_6)).
% 2.77/1.45  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.77/1.45  tff(f_109, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 2.77/1.45  tff(f_38, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.77/1.45  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.77/1.45  tff(f_135, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 2.77/1.45  tff(f_59, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> ~r2_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_waybel_0)).
% 2.77/1.45  tff(f_158, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (r2_waybel_0(A, C, D) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_6)).
% 2.77/1.45  tff(f_91, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 2.77/1.45  tff(c_48, plain, (~r1_tarski(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_64, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_58, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_62, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_60, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_56, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_54, plain, (v7_waybel_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_52, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.45  tff(c_140, plain, (![A_163, B_164]: (m1_subset_1(k10_yellow_6(A_163, B_164), k1_zfmisc_1(u1_struct_0(A_163))) | ~l1_waybel_0(B_164, A_163) | ~v7_waybel_0(B_164) | ~v4_orders_2(B_164) | v2_struct_0(B_164) | ~l1_pre_topc(A_163) | ~v2_pre_topc(A_163) | v2_struct_0(A_163))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.77/1.45  tff(c_8, plain, (![A_6, C_8, B_7]: (m1_subset_1(A_6, C_8) | ~m1_subset_1(B_7, k1_zfmisc_1(C_8)) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.77/1.45  tff(c_144, plain, (![A_165, A_166, B_167]: (m1_subset_1(A_165, u1_struct_0(A_166)) | ~r2_hidden(A_165, k10_yellow_6(A_166, B_167)) | ~l1_waybel_0(B_167, A_166) | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166))), inference(resolution, [status(thm)], [c_140, c_8])).
% 2.77/1.45  tff(c_154, plain, (![A_166, B_167, B_2]: (m1_subset_1('#skF_1'(k10_yellow_6(A_166, B_167), B_2), u1_struct_0(A_166)) | ~l1_waybel_0(B_167, A_166) | ~v7_waybel_0(B_167) | ~v4_orders_2(B_167) | v2_struct_0(B_167) | ~l1_pre_topc(A_166) | ~v2_pre_topc(A_166) | v2_struct_0(A_166) | r1_tarski(k10_yellow_6(A_166, B_167), B_2))), inference(resolution, [status(thm)], [c_6, c_144])).
% 2.77/1.45  tff(c_36, plain, (![A_101, B_102]: (m1_subset_1(k10_yellow_6(A_101, B_102), k1_zfmisc_1(u1_struct_0(A_101))) | ~l1_waybel_0(B_102, A_101) | ~v7_waybel_0(B_102) | ~v4_orders_2(B_102) | v2_struct_0(B_102) | ~l1_pre_topc(A_101) | ~v2_pre_topc(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_109])).
% 2.77/1.45  tff(c_10, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.77/1.45  tff(c_50, plain, (m2_yellow_6('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_181])).
% 2.77/1.45  tff(c_79, plain, (![C_138, A_139, B_140]: (v7_waybel_0(C_138) | ~m2_yellow_6(C_138, A_139, B_140) | ~l1_waybel_0(B_140, A_139) | ~v7_waybel_0(B_140) | ~v4_orders_2(B_140) | v2_struct_0(B_140) | ~l1_struct_0(A_139) | v2_struct_0(A_139))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.77/1.45  tff(c_82, plain, (v7_waybel_0('#skF_7') | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_79])).
% 2.77/1.45  tff(c_85, plain, (v7_waybel_0('#skF_7') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_82])).
% 2.77/1.45  tff(c_86, plain, (v7_waybel_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_85])).
% 2.77/1.45  tff(c_87, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_86])).
% 2.77/1.45  tff(c_90, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_10, c_87])).
% 2.77/1.45  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_90])).
% 2.77/1.45  tff(c_96, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_86])).
% 2.77/1.45  tff(c_118, plain, (![C_151, A_152, B_153]: (~v2_struct_0(C_151) | ~m2_yellow_6(C_151, A_152, B_153) | ~l1_waybel_0(B_153, A_152) | ~v7_waybel_0(B_153) | ~v4_orders_2(B_153) | v2_struct_0(B_153) | ~l1_struct_0(A_152) | v2_struct_0(A_152))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.77/1.45  tff(c_121, plain, (~v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_118])).
% 2.77/1.45  tff(c_124, plain, (~v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_56, c_54, c_52, c_121])).
% 2.77/1.45  tff(c_125, plain, (~v2_struct_0('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_124])).
% 2.77/1.45  tff(c_110, plain, (![C_148, A_149, B_150]: (v4_orders_2(C_148) | ~m2_yellow_6(C_148, A_149, B_150) | ~l1_waybel_0(B_150, A_149) | ~v7_waybel_0(B_150) | ~v4_orders_2(B_150) | v2_struct_0(B_150) | ~l1_struct_0(A_149) | v2_struct_0(A_149))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.77/1.45  tff(c_113, plain, (v4_orders_2('#skF_7') | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_110])).
% 2.77/1.45  tff(c_116, plain, (v4_orders_2('#skF_7') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_56, c_54, c_52, c_113])).
% 2.77/1.45  tff(c_117, plain, (v4_orders_2('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_116])).
% 2.77/1.45  tff(c_95, plain, (v7_waybel_0('#skF_7')), inference(splitRight, [status(thm)], [c_86])).
% 2.77/1.45  tff(c_126, plain, (![C_154, A_155, B_156]: (l1_waybel_0(C_154, A_155) | ~m2_yellow_6(C_154, A_155, B_156) | ~l1_waybel_0(B_156, A_155) | ~v7_waybel_0(B_156) | ~v4_orders_2(B_156) | v2_struct_0(B_156) | ~l1_struct_0(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_135])).
% 2.77/1.45  tff(c_129, plain, (l1_waybel_0('#skF_7', '#skF_5') | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_50, c_126])).
% 2.77/1.45  tff(c_132, plain, (l1_waybel_0('#skF_7', '#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_56, c_54, c_52, c_129])).
% 2.77/1.45  tff(c_133, plain, (l1_waybel_0('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_132])).
% 2.77/1.45  tff(c_14, plain, (![A_10, B_14, C_16]: (r1_waybel_0(A_10, B_14, C_16) | r2_waybel_0(A_10, B_14, k6_subset_1(u1_struct_0(A_10), C_16)) | ~l1_waybel_0(B_14, A_10) | v2_struct_0(B_14) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.45  tff(c_155, plain, (![A_168, B_169, D_170, C_171]: (r2_waybel_0(A_168, B_169, D_170) | ~r2_waybel_0(A_168, C_171, D_170) | ~m2_yellow_6(C_171, A_168, B_169) | ~l1_waybel_0(B_169, A_168) | ~v7_waybel_0(B_169) | ~v4_orders_2(B_169) | v2_struct_0(B_169) | ~l1_struct_0(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_158])).
% 2.77/1.45  tff(c_166, plain, (![A_182, B_183, C_184, B_185]: (r2_waybel_0(A_182, B_183, k6_subset_1(u1_struct_0(A_182), C_184)) | ~m2_yellow_6(B_185, A_182, B_183) | ~l1_waybel_0(B_183, A_182) | ~v7_waybel_0(B_183) | ~v4_orders_2(B_183) | v2_struct_0(B_183) | r1_waybel_0(A_182, B_185, C_184) | ~l1_waybel_0(B_185, A_182) | v2_struct_0(B_185) | ~l1_struct_0(A_182) | v2_struct_0(A_182))), inference(resolution, [status(thm)], [c_14, c_155])).
% 2.77/1.45  tff(c_168, plain, (![C_184]: (r2_waybel_0('#skF_5', '#skF_6', k6_subset_1(u1_struct_0('#skF_5'), C_184)) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | r1_waybel_0('#skF_5', '#skF_7', C_184) | ~l1_waybel_0('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_50, c_166])).
% 2.77/1.45  tff(c_171, plain, (![C_184]: (r2_waybel_0('#skF_5', '#skF_6', k6_subset_1(u1_struct_0('#skF_5'), C_184)) | v2_struct_0('#skF_6') | r1_waybel_0('#skF_5', '#skF_7', C_184) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_133, c_56, c_54, c_52, c_168])).
% 2.77/1.45  tff(c_173, plain, (![C_186]: (r2_waybel_0('#skF_5', '#skF_6', k6_subset_1(u1_struct_0('#skF_5'), C_186)) | r1_waybel_0('#skF_5', '#skF_7', C_186))), inference(negUnitSimplification, [status(thm)], [c_64, c_125, c_58, c_171])).
% 2.77/1.45  tff(c_12, plain, (![A_10, B_14, C_16]: (~r2_waybel_0(A_10, B_14, k6_subset_1(u1_struct_0(A_10), C_16)) | ~r1_waybel_0(A_10, B_14, C_16) | ~l1_waybel_0(B_14, A_10) | v2_struct_0(B_14) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.77/1.45  tff(c_178, plain, (![C_186]: (~r1_waybel_0('#skF_5', '#skF_6', C_186) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | r1_waybel_0('#skF_5', '#skF_7', C_186))), inference(resolution, [status(thm)], [c_173, c_12])).
% 2.77/1.45  tff(c_185, plain, (![C_186]: (~r1_waybel_0('#skF_5', '#skF_6', C_186) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | r1_waybel_0('#skF_5', '#skF_7', C_186))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_52, c_178])).
% 2.77/1.45  tff(c_186, plain, (![C_186]: (~r1_waybel_0('#skF_5', '#skF_6', C_186) | r1_waybel_0('#skF_5', '#skF_7', C_186))), inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_185])).
% 2.77/1.45  tff(c_230, plain, (![A_206, B_207, D_208]: (~r1_waybel_0(A_206, B_207, '#skF_2'(A_206, B_207, k10_yellow_6(A_206, B_207), D_208)) | r2_hidden(D_208, k10_yellow_6(A_206, B_207)) | ~m1_subset_1(D_208, u1_struct_0(A_206)) | ~m1_subset_1(k10_yellow_6(A_206, B_207), k1_zfmisc_1(u1_struct_0(A_206))) | ~l1_waybel_0(B_207, A_206) | ~v7_waybel_0(B_207) | ~v4_orders_2(B_207) | v2_struct_0(B_207) | ~l1_pre_topc(A_206) | ~v2_pre_topc(A_206) | v2_struct_0(A_206))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.77/1.45  tff(c_233, plain, (![D_208]: (r2_hidden(D_208, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_208, u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r1_waybel_0('#skF_5', '#skF_6', '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_208)))), inference(resolution, [status(thm)], [c_186, c_230])).
% 2.77/1.45  tff(c_236, plain, (![D_208]: (r2_hidden(D_208, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_208, u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5') | ~r1_waybel_0('#skF_5', '#skF_6', '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_208)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_117, c_95, c_133, c_233])).
% 2.77/1.45  tff(c_237, plain, (![D_208]: (r2_hidden(D_208, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_208, u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_waybel_0('#skF_5', '#skF_6', '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_208)))), inference(negUnitSimplification, [status(thm)], [c_64, c_125, c_236])).
% 2.77/1.45  tff(c_238, plain, (~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_237])).
% 2.77/1.45  tff(c_241, plain, (~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_238])).
% 2.77/1.45  tff(c_244, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_117, c_95, c_133, c_241])).
% 2.77/1.45  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_125, c_244])).
% 2.77/1.45  tff(c_248, plain, (m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_237])).
% 2.77/1.45  tff(c_270, plain, (![A_218, B_219, D_220]: (m1_connsp_2('#skF_2'(A_218, B_219, k10_yellow_6(A_218, B_219), D_220), A_218, D_220) | r2_hidden(D_220, k10_yellow_6(A_218, B_219)) | ~m1_subset_1(D_220, u1_struct_0(A_218)) | ~m1_subset_1(k10_yellow_6(A_218, B_219), k1_zfmisc_1(u1_struct_0(A_218))) | ~l1_waybel_0(B_219, A_218) | ~v7_waybel_0(B_219) | ~v4_orders_2(B_219) | v2_struct_0(B_219) | ~l1_pre_topc(A_218) | ~v2_pre_topc(A_218) | v2_struct_0(A_218))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.77/1.45  tff(c_272, plain, (![D_220]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_220), '#skF_5', D_220) | r2_hidden(D_220, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_220, u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_248, c_270])).
% 2.77/1.45  tff(c_277, plain, (![D_220]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_220), '#skF_5', D_220) | r2_hidden(D_220, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_220, u1_struct_0('#skF_5')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_117, c_95, c_133, c_272])).
% 2.77/1.45  tff(c_280, plain, (![D_221]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_221), '#skF_5', D_221) | r2_hidden(D_221, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_221, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_125, c_277])).
% 2.77/1.45  tff(c_30, plain, (![A_17, B_61, E_97, D_94]: (r1_waybel_0(A_17, B_61, E_97) | ~m1_connsp_2(E_97, A_17, D_94) | ~r2_hidden(D_94, k10_yellow_6(A_17, B_61)) | ~m1_subset_1(D_94, u1_struct_0(A_17)) | ~m1_subset_1(k10_yellow_6(A_17, B_61), k1_zfmisc_1(u1_struct_0(A_17))) | ~l1_waybel_0(B_61, A_17) | ~v7_waybel_0(B_61) | ~v4_orders_2(B_61) | v2_struct_0(B_61) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17) | v2_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.77/1.45  tff(c_285, plain, (![B_61, D_221]: (r1_waybel_0('#skF_5', B_61, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_221)) | ~r2_hidden(D_221, k10_yellow_6('#skF_5', B_61)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_61), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_61, '#skF_5') | ~v7_waybel_0(B_61) | ~v4_orders_2(B_61) | v2_struct_0(B_61) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | r2_hidden(D_221, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_221, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_280, c_30])).
% 2.77/1.45  tff(c_292, plain, (![B_61, D_221]: (r1_waybel_0('#skF_5', B_61, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_221)) | ~r2_hidden(D_221, k10_yellow_6('#skF_5', B_61)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_61), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_61, '#skF_5') | ~v7_waybel_0(B_61) | ~v4_orders_2(B_61) | v2_struct_0(B_61) | v2_struct_0('#skF_5') | r2_hidden(D_221, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_221, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_285])).
% 2.77/1.45  tff(c_302, plain, (![B_225, D_226]: (r1_waybel_0('#skF_5', B_225, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_226)) | ~r2_hidden(D_226, k10_yellow_6('#skF_5', B_225)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_225), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_225, '#skF_5') | ~v7_waybel_0(B_225) | ~v4_orders_2(B_225) | v2_struct_0(B_225) | r2_hidden(D_226, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_226, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_64, c_292])).
% 2.77/1.45  tff(c_307, plain, (![B_102, D_226]: (r1_waybel_0('#skF_5', B_102, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_226)) | ~r2_hidden(D_226, k10_yellow_6('#skF_5', B_102)) | r2_hidden(D_226, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_226, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_102, '#skF_5') | ~v7_waybel_0(B_102) | ~v4_orders_2(B_102) | v2_struct_0(B_102) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_36, c_302])).
% 2.77/1.45  tff(c_314, plain, (![B_102, D_226]: (r1_waybel_0('#skF_5', B_102, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_226)) | ~r2_hidden(D_226, k10_yellow_6('#skF_5', B_102)) | r2_hidden(D_226, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_226, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_102, '#skF_5') | ~v7_waybel_0(B_102) | ~v4_orders_2(B_102) | v2_struct_0(B_102) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_307])).
% 2.77/1.45  tff(c_316, plain, (![B_227, D_228]: (r1_waybel_0('#skF_5', B_227, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_228)) | ~r2_hidden(D_228, k10_yellow_6('#skF_5', B_227)) | r2_hidden(D_228, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_228, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_227, '#skF_5') | ~v7_waybel_0(B_227) | ~v4_orders_2(B_227) | v2_struct_0(B_227))), inference(negUnitSimplification, [status(thm)], [c_64, c_314])).
% 2.77/1.45  tff(c_247, plain, (![D_208]: (r2_hidden(D_208, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_208, u1_struct_0('#skF_5')) | ~r1_waybel_0('#skF_5', '#skF_6', '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_208)))), inference(splitRight, [status(thm)], [c_237])).
% 2.77/1.45  tff(c_320, plain, (![D_228]: (~r2_hidden(D_228, k10_yellow_6('#skF_5', '#skF_6')) | r2_hidden(D_228, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_228, u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_316, c_247])).
% 2.77/1.45  tff(c_328, plain, (![D_228]: (~r2_hidden(D_228, k10_yellow_6('#skF_5', '#skF_6')) | r2_hidden(D_228, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_228, u1_struct_0('#skF_5')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_52, c_320])).
% 2.77/1.45  tff(c_335, plain, (![D_229]: (~r2_hidden(D_229, k10_yellow_6('#skF_5', '#skF_6')) | r2_hidden(D_229, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_229, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_58, c_328])).
% 2.77/1.45  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.77/1.45  tff(c_367, plain, (![A_232]: (r1_tarski(A_232, k10_yellow_6('#skF_5', '#skF_7')) | ~r2_hidden('#skF_1'(A_232, k10_yellow_6('#skF_5', '#skF_7')), k10_yellow_6('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'(A_232, k10_yellow_6('#skF_5', '#skF_7')), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_335, c_4])).
% 2.77/1.45  tff(c_375, plain, (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7')), u1_struct_0('#skF_5')) | r1_tarski(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_6, c_367])).
% 2.77/1.45  tff(c_379, plain, (~m1_subset_1('#skF_1'(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7')), u1_struct_0('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_48, c_48, c_375])).
% 2.77/1.45  tff(c_385, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | r1_tarski(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7'))), inference(resolution, [status(thm)], [c_154, c_379])).
% 2.77/1.45  tff(c_390, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | r1_tarski(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_56, c_54, c_52, c_385])).
% 2.77/1.45  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_64, c_58, c_390])).
% 2.77/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.77/1.45  
% 2.77/1.45  Inference rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Ref     : 0
% 2.77/1.45  #Sup     : 52
% 2.77/1.45  #Fact    : 0
% 2.77/1.45  #Define  : 0
% 2.77/1.45  #Split   : 2
% 2.77/1.45  #Chain   : 0
% 2.77/1.45  #Close   : 0
% 2.77/1.45  
% 2.77/1.45  Ordering : KBO
% 2.77/1.45  
% 2.77/1.45  Simplification rules
% 2.77/1.45  ----------------------
% 2.77/1.45  #Subsume      : 8
% 2.77/1.45  #Demod        : 84
% 2.77/1.45  #Tautology    : 9
% 2.77/1.45  #SimpNegUnit  : 25
% 2.77/1.45  #BackRed      : 0
% 2.77/1.45  
% 2.77/1.45  #Partial instantiations: 0
% 2.77/1.45  #Strategies tried      : 1
% 2.77/1.45  
% 2.77/1.45  Timing (in seconds)
% 2.77/1.45  ----------------------
% 2.77/1.46  Preprocessing        : 0.33
% 2.77/1.46  Parsing              : 0.17
% 2.77/1.46  CNF conversion       : 0.03
% 2.77/1.46  Main loop            : 0.32
% 2.77/1.46  Inferencing          : 0.13
% 2.77/1.46  Reduction            : 0.09
% 2.77/1.46  Demodulation         : 0.06
% 2.77/1.46  BG Simplification    : 0.02
% 2.77/1.46  Subsumption          : 0.07
% 2.77/1.46  Abstraction          : 0.01
% 2.77/1.46  MUC search           : 0.00
% 2.77/1.46  Cooper               : 0.00
% 2.77/1.46  Total                : 0.69
% 2.77/1.46  Index Insertion      : 0.00
% 2.77/1.46  Index Deletion       : 0.00
% 2.77/1.46  Index Matching       : 0.00
% 2.77/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
