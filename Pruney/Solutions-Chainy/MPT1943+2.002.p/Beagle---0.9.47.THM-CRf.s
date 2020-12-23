%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:54 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  117 (1345 expanded)
%              Number of leaves         :   36 ( 541 expanded)
%              Depth                    :   37
%              Number of atoms          :  433 (6966 expanded)
%              Number of equality atoms :    1 (   6 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k6_subset_1 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m2_yellow_6,type,(
    m2_yellow_6: ( $i * $i * $i ) > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_182,negated_conjecture,(
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

tff(f_110,axiom,(
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

tff(f_43,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_136,axiom,(
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

tff(f_60,axiom,(
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

tff(f_159,axiom,(
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

tff(f_92,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_60,plain,(
    v2_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_58,plain,(
    l1_pre_topc('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_54,plain,(
    v4_orders_2('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_52,plain,(
    v7_waybel_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_50,plain,(
    l1_waybel_0('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_34,plain,(
    ! [A_100,B_101] :
      ( m1_subset_1(k10_yellow_6(A_100,B_101),k1_zfmisc_1(u1_struct_0(A_100)))
      | ~ l1_waybel_0(B_101,A_100)
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101)
      | ~ l1_pre_topc(A_100)
      | ~ v2_pre_topc(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_46,plain,(
    ~ r1_tarski(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_8,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_48,plain,(
    m2_yellow_6('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_77,plain,(
    ! [C_137,A_138,B_139] :
      ( v7_waybel_0(C_137)
      | ~ m2_yellow_6(C_137,A_138,B_139)
      | ~ l1_waybel_0(B_139,A_138)
      | ~ v7_waybel_0(B_139)
      | ~ v4_orders_2(B_139)
      | v2_struct_0(B_139)
      | ~ l1_struct_0(A_138)
      | v2_struct_0(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_80,plain,
    ( v7_waybel_0('#skF_7')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_77])).

tff(c_83,plain,
    ( v7_waybel_0('#skF_7')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_80])).

tff(c_84,plain,
    ( v7_waybel_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_83])).

tff(c_93,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_96,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_96])).

tff(c_102,plain,(
    l1_struct_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_85,plain,(
    ! [C_140,A_141,B_142] :
      ( ~ v2_struct_0(C_140)
      | ~ m2_yellow_6(C_140,A_141,B_142)
      | ~ l1_waybel_0(B_142,A_141)
      | ~ v7_waybel_0(B_142)
      | ~ v4_orders_2(B_142)
      | v2_struct_0(B_142)
      | ~ l1_struct_0(A_141)
      | v2_struct_0(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_88,plain,
    ( ~ v2_struct_0('#skF_7')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_91,plain,
    ( ~ v2_struct_0('#skF_7')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_88])).

tff(c_92,plain,
    ( ~ v2_struct_0('#skF_7')
    | ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_91])).

tff(c_103,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_103])).

tff(c_106,plain,(
    ~ v2_struct_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_109,plain,(
    ! [C_143,A_144,B_145] :
      ( v4_orders_2(C_143)
      | ~ m2_yellow_6(C_143,A_144,B_145)
      | ~ l1_waybel_0(B_145,A_144)
      | ~ v7_waybel_0(B_145)
      | ~ v4_orders_2(B_145)
      | v2_struct_0(B_145)
      | ~ l1_struct_0(A_144)
      | v2_struct_0(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_112,plain,
    ( v4_orders_2('#skF_7')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_109])).

tff(c_115,plain,
    ( v4_orders_2('#skF_7')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_54,c_52,c_50,c_112])).

tff(c_116,plain,(
    v4_orders_2('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_115])).

tff(c_101,plain,(
    v7_waybel_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_117,plain,(
    ! [C_146,A_147,B_148] :
      ( l1_waybel_0(C_146,A_147)
      | ~ m2_yellow_6(C_146,A_147,B_148)
      | ~ l1_waybel_0(B_148,A_147)
      | ~ v7_waybel_0(B_148)
      | ~ v4_orders_2(B_148)
      | v2_struct_0(B_148)
      | ~ l1_struct_0(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_120,plain,
    ( l1_waybel_0('#skF_7','#skF_5')
    | ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_117])).

tff(c_123,plain,
    ( l1_waybel_0('#skF_7','#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_54,c_52,c_50,c_120])).

tff(c_124,plain,(
    l1_waybel_0('#skF_7','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_123])).

tff(c_12,plain,(
    ! [A_9,B_13,C_15] :
      ( r1_waybel_0(A_9,B_13,C_15)
      | r2_waybel_0(A_9,B_13,k6_subset_1(u1_struct_0(A_9),C_15))
      | ~ l1_waybel_0(B_13,A_9)
      | v2_struct_0(B_13)
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_137,plain,(
    ! [A_162,B_163,D_164,C_165] :
      ( r2_waybel_0(A_162,B_163,D_164)
      | ~ r2_waybel_0(A_162,C_165,D_164)
      | ~ m2_yellow_6(C_165,A_162,B_163)
      | ~ l1_waybel_0(B_163,A_162)
      | ~ v7_waybel_0(B_163)
      | ~ v4_orders_2(B_163)
      | v2_struct_0(B_163)
      | ~ l1_struct_0(A_162)
      | v2_struct_0(A_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_142,plain,(
    ! [A_169,B_170,C_171,B_172] :
      ( r2_waybel_0(A_169,B_170,k6_subset_1(u1_struct_0(A_169),C_171))
      | ~ m2_yellow_6(B_172,A_169,B_170)
      | ~ l1_waybel_0(B_170,A_169)
      | ~ v7_waybel_0(B_170)
      | ~ v4_orders_2(B_170)
      | v2_struct_0(B_170)
      | r1_waybel_0(A_169,B_172,C_171)
      | ~ l1_waybel_0(B_172,A_169)
      | v2_struct_0(B_172)
      | ~ l1_struct_0(A_169)
      | v2_struct_0(A_169) ) ),
    inference(resolution,[status(thm)],[c_12,c_137])).

tff(c_144,plain,(
    ! [C_171] :
      ( r2_waybel_0('#skF_5','#skF_6',k6_subset_1(u1_struct_0('#skF_5'),C_171))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6')
      | r1_waybel_0('#skF_5','#skF_7',C_171)
      | ~ l1_waybel_0('#skF_7','#skF_5')
      | v2_struct_0('#skF_7')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_142])).

tff(c_147,plain,(
    ! [C_171] :
      ( r2_waybel_0('#skF_5','#skF_6',k6_subset_1(u1_struct_0('#skF_5'),C_171))
      | v2_struct_0('#skF_6')
      | r1_waybel_0('#skF_5','#skF_7',C_171)
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_124,c_54,c_52,c_50,c_144])).

tff(c_149,plain,(
    ! [C_173] :
      ( r2_waybel_0('#skF_5','#skF_6',k6_subset_1(u1_struct_0('#skF_5'),C_173))
      | r1_waybel_0('#skF_5','#skF_7',C_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_106,c_56,c_147])).

tff(c_10,plain,(
    ! [A_9,B_13,C_15] :
      ( ~ r2_waybel_0(A_9,B_13,k6_subset_1(u1_struct_0(A_9),C_15))
      | ~ r1_waybel_0(A_9,B_13,C_15)
      | ~ l1_waybel_0(B_13,A_9)
      | v2_struct_0(B_13)
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_154,plain,(
    ! [C_173] :
      ( ~ r1_waybel_0('#skF_5','#skF_6',C_173)
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | v2_struct_0('#skF_6')
      | ~ l1_struct_0('#skF_5')
      | v2_struct_0('#skF_5')
      | r1_waybel_0('#skF_5','#skF_7',C_173) ) ),
    inference(resolution,[status(thm)],[c_149,c_10])).

tff(c_161,plain,(
    ! [C_173] :
      ( ~ r1_waybel_0('#skF_5','#skF_6',C_173)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | r1_waybel_0('#skF_5','#skF_7',C_173) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_50,c_154])).

tff(c_162,plain,(
    ! [C_173] :
      ( ~ r1_waybel_0('#skF_5','#skF_6',C_173)
      | r1_waybel_0('#skF_5','#skF_7',C_173) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_161])).

tff(c_210,plain,(
    ! [A_197,B_198,D_199] :
      ( ~ r1_waybel_0(A_197,B_198,'#skF_2'(A_197,B_198,k10_yellow_6(A_197,B_198),D_199))
      | r2_hidden(D_199,k10_yellow_6(A_197,B_198))
      | ~ m1_subset_1(D_199,u1_struct_0(A_197))
      | ~ m1_subset_1(k10_yellow_6(A_197,B_198),k1_zfmisc_1(u1_struct_0(A_197)))
      | ~ l1_waybel_0(B_198,A_197)
      | ~ v7_waybel_0(B_198)
      | ~ v4_orders_2(B_198)
      | v2_struct_0(B_198)
      | ~ l1_pre_topc(A_197)
      | ~ v2_pre_topc(A_197)
      | v2_struct_0(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_213,plain,(
    ! [D_199] :
      ( r2_hidden(D_199,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_199,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0('#skF_7','#skF_5')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ r1_waybel_0('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_199)) ) ),
    inference(resolution,[status(thm)],[c_162,c_210])).

tff(c_216,plain,(
    ! [D_199] :
      ( r2_hidden(D_199,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_199,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5')
      | ~ r1_waybel_0('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_199)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_116,c_101,c_124,c_213])).

tff(c_217,plain,(
    ! [D_199] :
      ( r2_hidden(D_199,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_199,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ r1_waybel_0('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_199)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_106,c_216])).

tff(c_218,plain,(
    ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_221,plain,
    ( ~ l1_waybel_0('#skF_7','#skF_5')
    | ~ v7_waybel_0('#skF_7')
    | ~ v4_orders_2('#skF_7')
    | v2_struct_0('#skF_7')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_218])).

tff(c_224,plain,
    ( v2_struct_0('#skF_7')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_116,c_101,c_124,c_221])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_106,c_224])).

tff(c_228,plain,(
    m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_6,plain,(
    ! [A_1,B_2,C_6] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_6),A_1)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_1,B_2,C_6] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_6),B_2)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_233,plain,(
    ! [A_201,B_202,D_203] :
      ( m1_connsp_2('#skF_2'(A_201,B_202,k10_yellow_6(A_201,B_202),D_203),A_201,D_203)
      | r2_hidden(D_203,k10_yellow_6(A_201,B_202))
      | ~ m1_subset_1(D_203,u1_struct_0(A_201))
      | ~ m1_subset_1(k10_yellow_6(A_201,B_202),k1_zfmisc_1(u1_struct_0(A_201)))
      | ~ l1_waybel_0(B_202,A_201)
      | ~ v7_waybel_0(B_202)
      | ~ v4_orders_2(B_202)
      | v2_struct_0(B_202)
      | ~ l1_pre_topc(A_201)
      | ~ v2_pre_topc(A_201)
      | v2_struct_0(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_235,plain,(
    ! [D_203] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_203),'#skF_5',D_203)
      | r2_hidden(D_203,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_203,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_7','#skF_5')
      | ~ v7_waybel_0('#skF_7')
      | ~ v4_orders_2('#skF_7')
      | v2_struct_0('#skF_7')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_228,c_233])).

tff(c_240,plain,(
    ! [D_203] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_203),'#skF_5',D_203)
      | r2_hidden(D_203,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_203,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_7')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_116,c_101,c_124,c_235])).

tff(c_243,plain,(
    ! [D_204] :
      ( m1_connsp_2('#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_204),'#skF_5',D_204)
      | r2_hidden(D_204,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_204,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_106,c_240])).

tff(c_28,plain,(
    ! [A_16,B_60,E_96,D_93] :
      ( r1_waybel_0(A_16,B_60,E_96)
      | ~ m1_connsp_2(E_96,A_16,D_93)
      | ~ r2_hidden(D_93,k10_yellow_6(A_16,B_60))
      | ~ m1_subset_1(D_93,u1_struct_0(A_16))
      | ~ m1_subset_1(k10_yellow_6(A_16,B_60),k1_zfmisc_1(u1_struct_0(A_16)))
      | ~ l1_waybel_0(B_60,A_16)
      | ~ v7_waybel_0(B_60)
      | ~ v4_orders_2(B_60)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc(A_16)
      | ~ v2_pre_topc(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_248,plain,(
    ! [B_60,D_204] :
      ( r1_waybel_0('#skF_5',B_60,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_204))
      | ~ r2_hidden(D_204,k10_yellow_6('#skF_5',B_60))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_60),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_60,'#skF_5')
      | ~ v7_waybel_0(B_60)
      | ~ v4_orders_2(B_60)
      | v2_struct_0(B_60)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | r2_hidden(D_204,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_204,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_243,c_28])).

tff(c_255,plain,(
    ! [B_60,D_204] :
      ( r1_waybel_0('#skF_5',B_60,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_204))
      | ~ r2_hidden(D_204,k10_yellow_6('#skF_5',B_60))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_60),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_60,'#skF_5')
      | ~ v7_waybel_0(B_60)
      | ~ v4_orders_2(B_60)
      | v2_struct_0(B_60)
      | v2_struct_0('#skF_5')
      | r2_hidden(D_204,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_204,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_248])).

tff(c_292,plain,(
    ! [B_214,D_215] :
      ( r1_waybel_0('#skF_5',B_214,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_215))
      | ~ r2_hidden(D_215,k10_yellow_6('#skF_5',B_214))
      | ~ m1_subset_1(k10_yellow_6('#skF_5',B_214),k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ l1_waybel_0(B_214,'#skF_5')
      | ~ v7_waybel_0(B_214)
      | ~ v4_orders_2(B_214)
      | v2_struct_0(B_214)
      | r2_hidden(D_215,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_215,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_255])).

tff(c_297,plain,(
    ! [B_101,D_215] :
      ( r1_waybel_0('#skF_5',B_101,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_215))
      | ~ r2_hidden(D_215,k10_yellow_6('#skF_5',B_101))
      | r2_hidden(D_215,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_215,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_101,'#skF_5')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101)
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_292])).

tff(c_304,plain,(
    ! [B_101,D_215] :
      ( r1_waybel_0('#skF_5',B_101,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_215))
      | ~ r2_hidden(D_215,k10_yellow_6('#skF_5',B_101))
      | r2_hidden(D_215,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_215,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_101,'#skF_5')
      | ~ v7_waybel_0(B_101)
      | ~ v4_orders_2(B_101)
      | v2_struct_0(B_101)
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_297])).

tff(c_306,plain,(
    ! [B_216,D_217] :
      ( r1_waybel_0('#skF_5',B_216,'#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_217))
      | ~ r2_hidden(D_217,k10_yellow_6('#skF_5',B_216))
      | r2_hidden(D_217,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_217,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0(B_216,'#skF_5')
      | ~ v7_waybel_0(B_216)
      | ~ v4_orders_2(B_216)
      | v2_struct_0(B_216) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_304])).

tff(c_227,plain,(
    ! [D_199] :
      ( r2_hidden(D_199,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_199,u1_struct_0('#skF_5'))
      | ~ r1_waybel_0('#skF_5','#skF_6','#skF_2'('#skF_5','#skF_7',k10_yellow_6('#skF_5','#skF_7'),D_199)) ) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_310,plain,(
    ! [D_217] :
      ( ~ r2_hidden(D_217,k10_yellow_6('#skF_5','#skF_6'))
      | r2_hidden(D_217,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_217,u1_struct_0('#skF_5'))
      | ~ l1_waybel_0('#skF_6','#skF_5')
      | ~ v7_waybel_0('#skF_6')
      | ~ v4_orders_2('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_306,c_227])).

tff(c_318,plain,(
    ! [D_217] :
      ( ~ r2_hidden(D_217,k10_yellow_6('#skF_5','#skF_6'))
      | r2_hidden(D_217,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_217,u1_struct_0('#skF_5'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_50,c_310])).

tff(c_325,plain,(
    ! [D_218] :
      ( ~ r2_hidden(D_218,k10_yellow_6('#skF_5','#skF_6'))
      | r2_hidden(D_218,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(D_218,u1_struct_0('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_318])).

tff(c_2,plain,(
    ! [A_1,B_2,C_6] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_6),C_6)
      | r1_tarski(B_2,C_6)
      | ~ m1_subset_1(C_6,k1_zfmisc_1(A_1))
      | ~ m1_subset_1(B_2,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_338,plain,(
    ! [B_219,A_220] :
      ( r1_tarski(B_219,k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(A_220))
      | ~ m1_subset_1(B_219,k1_zfmisc_1(A_220))
      | ~ r2_hidden('#skF_1'(A_220,B_219,k10_yellow_6('#skF_5','#skF_7')),k10_yellow_6('#skF_5','#skF_6'))
      | ~ m1_subset_1('#skF_1'(A_220,B_219,k10_yellow_6('#skF_5','#skF_7')),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_325,c_2])).

tff(c_342,plain,(
    ! [A_1] :
      ( ~ m1_subset_1('#skF_1'(A_1,k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')),u1_struct_0('#skF_5'))
      | r1_tarski(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(A_1))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_6'),k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_4,c_338])).

tff(c_346,plain,(
    ! [A_221] :
      ( ~ m1_subset_1('#skF_1'(A_221,k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7')),u1_struct_0('#skF_5'))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(A_221))
      | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_6'),k1_zfmisc_1(A_221)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_342])).

tff(c_350,plain,
    ( r1_tarski(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7'))
    | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_7'),k1_zfmisc_1(u1_struct_0('#skF_5')))
    | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_6,c_346])).

tff(c_353,plain,
    ( r1_tarski(k10_yellow_6('#skF_5','#skF_6'),k10_yellow_6('#skF_5','#skF_7'))
    | ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_350])).

tff(c_354,plain,(
    ~ m1_subset_1(k10_yellow_6('#skF_5','#skF_6'),k1_zfmisc_1(u1_struct_0('#skF_5'))) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_353])).

tff(c_357,plain,
    ( ~ l1_waybel_0('#skF_6','#skF_5')
    | ~ v7_waybel_0('#skF_6')
    | ~ v4_orders_2('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_354])).

tff(c_360,plain,
    ( v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_54,c_52,c_50,c_357])).

tff(c_362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_56,c_360])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.39  
% 2.98/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.39  %$ r2_waybel_0 > r1_waybel_0 > m2_yellow_6 > m1_connsp_2 > r2_hidden > r1_tarski > m1_subset_1 > l1_waybel_0 > v7_waybel_0 > v4_orders_2 > v2_struct_0 > v2_pre_topc > l1_struct_0 > l1_pre_topc > k6_subset_1 > k10_yellow_6 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3
% 2.98/1.39  
% 2.98/1.39  %Foreground sorts:
% 2.98/1.39  
% 2.98/1.39  
% 2.98/1.39  %Background operators:
% 2.98/1.39  
% 2.98/1.39  
% 2.98/1.39  %Foreground operators:
% 2.98/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.98/1.39  tff(m2_yellow_6, type, m2_yellow_6: ($i * $i * $i) > $o).
% 2.98/1.39  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 2.98/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.98/1.39  tff(r2_waybel_0, type, r2_waybel_0: ($i * $i * $i) > $o).
% 2.98/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.39  tff(k10_yellow_6, type, k10_yellow_6: ($i * $i) > $i).
% 2.98/1.39  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.98/1.39  tff(v7_waybel_0, type, v7_waybel_0: $i > $o).
% 2.98/1.39  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.98/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.98/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.39  tff(r1_waybel_0, type, r1_waybel_0: ($i * $i * $i) > $o).
% 2.98/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.98/1.39  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.39  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.98/1.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.98/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.98/1.39  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.98/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.39  tff(l1_waybel_0, type, l1_waybel_0: ($i * $i) > $o).
% 2.98/1.39  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.98/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.39  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.98/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.98/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.98/1.39  
% 2.98/1.42  tff(f_182, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => r1_tarski(k10_yellow_6(A, B), k10_yellow_6(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_yellow_6)).
% 2.98/1.42  tff(f_110, axiom, (![A, B]: (((((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => m1_subset_1(k10_yellow_6(A, B), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_yellow_6)).
% 2.98/1.42  tff(f_43, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.98/1.42  tff(f_136, axiom, (![A, B]: ((((((~v2_struct_0(A) & l1_struct_0(A)) & ~v2_struct_0(B)) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (((~v2_struct_0(C) & v4_orders_2(C)) & v7_waybel_0(C)) & l1_waybel_0(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m2_yellow_6)).
% 2.98/1.42  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((~v2_struct_0(B) & l1_waybel_0(B, A)) => (![C]: (r1_waybel_0(A, B, C) <=> ~r2_waybel_0(A, B, k6_subset_1(u1_struct_0(A), C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_waybel_0)).
% 2.98/1.42  tff(f_159, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m2_yellow_6(C, A, B) => (![D]: (r2_waybel_0(A, C, D) => r2_waybel_0(A, B, D))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_yellow_6)).
% 2.98/1.42  tff(f_92, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((((~v2_struct_0(B) & v4_orders_2(B)) & v7_waybel_0(B)) & l1_waybel_0(B, A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = k10_yellow_6(A, B)) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, C) <=> (![E]: (m1_connsp_2(E, A, D) => r1_waybel_0(A, B, E))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_yellow_6)).
% 2.98/1.42  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 2.98/1.42  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_56, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_60, plain, (v2_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_58, plain, (l1_pre_topc('#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_54, plain, (v4_orders_2('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_52, plain, (v7_waybel_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_50, plain, (l1_waybel_0('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_34, plain, (![A_100, B_101]: (m1_subset_1(k10_yellow_6(A_100, B_101), k1_zfmisc_1(u1_struct_0(A_100))) | ~l1_waybel_0(B_101, A_100) | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | ~l1_pre_topc(A_100) | ~v2_pre_topc(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.98/1.42  tff(c_46, plain, (~r1_tarski(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_8, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.98/1.42  tff(c_48, plain, (m2_yellow_6('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_182])).
% 2.98/1.42  tff(c_77, plain, (![C_137, A_138, B_139]: (v7_waybel_0(C_137) | ~m2_yellow_6(C_137, A_138, B_139) | ~l1_waybel_0(B_139, A_138) | ~v7_waybel_0(B_139) | ~v4_orders_2(B_139) | v2_struct_0(B_139) | ~l1_struct_0(A_138) | v2_struct_0(A_138))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.98/1.42  tff(c_80, plain, (v7_waybel_0('#skF_7') | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_77])).
% 2.98/1.42  tff(c_83, plain, (v7_waybel_0('#skF_7') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_80])).
% 2.98/1.42  tff(c_84, plain, (v7_waybel_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_83])).
% 2.98/1.42  tff(c_93, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_84])).
% 2.98/1.42  tff(c_96, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_8, c_93])).
% 2.98/1.42  tff(c_100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_96])).
% 2.98/1.42  tff(c_102, plain, (l1_struct_0('#skF_5')), inference(splitRight, [status(thm)], [c_84])).
% 2.98/1.42  tff(c_85, plain, (![C_140, A_141, B_142]: (~v2_struct_0(C_140) | ~m2_yellow_6(C_140, A_141, B_142) | ~l1_waybel_0(B_142, A_141) | ~v7_waybel_0(B_142) | ~v4_orders_2(B_142) | v2_struct_0(B_142) | ~l1_struct_0(A_141) | v2_struct_0(A_141))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.98/1.42  tff(c_88, plain, (~v2_struct_0('#skF_7') | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_85])).
% 2.98/1.42  tff(c_91, plain, (~v2_struct_0('#skF_7') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_88])).
% 2.98/1.42  tff(c_92, plain, (~v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_91])).
% 2.98/1.42  tff(c_103, plain, (~l1_struct_0('#skF_5')), inference(splitLeft, [status(thm)], [c_92])).
% 2.98/1.42  tff(c_105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_103])).
% 2.98/1.42  tff(c_106, plain, (~v2_struct_0('#skF_7')), inference(splitRight, [status(thm)], [c_92])).
% 2.98/1.42  tff(c_109, plain, (![C_143, A_144, B_145]: (v4_orders_2(C_143) | ~m2_yellow_6(C_143, A_144, B_145) | ~l1_waybel_0(B_145, A_144) | ~v7_waybel_0(B_145) | ~v4_orders_2(B_145) | v2_struct_0(B_145) | ~l1_struct_0(A_144) | v2_struct_0(A_144))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.98/1.42  tff(c_112, plain, (v4_orders_2('#skF_7') | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_109])).
% 2.98/1.42  tff(c_115, plain, (v4_orders_2('#skF_7') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_54, c_52, c_50, c_112])).
% 2.98/1.42  tff(c_116, plain, (v4_orders_2('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_115])).
% 2.98/1.42  tff(c_101, plain, (v7_waybel_0('#skF_7')), inference(splitRight, [status(thm)], [c_84])).
% 2.98/1.42  tff(c_117, plain, (![C_146, A_147, B_148]: (l1_waybel_0(C_146, A_147) | ~m2_yellow_6(C_146, A_147, B_148) | ~l1_waybel_0(B_148, A_147) | ~v7_waybel_0(B_148) | ~v4_orders_2(B_148) | v2_struct_0(B_148) | ~l1_struct_0(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.98/1.42  tff(c_120, plain, (l1_waybel_0('#skF_7', '#skF_5') | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_117])).
% 2.98/1.42  tff(c_123, plain, (l1_waybel_0('#skF_7', '#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_54, c_52, c_50, c_120])).
% 2.98/1.42  tff(c_124, plain, (l1_waybel_0('#skF_7', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_123])).
% 2.98/1.42  tff(c_12, plain, (![A_9, B_13, C_15]: (r1_waybel_0(A_9, B_13, C_15) | r2_waybel_0(A_9, B_13, k6_subset_1(u1_struct_0(A_9), C_15)) | ~l1_waybel_0(B_13, A_9) | v2_struct_0(B_13) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.98/1.42  tff(c_137, plain, (![A_162, B_163, D_164, C_165]: (r2_waybel_0(A_162, B_163, D_164) | ~r2_waybel_0(A_162, C_165, D_164) | ~m2_yellow_6(C_165, A_162, B_163) | ~l1_waybel_0(B_163, A_162) | ~v7_waybel_0(B_163) | ~v4_orders_2(B_163) | v2_struct_0(B_163) | ~l1_struct_0(A_162) | v2_struct_0(A_162))), inference(cnfTransformation, [status(thm)], [f_159])).
% 2.98/1.42  tff(c_142, plain, (![A_169, B_170, C_171, B_172]: (r2_waybel_0(A_169, B_170, k6_subset_1(u1_struct_0(A_169), C_171)) | ~m2_yellow_6(B_172, A_169, B_170) | ~l1_waybel_0(B_170, A_169) | ~v7_waybel_0(B_170) | ~v4_orders_2(B_170) | v2_struct_0(B_170) | r1_waybel_0(A_169, B_172, C_171) | ~l1_waybel_0(B_172, A_169) | v2_struct_0(B_172) | ~l1_struct_0(A_169) | v2_struct_0(A_169))), inference(resolution, [status(thm)], [c_12, c_137])).
% 2.98/1.42  tff(c_144, plain, (![C_171]: (r2_waybel_0('#skF_5', '#skF_6', k6_subset_1(u1_struct_0('#skF_5'), C_171)) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | r1_waybel_0('#skF_5', '#skF_7', C_171) | ~l1_waybel_0('#skF_7', '#skF_5') | v2_struct_0('#skF_7') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_48, c_142])).
% 2.98/1.42  tff(c_147, plain, (![C_171]: (r2_waybel_0('#skF_5', '#skF_6', k6_subset_1(u1_struct_0('#skF_5'), C_171)) | v2_struct_0('#skF_6') | r1_waybel_0('#skF_5', '#skF_7', C_171) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_124, c_54, c_52, c_50, c_144])).
% 2.98/1.42  tff(c_149, plain, (![C_173]: (r2_waybel_0('#skF_5', '#skF_6', k6_subset_1(u1_struct_0('#skF_5'), C_173)) | r1_waybel_0('#skF_5', '#skF_7', C_173))), inference(negUnitSimplification, [status(thm)], [c_62, c_106, c_56, c_147])).
% 2.98/1.42  tff(c_10, plain, (![A_9, B_13, C_15]: (~r2_waybel_0(A_9, B_13, k6_subset_1(u1_struct_0(A_9), C_15)) | ~r1_waybel_0(A_9, B_13, C_15) | ~l1_waybel_0(B_13, A_9) | v2_struct_0(B_13) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.98/1.42  tff(c_154, plain, (![C_173]: (~r1_waybel_0('#skF_5', '#skF_6', C_173) | ~l1_waybel_0('#skF_6', '#skF_5') | v2_struct_0('#skF_6') | ~l1_struct_0('#skF_5') | v2_struct_0('#skF_5') | r1_waybel_0('#skF_5', '#skF_7', C_173))), inference(resolution, [status(thm)], [c_149, c_10])).
% 2.98/1.42  tff(c_161, plain, (![C_173]: (~r1_waybel_0('#skF_5', '#skF_6', C_173) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | r1_waybel_0('#skF_5', '#skF_7', C_173))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_50, c_154])).
% 2.98/1.42  tff(c_162, plain, (![C_173]: (~r1_waybel_0('#skF_5', '#skF_6', C_173) | r1_waybel_0('#skF_5', '#skF_7', C_173))), inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_161])).
% 2.98/1.42  tff(c_210, plain, (![A_197, B_198, D_199]: (~r1_waybel_0(A_197, B_198, '#skF_2'(A_197, B_198, k10_yellow_6(A_197, B_198), D_199)) | r2_hidden(D_199, k10_yellow_6(A_197, B_198)) | ~m1_subset_1(D_199, u1_struct_0(A_197)) | ~m1_subset_1(k10_yellow_6(A_197, B_198), k1_zfmisc_1(u1_struct_0(A_197))) | ~l1_waybel_0(B_198, A_197) | ~v7_waybel_0(B_198) | ~v4_orders_2(B_198) | v2_struct_0(B_198) | ~l1_pre_topc(A_197) | ~v2_pre_topc(A_197) | v2_struct_0(A_197))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.98/1.42  tff(c_213, plain, (![D_199]: (r2_hidden(D_199, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_199, u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~r1_waybel_0('#skF_5', '#skF_6', '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_199)))), inference(resolution, [status(thm)], [c_162, c_210])).
% 2.98/1.42  tff(c_216, plain, (![D_199]: (r2_hidden(D_199, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_199, u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5') | ~r1_waybel_0('#skF_5', '#skF_6', '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_199)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_116, c_101, c_124, c_213])).
% 2.98/1.42  tff(c_217, plain, (![D_199]: (r2_hidden(D_199, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_199, u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~r1_waybel_0('#skF_5', '#skF_6', '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_199)))), inference(negUnitSimplification, [status(thm)], [c_62, c_106, c_216])).
% 2.98/1.42  tff(c_218, plain, (~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitLeft, [status(thm)], [c_217])).
% 2.98/1.42  tff(c_221, plain, (~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_218])).
% 2.98/1.42  tff(c_224, plain, (v2_struct_0('#skF_7') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_116, c_101, c_124, c_221])).
% 2.98/1.42  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_106, c_224])).
% 2.98/1.42  tff(c_228, plain, (m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(splitRight, [status(thm)], [c_217])).
% 2.98/1.42  tff(c_6, plain, (![A_1, B_2, C_6]: (m1_subset_1('#skF_1'(A_1, B_2, C_6), A_1) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.42  tff(c_4, plain, (![A_1, B_2, C_6]: (r2_hidden('#skF_1'(A_1, B_2, C_6), B_2) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.42  tff(c_233, plain, (![A_201, B_202, D_203]: (m1_connsp_2('#skF_2'(A_201, B_202, k10_yellow_6(A_201, B_202), D_203), A_201, D_203) | r2_hidden(D_203, k10_yellow_6(A_201, B_202)) | ~m1_subset_1(D_203, u1_struct_0(A_201)) | ~m1_subset_1(k10_yellow_6(A_201, B_202), k1_zfmisc_1(u1_struct_0(A_201))) | ~l1_waybel_0(B_202, A_201) | ~v7_waybel_0(B_202) | ~v4_orders_2(B_202) | v2_struct_0(B_202) | ~l1_pre_topc(A_201) | ~v2_pre_topc(A_201) | v2_struct_0(A_201))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.98/1.42  tff(c_235, plain, (![D_203]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_203), '#skF_5', D_203) | r2_hidden(D_203, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_203, u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_7', '#skF_5') | ~v7_waybel_0('#skF_7') | ~v4_orders_2('#skF_7') | v2_struct_0('#skF_7') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_228, c_233])).
% 2.98/1.42  tff(c_240, plain, (![D_203]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_203), '#skF_5', D_203) | r2_hidden(D_203, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_203, u1_struct_0('#skF_5')) | v2_struct_0('#skF_7') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_116, c_101, c_124, c_235])).
% 2.98/1.42  tff(c_243, plain, (![D_204]: (m1_connsp_2('#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_204), '#skF_5', D_204) | r2_hidden(D_204, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_204, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_106, c_240])).
% 2.98/1.42  tff(c_28, plain, (![A_16, B_60, E_96, D_93]: (r1_waybel_0(A_16, B_60, E_96) | ~m1_connsp_2(E_96, A_16, D_93) | ~r2_hidden(D_93, k10_yellow_6(A_16, B_60)) | ~m1_subset_1(D_93, u1_struct_0(A_16)) | ~m1_subset_1(k10_yellow_6(A_16, B_60), k1_zfmisc_1(u1_struct_0(A_16))) | ~l1_waybel_0(B_60, A_16) | ~v7_waybel_0(B_60) | ~v4_orders_2(B_60) | v2_struct_0(B_60) | ~l1_pre_topc(A_16) | ~v2_pre_topc(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.98/1.42  tff(c_248, plain, (![B_60, D_204]: (r1_waybel_0('#skF_5', B_60, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_204)) | ~r2_hidden(D_204, k10_yellow_6('#skF_5', B_60)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_60), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_60, '#skF_5') | ~v7_waybel_0(B_60) | ~v4_orders_2(B_60) | v2_struct_0(B_60) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | r2_hidden(D_204, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_204, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_243, c_28])).
% 2.98/1.42  tff(c_255, plain, (![B_60, D_204]: (r1_waybel_0('#skF_5', B_60, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_204)) | ~r2_hidden(D_204, k10_yellow_6('#skF_5', B_60)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_60), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_60, '#skF_5') | ~v7_waybel_0(B_60) | ~v4_orders_2(B_60) | v2_struct_0(B_60) | v2_struct_0('#skF_5') | r2_hidden(D_204, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_204, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_248])).
% 2.98/1.42  tff(c_292, plain, (![B_214, D_215]: (r1_waybel_0('#skF_5', B_214, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_215)) | ~r2_hidden(D_215, k10_yellow_6('#skF_5', B_214)) | ~m1_subset_1(k10_yellow_6('#skF_5', B_214), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~l1_waybel_0(B_214, '#skF_5') | ~v7_waybel_0(B_214) | ~v4_orders_2(B_214) | v2_struct_0(B_214) | r2_hidden(D_215, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_215, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_62, c_255])).
% 2.98/1.42  tff(c_297, plain, (![B_101, D_215]: (r1_waybel_0('#skF_5', B_101, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_215)) | ~r2_hidden(D_215, k10_yellow_6('#skF_5', B_101)) | r2_hidden(D_215, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_215, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_101, '#skF_5') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_292])).
% 2.98/1.42  tff(c_304, plain, (![B_101, D_215]: (r1_waybel_0('#skF_5', B_101, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_215)) | ~r2_hidden(D_215, k10_yellow_6('#skF_5', B_101)) | r2_hidden(D_215, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_215, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_101, '#skF_5') | ~v7_waybel_0(B_101) | ~v4_orders_2(B_101) | v2_struct_0(B_101) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_297])).
% 2.98/1.42  tff(c_306, plain, (![B_216, D_217]: (r1_waybel_0('#skF_5', B_216, '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_217)) | ~r2_hidden(D_217, k10_yellow_6('#skF_5', B_216)) | r2_hidden(D_217, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_217, u1_struct_0('#skF_5')) | ~l1_waybel_0(B_216, '#skF_5') | ~v7_waybel_0(B_216) | ~v4_orders_2(B_216) | v2_struct_0(B_216))), inference(negUnitSimplification, [status(thm)], [c_62, c_304])).
% 2.98/1.42  tff(c_227, plain, (![D_199]: (r2_hidden(D_199, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_199, u1_struct_0('#skF_5')) | ~r1_waybel_0('#skF_5', '#skF_6', '#skF_2'('#skF_5', '#skF_7', k10_yellow_6('#skF_5', '#skF_7'), D_199)))), inference(splitRight, [status(thm)], [c_217])).
% 2.98/1.42  tff(c_310, plain, (![D_217]: (~r2_hidden(D_217, k10_yellow_6('#skF_5', '#skF_6')) | r2_hidden(D_217, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_217, u1_struct_0('#skF_5')) | ~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_306, c_227])).
% 2.98/1.42  tff(c_318, plain, (![D_217]: (~r2_hidden(D_217, k10_yellow_6('#skF_5', '#skF_6')) | r2_hidden(D_217, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_217, u1_struct_0('#skF_5')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_50, c_310])).
% 2.98/1.42  tff(c_325, plain, (![D_218]: (~r2_hidden(D_218, k10_yellow_6('#skF_5', '#skF_6')) | r2_hidden(D_218, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(D_218, u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_56, c_318])).
% 2.98/1.42  tff(c_2, plain, (![A_1, B_2, C_6]: (~r2_hidden('#skF_1'(A_1, B_2, C_6), C_6) | r1_tarski(B_2, C_6) | ~m1_subset_1(C_6, k1_zfmisc_1(A_1)) | ~m1_subset_1(B_2, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.98/1.42  tff(c_338, plain, (![B_219, A_220]: (r1_tarski(B_219, k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(A_220)) | ~m1_subset_1(B_219, k1_zfmisc_1(A_220)) | ~r2_hidden('#skF_1'(A_220, B_219, k10_yellow_6('#skF_5', '#skF_7')), k10_yellow_6('#skF_5', '#skF_6')) | ~m1_subset_1('#skF_1'(A_220, B_219, k10_yellow_6('#skF_5', '#skF_7')), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_325, c_2])).
% 2.98/1.42  tff(c_342, plain, (![A_1]: (~m1_subset_1('#skF_1'(A_1, k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7')), u1_struct_0('#skF_5')) | r1_tarski(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(A_1)) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_6'), k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_4, c_338])).
% 2.98/1.42  tff(c_346, plain, (![A_221]: (~m1_subset_1('#skF_1'(A_221, k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7')), u1_struct_0('#skF_5')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(A_221)) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_6'), k1_zfmisc_1(A_221)))), inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_342])).
% 2.98/1.42  tff(c_350, plain, (r1_tarski(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_7'), k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_346])).
% 2.98/1.42  tff(c_353, plain, (r1_tarski(k10_yellow_6('#skF_5', '#skF_6'), k10_yellow_6('#skF_5', '#skF_7')) | ~m1_subset_1(k10_yellow_6('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_228, c_350])).
% 2.98/1.42  tff(c_354, plain, (~m1_subset_1(k10_yellow_6('#skF_5', '#skF_6'), k1_zfmisc_1(u1_struct_0('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_46, c_353])).
% 2.98/1.42  tff(c_357, plain, (~l1_waybel_0('#skF_6', '#skF_5') | ~v7_waybel_0('#skF_6') | ~v4_orders_2('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_34, c_354])).
% 2.98/1.42  tff(c_360, plain, (v2_struct_0('#skF_6') | v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_54, c_52, c_50, c_357])).
% 2.98/1.42  tff(c_362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_56, c_360])).
% 2.98/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.42  
% 2.98/1.42  Inference rules
% 2.98/1.42  ----------------------
% 2.98/1.42  #Ref     : 0
% 2.98/1.42  #Sup     : 43
% 2.98/1.42  #Fact    : 0
% 2.98/1.42  #Define  : 0
% 2.98/1.42  #Split   : 3
% 2.98/1.42  #Chain   : 0
% 2.98/1.42  #Close   : 0
% 2.98/1.42  
% 2.98/1.42  Ordering : KBO
% 2.98/1.42  
% 2.98/1.42  Simplification rules
% 2.98/1.42  ----------------------
% 2.98/1.42  #Subsume      : 5
% 2.98/1.42  #Demod        : 93
% 2.98/1.42  #Tautology    : 7
% 2.98/1.42  #SimpNegUnit  : 27
% 2.98/1.42  #BackRed      : 0
% 2.98/1.42  
% 2.98/1.42  #Partial instantiations: 0
% 2.98/1.42  #Strategies tried      : 1
% 2.98/1.42  
% 2.98/1.42  Timing (in seconds)
% 2.98/1.42  ----------------------
% 2.98/1.42  Preprocessing        : 0.34
% 2.98/1.42  Parsing              : 0.18
% 2.98/1.42  CNF conversion       : 0.03
% 2.98/1.42  Main loop            : 0.31
% 2.98/1.42  Inferencing          : 0.12
% 2.98/1.42  Reduction            : 0.09
% 2.98/1.42  Demodulation         : 0.06
% 2.98/1.42  BG Simplification    : 0.02
% 2.98/1.42  Subsumption          : 0.06
% 2.98/1.42  Abstraction          : 0.01
% 2.98/1.42  MUC search           : 0.00
% 2.98/1.42  Cooper               : 0.00
% 2.98/1.42  Total                : 0.69
% 2.98/1.42  Index Insertion      : 0.00
% 2.98/1.42  Index Deletion       : 0.00
% 2.98/1.42  Index Matching       : 0.00
% 2.98/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
