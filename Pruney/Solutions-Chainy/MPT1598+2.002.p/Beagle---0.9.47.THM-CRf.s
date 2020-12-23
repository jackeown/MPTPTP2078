%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:21 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 183 expanded)
%              Number of leaves         :   35 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  254 ( 482 expanded)
%              Number of equality atoms :    4 (  68 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k10_lattice3,type,(
    k10_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_lattice3,type,(
    v1_lattice3: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_137,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v1_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k2_xboole_0(B,C),k10_lattice3(k2_yellow_1(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

tff(f_110,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k10_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_123,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v1_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

tff(c_28,plain,(
    ! [A_57] : l1_orders_2(k2_yellow_1(A_57)) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_52,plain,(
    v1_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_38,plain,(
    ! [A_59] : u1_struct_0(k2_yellow_1(A_59)) = A_59 ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_55,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_56,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_48])).

tff(c_219,plain,(
    ! [A_149,B_150,C_151] :
      ( m1_subset_1(k10_lattice3(A_149,B_150,C_151),u1_struct_0(A_149))
      | ~ m1_subset_1(C_151,u1_struct_0(A_149))
      | ~ m1_subset_1(B_150,u1_struct_0(A_149))
      | ~ l1_orders_2(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_222,plain,(
    ! [A_59,B_150,C_151] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(A_59),B_150,C_151),A_59)
      | ~ m1_subset_1(C_151,u1_struct_0(k2_yellow_1(A_59)))
      | ~ m1_subset_1(B_150,u1_struct_0(k2_yellow_1(A_59)))
      | ~ l1_orders_2(k2_yellow_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_219])).

tff(c_224,plain,(
    ! [A_59,B_150,C_151] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(A_59),B_150,C_151),A_59)
      | ~ m1_subset_1(C_151,A_59)
      | ~ m1_subset_1(B_150,A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38,c_38,c_222])).

tff(c_36,plain,(
    ! [A_58] : v5_orders_2(k2_yellow_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_10,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k10_lattice3(A_8,B_9,C_10),u1_struct_0(A_8))
      | ~ m1_subset_1(C_10,u1_struct_0(A_8))
      | ~ m1_subset_1(B_9,u1_struct_0(A_8))
      | ~ l1_orders_2(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_260,plain,(
    ! [A_170,C_171,B_172] :
      ( r1_orders_2(A_170,C_171,k10_lattice3(A_170,B_172,C_171))
      | ~ m1_subset_1(k10_lattice3(A_170,B_172,C_171),u1_struct_0(A_170))
      | ~ m1_subset_1(C_171,u1_struct_0(A_170))
      | ~ m1_subset_1(B_172,u1_struct_0(A_170))
      | ~ l1_orders_2(A_170)
      | ~ v1_lattice3(A_170)
      | ~ v5_orders_2(A_170)
      | v2_struct_0(A_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_268,plain,(
    ! [A_173,C_174,B_175] :
      ( r1_orders_2(A_173,C_174,k10_lattice3(A_173,B_175,C_174))
      | ~ v1_lattice3(A_173)
      | ~ v5_orders_2(A_173)
      | v2_struct_0(A_173)
      | ~ m1_subset_1(C_174,u1_struct_0(A_173))
      | ~ m1_subset_1(B_175,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173) ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_32,plain,(
    ! [A_58] : v3_orders_2(k2_yellow_1(A_58)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_226,plain,(
    ! [A_155,B_156,C_157] :
      ( r3_orders_2(A_155,B_156,C_157)
      | ~ r1_orders_2(A_155,B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_233,plain,(
    ! [A_59,B_156,C_157] :
      ( r3_orders_2(k2_yellow_1(A_59),B_156,C_157)
      | ~ r1_orders_2(k2_yellow_1(A_59),B_156,C_157)
      | ~ m1_subset_1(C_157,A_59)
      | ~ m1_subset_1(B_156,u1_struct_0(k2_yellow_1(A_59)))
      | ~ l1_orders_2(k2_yellow_1(A_59))
      | ~ v3_orders_2(k2_yellow_1(A_59))
      | v2_struct_0(k2_yellow_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_226])).

tff(c_244,plain,(
    ! [A_161,B_162,C_163] :
      ( r3_orders_2(k2_yellow_1(A_161),B_162,C_163)
      | ~ r1_orders_2(k2_yellow_1(A_161),B_162,C_163)
      | ~ m1_subset_1(C_163,A_161)
      | ~ m1_subset_1(B_162,A_161)
      | v2_struct_0(k2_yellow_1(A_161)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_38,c_233])).

tff(c_44,plain,(
    ! [B_64,C_66,A_60] :
      ( r1_tarski(B_64,C_66)
      | ~ r3_orders_2(k2_yellow_1(A_60),B_64,C_66)
      | ~ m1_subset_1(C_66,u1_struct_0(k2_yellow_1(A_60)))
      | ~ m1_subset_1(B_64,u1_struct_0(k2_yellow_1(A_60)))
      | v1_xboole_0(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_57,plain,(
    ! [B_64,C_66,A_60] :
      ( r1_tarski(B_64,C_66)
      | ~ r3_orders_2(k2_yellow_1(A_60),B_64,C_66)
      | ~ m1_subset_1(C_66,A_60)
      | ~ m1_subset_1(B_64,A_60)
      | v1_xboole_0(A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_44])).

tff(c_253,plain,(
    ! [B_162,C_163,A_161] :
      ( r1_tarski(B_162,C_163)
      | v1_xboole_0(A_161)
      | ~ r1_orders_2(k2_yellow_1(A_161),B_162,C_163)
      | ~ m1_subset_1(C_163,A_161)
      | ~ m1_subset_1(B_162,A_161)
      | v2_struct_0(k2_yellow_1(A_161)) ) ),
    inference(resolution,[status(thm)],[c_244,c_57])).

tff(c_272,plain,(
    ! [C_174,A_161,B_175] :
      ( r1_tarski(C_174,k10_lattice3(k2_yellow_1(A_161),B_175,C_174))
      | v1_xboole_0(A_161)
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(A_161),B_175,C_174),A_161)
      | ~ m1_subset_1(C_174,A_161)
      | ~ v1_lattice3(k2_yellow_1(A_161))
      | ~ v5_orders_2(k2_yellow_1(A_161))
      | v2_struct_0(k2_yellow_1(A_161))
      | ~ m1_subset_1(C_174,u1_struct_0(k2_yellow_1(A_161)))
      | ~ m1_subset_1(B_175,u1_struct_0(k2_yellow_1(A_161)))
      | ~ l1_orders_2(k2_yellow_1(A_161)) ) ),
    inference(resolution,[status(thm)],[c_268,c_253])).

tff(c_281,plain,(
    ! [C_179,A_180,B_181] :
      ( r1_tarski(C_179,k10_lattice3(k2_yellow_1(A_180),B_181,C_179))
      | v1_xboole_0(A_180)
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(A_180),B_181,C_179),A_180)
      | ~ v1_lattice3(k2_yellow_1(A_180))
      | v2_struct_0(k2_yellow_1(A_180))
      | ~ m1_subset_1(C_179,A_180)
      | ~ m1_subset_1(B_181,A_180) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38,c_38,c_36,c_272])).

tff(c_285,plain,(
    ! [C_182,A_183,B_184] :
      ( r1_tarski(C_182,k10_lattice3(k2_yellow_1(A_183),B_184,C_182))
      | v1_xboole_0(A_183)
      | ~ v1_lattice3(k2_yellow_1(A_183))
      | v2_struct_0(k2_yellow_1(A_183))
      | ~ m1_subset_1(C_182,A_183)
      | ~ m1_subset_1(B_184,A_183) ) ),
    inference(resolution,[status(thm)],[c_224,c_281])).

tff(c_96,plain,(
    ! [A_88,B_89,C_90] :
      ( m1_subset_1(k10_lattice3(A_88,B_89,C_90),u1_struct_0(A_88))
      | ~ m1_subset_1(C_90,u1_struct_0(A_88))
      | ~ m1_subset_1(B_89,u1_struct_0(A_88))
      | ~ l1_orders_2(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_99,plain,(
    ! [A_59,B_89,C_90] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(A_59),B_89,C_90),A_59)
      | ~ m1_subset_1(C_90,u1_struct_0(k2_yellow_1(A_59)))
      | ~ m1_subset_1(B_89,u1_struct_0(k2_yellow_1(A_59)))
      | ~ l1_orders_2(k2_yellow_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_96])).

tff(c_101,plain,(
    ! [A_59,B_89,C_90] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(A_59),B_89,C_90),A_59)
      | ~ m1_subset_1(C_90,A_59)
      | ~ m1_subset_1(B_89,A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38,c_38,c_99])).

tff(c_162,plain,(
    ! [A_121,B_122,C_123] :
      ( r1_orders_2(A_121,B_122,k10_lattice3(A_121,B_122,C_123))
      | ~ m1_subset_1(k10_lattice3(A_121,B_122,C_123),u1_struct_0(A_121))
      | ~ m1_subset_1(C_123,u1_struct_0(A_121))
      | ~ m1_subset_1(B_122,u1_struct_0(A_121))
      | ~ l1_orders_2(A_121)
      | ~ v1_lattice3(A_121)
      | ~ v5_orders_2(A_121)
      | v2_struct_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_171,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_orders_2(A_127,B_128,k10_lattice3(A_127,B_128,C_129))
      | ~ v1_lattice3(A_127)
      | ~ v5_orders_2(A_127)
      | v2_struct_0(A_127)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127) ) ),
    inference(resolution,[status(thm)],[c_10,c_162])).

tff(c_102,plain,(
    ! [A_91,B_92,C_93] :
      ( r3_orders_2(A_91,B_92,C_93)
      | ~ r1_orders_2(A_91,B_92,C_93)
      | ~ m1_subset_1(C_93,u1_struct_0(A_91))
      | ~ m1_subset_1(B_92,u1_struct_0(A_91))
      | ~ l1_orders_2(A_91)
      | ~ v3_orders_2(A_91)
      | v2_struct_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_106,plain,(
    ! [A_59,B_92,C_93] :
      ( r3_orders_2(k2_yellow_1(A_59),B_92,C_93)
      | ~ r1_orders_2(k2_yellow_1(A_59),B_92,C_93)
      | ~ m1_subset_1(C_93,A_59)
      | ~ m1_subset_1(B_92,u1_struct_0(k2_yellow_1(A_59)))
      | ~ l1_orders_2(k2_yellow_1(A_59))
      | ~ v3_orders_2(k2_yellow_1(A_59))
      | v2_struct_0(k2_yellow_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_102])).

tff(c_115,plain,(
    ! [A_97,B_98,C_99] :
      ( r3_orders_2(k2_yellow_1(A_97),B_98,C_99)
      | ~ r1_orders_2(k2_yellow_1(A_97),B_98,C_99)
      | ~ m1_subset_1(C_99,A_97)
      | ~ m1_subset_1(B_98,A_97)
      | v2_struct_0(k2_yellow_1(A_97)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_38,c_106])).

tff(c_119,plain,(
    ! [B_98,C_99,A_97] :
      ( r1_tarski(B_98,C_99)
      | v1_xboole_0(A_97)
      | ~ r1_orders_2(k2_yellow_1(A_97),B_98,C_99)
      | ~ m1_subset_1(C_99,A_97)
      | ~ m1_subset_1(B_98,A_97)
      | v2_struct_0(k2_yellow_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_115,c_57])).

tff(c_175,plain,(
    ! [B_128,A_97,C_129] :
      ( r1_tarski(B_128,k10_lattice3(k2_yellow_1(A_97),B_128,C_129))
      | v1_xboole_0(A_97)
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(A_97),B_128,C_129),A_97)
      | ~ m1_subset_1(B_128,A_97)
      | ~ v1_lattice3(k2_yellow_1(A_97))
      | ~ v5_orders_2(k2_yellow_1(A_97))
      | v2_struct_0(k2_yellow_1(A_97))
      | ~ m1_subset_1(C_129,u1_struct_0(k2_yellow_1(A_97)))
      | ~ m1_subset_1(B_128,u1_struct_0(k2_yellow_1(A_97)))
      | ~ l1_orders_2(k2_yellow_1(A_97)) ) ),
    inference(resolution,[status(thm)],[c_171,c_119])).

tff(c_184,plain,(
    ! [B_133,A_134,C_135] :
      ( r1_tarski(B_133,k10_lattice3(k2_yellow_1(A_134),B_133,C_135))
      | v1_xboole_0(A_134)
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1(A_134),B_133,C_135),A_134)
      | ~ v1_lattice3(k2_yellow_1(A_134))
      | v2_struct_0(k2_yellow_1(A_134))
      | ~ m1_subset_1(C_135,A_134)
      | ~ m1_subset_1(B_133,A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_38,c_38,c_36,c_175])).

tff(c_196,plain,(
    ! [B_140,A_141,C_142] :
      ( r1_tarski(B_140,k10_lattice3(k2_yellow_1(A_141),B_140,C_142))
      | v1_xboole_0(A_141)
      | ~ v1_lattice3(k2_yellow_1(A_141))
      | v2_struct_0(k2_yellow_1(A_141))
      | ~ m1_subset_1(C_142,A_141)
      | ~ m1_subset_1(B_140,A_141) ) ),
    inference(resolution,[status(thm)],[c_101,c_184])).

tff(c_84,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_tarski(k2_xboole_0(A_79,C_80),B_81)
      | ~ r1_tarski(C_80,B_81)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_4'),k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_88,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_84,c_46])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_199,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_196,c_89])).

tff(c_202,plain,
    ( v1_xboole_0('#skF_2')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_56,c_52,c_199])).

tff(c_203,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_202])).

tff(c_8,plain,(
    ! [A_7] :
      ( ~ v2_struct_0(A_7)
      | ~ v1_lattice3(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_206,plain,
    ( ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_203,c_8])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52,c_206])).

tff(c_211,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_288,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | v2_struct_0(k2_yellow_1('#skF_2'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_285,c_211])).

tff(c_291,plain,
    ( v1_xboole_0('#skF_2')
    | v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_56,c_52,c_288])).

tff(c_292,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_291])).

tff(c_295,plain,
    ( ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_292,c_8])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_52,c_295])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:01:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.39  
% 2.66/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.39  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.66/1.39  
% 2.66/1.39  %Foreground sorts:
% 2.66/1.39  
% 2.66/1.39  
% 2.66/1.39  %Background operators:
% 2.66/1.39  
% 2.66/1.39  
% 2.66/1.39  %Foreground operators:
% 2.66/1.39  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.66/1.39  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.66/1.39  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.66/1.39  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.39  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.66/1.39  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 2.66/1.39  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.66/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.39  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.66/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.39  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.66/1.39  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.66/1.39  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.39  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.66/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.39  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.66/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.66/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.66/1.39  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.66/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.66/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.39  
% 2.66/1.41  tff(f_98, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 2.66/1.41  tff(f_137, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v1_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k2_xboole_0(B, C), k10_lattice3(k2_yellow_1(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_1)).
% 2.66/1.41  tff(f_110, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 2.66/1.41  tff(f_61, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 2.66/1.41  tff(f_106, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 2.66/1.41  tff(f_94, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l26_lattice3)).
% 2.66/1.41  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 2.66/1.41  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 2.66/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.66/1.41  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v1_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_lattice3)).
% 2.66/1.41  tff(c_28, plain, (![A_57]: (l1_orders_2(k2_yellow_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_98])).
% 2.66/1.41  tff(c_52, plain, (v1_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.66/1.41  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.66/1.41  tff(c_38, plain, (![A_59]: (u1_struct_0(k2_yellow_1(A_59))=A_59)), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.66/1.41  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.66/1.41  tff(c_55, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50])).
% 2.66/1.41  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.66/1.41  tff(c_56, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_48])).
% 2.66/1.41  tff(c_219, plain, (![A_149, B_150, C_151]: (m1_subset_1(k10_lattice3(A_149, B_150, C_151), u1_struct_0(A_149)) | ~m1_subset_1(C_151, u1_struct_0(A_149)) | ~m1_subset_1(B_150, u1_struct_0(A_149)) | ~l1_orders_2(A_149))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.41  tff(c_222, plain, (![A_59, B_150, C_151]: (m1_subset_1(k10_lattice3(k2_yellow_1(A_59), B_150, C_151), A_59) | ~m1_subset_1(C_151, u1_struct_0(k2_yellow_1(A_59))) | ~m1_subset_1(B_150, u1_struct_0(k2_yellow_1(A_59))) | ~l1_orders_2(k2_yellow_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_219])).
% 2.66/1.41  tff(c_224, plain, (![A_59, B_150, C_151]: (m1_subset_1(k10_lattice3(k2_yellow_1(A_59), B_150, C_151), A_59) | ~m1_subset_1(C_151, A_59) | ~m1_subset_1(B_150, A_59))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38, c_38, c_222])).
% 2.66/1.41  tff(c_36, plain, (![A_58]: (v5_orders_2(k2_yellow_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.66/1.41  tff(c_10, plain, (![A_8, B_9, C_10]: (m1_subset_1(k10_lattice3(A_8, B_9, C_10), u1_struct_0(A_8)) | ~m1_subset_1(C_10, u1_struct_0(A_8)) | ~m1_subset_1(B_9, u1_struct_0(A_8)) | ~l1_orders_2(A_8))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.41  tff(c_260, plain, (![A_170, C_171, B_172]: (r1_orders_2(A_170, C_171, k10_lattice3(A_170, B_172, C_171)) | ~m1_subset_1(k10_lattice3(A_170, B_172, C_171), u1_struct_0(A_170)) | ~m1_subset_1(C_171, u1_struct_0(A_170)) | ~m1_subset_1(B_172, u1_struct_0(A_170)) | ~l1_orders_2(A_170) | ~v1_lattice3(A_170) | ~v5_orders_2(A_170) | v2_struct_0(A_170))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.66/1.41  tff(c_268, plain, (![A_173, C_174, B_175]: (r1_orders_2(A_173, C_174, k10_lattice3(A_173, B_175, C_174)) | ~v1_lattice3(A_173) | ~v5_orders_2(A_173) | v2_struct_0(A_173) | ~m1_subset_1(C_174, u1_struct_0(A_173)) | ~m1_subset_1(B_175, u1_struct_0(A_173)) | ~l1_orders_2(A_173))), inference(resolution, [status(thm)], [c_10, c_260])).
% 2.66/1.41  tff(c_32, plain, (![A_58]: (v3_orders_2(k2_yellow_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.66/1.41  tff(c_226, plain, (![A_155, B_156, C_157]: (r3_orders_2(A_155, B_156, C_157) | ~r1_orders_2(A_155, B_156, C_157) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.41  tff(c_233, plain, (![A_59, B_156, C_157]: (r3_orders_2(k2_yellow_1(A_59), B_156, C_157) | ~r1_orders_2(k2_yellow_1(A_59), B_156, C_157) | ~m1_subset_1(C_157, A_59) | ~m1_subset_1(B_156, u1_struct_0(k2_yellow_1(A_59))) | ~l1_orders_2(k2_yellow_1(A_59)) | ~v3_orders_2(k2_yellow_1(A_59)) | v2_struct_0(k2_yellow_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_226])).
% 2.66/1.41  tff(c_244, plain, (![A_161, B_162, C_163]: (r3_orders_2(k2_yellow_1(A_161), B_162, C_163) | ~r1_orders_2(k2_yellow_1(A_161), B_162, C_163) | ~m1_subset_1(C_163, A_161) | ~m1_subset_1(B_162, A_161) | v2_struct_0(k2_yellow_1(A_161)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_38, c_233])).
% 2.66/1.41  tff(c_44, plain, (![B_64, C_66, A_60]: (r1_tarski(B_64, C_66) | ~r3_orders_2(k2_yellow_1(A_60), B_64, C_66) | ~m1_subset_1(C_66, u1_struct_0(k2_yellow_1(A_60))) | ~m1_subset_1(B_64, u1_struct_0(k2_yellow_1(A_60))) | v1_xboole_0(A_60))), inference(cnfTransformation, [status(thm)], [f_123])).
% 2.66/1.41  tff(c_57, plain, (![B_64, C_66, A_60]: (r1_tarski(B_64, C_66) | ~r3_orders_2(k2_yellow_1(A_60), B_64, C_66) | ~m1_subset_1(C_66, A_60) | ~m1_subset_1(B_64, A_60) | v1_xboole_0(A_60))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_44])).
% 2.66/1.41  tff(c_253, plain, (![B_162, C_163, A_161]: (r1_tarski(B_162, C_163) | v1_xboole_0(A_161) | ~r1_orders_2(k2_yellow_1(A_161), B_162, C_163) | ~m1_subset_1(C_163, A_161) | ~m1_subset_1(B_162, A_161) | v2_struct_0(k2_yellow_1(A_161)))), inference(resolution, [status(thm)], [c_244, c_57])).
% 2.66/1.41  tff(c_272, plain, (![C_174, A_161, B_175]: (r1_tarski(C_174, k10_lattice3(k2_yellow_1(A_161), B_175, C_174)) | v1_xboole_0(A_161) | ~m1_subset_1(k10_lattice3(k2_yellow_1(A_161), B_175, C_174), A_161) | ~m1_subset_1(C_174, A_161) | ~v1_lattice3(k2_yellow_1(A_161)) | ~v5_orders_2(k2_yellow_1(A_161)) | v2_struct_0(k2_yellow_1(A_161)) | ~m1_subset_1(C_174, u1_struct_0(k2_yellow_1(A_161))) | ~m1_subset_1(B_175, u1_struct_0(k2_yellow_1(A_161))) | ~l1_orders_2(k2_yellow_1(A_161)))), inference(resolution, [status(thm)], [c_268, c_253])).
% 2.66/1.41  tff(c_281, plain, (![C_179, A_180, B_181]: (r1_tarski(C_179, k10_lattice3(k2_yellow_1(A_180), B_181, C_179)) | v1_xboole_0(A_180) | ~m1_subset_1(k10_lattice3(k2_yellow_1(A_180), B_181, C_179), A_180) | ~v1_lattice3(k2_yellow_1(A_180)) | v2_struct_0(k2_yellow_1(A_180)) | ~m1_subset_1(C_179, A_180) | ~m1_subset_1(B_181, A_180))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38, c_38, c_36, c_272])).
% 2.66/1.41  tff(c_285, plain, (![C_182, A_183, B_184]: (r1_tarski(C_182, k10_lattice3(k2_yellow_1(A_183), B_184, C_182)) | v1_xboole_0(A_183) | ~v1_lattice3(k2_yellow_1(A_183)) | v2_struct_0(k2_yellow_1(A_183)) | ~m1_subset_1(C_182, A_183) | ~m1_subset_1(B_184, A_183))), inference(resolution, [status(thm)], [c_224, c_281])).
% 2.66/1.41  tff(c_96, plain, (![A_88, B_89, C_90]: (m1_subset_1(k10_lattice3(A_88, B_89, C_90), u1_struct_0(A_88)) | ~m1_subset_1(C_90, u1_struct_0(A_88)) | ~m1_subset_1(B_89, u1_struct_0(A_88)) | ~l1_orders_2(A_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.66/1.41  tff(c_99, plain, (![A_59, B_89, C_90]: (m1_subset_1(k10_lattice3(k2_yellow_1(A_59), B_89, C_90), A_59) | ~m1_subset_1(C_90, u1_struct_0(k2_yellow_1(A_59))) | ~m1_subset_1(B_89, u1_struct_0(k2_yellow_1(A_59))) | ~l1_orders_2(k2_yellow_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_96])).
% 2.66/1.41  tff(c_101, plain, (![A_59, B_89, C_90]: (m1_subset_1(k10_lattice3(k2_yellow_1(A_59), B_89, C_90), A_59) | ~m1_subset_1(C_90, A_59) | ~m1_subset_1(B_89, A_59))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38, c_38, c_99])).
% 2.66/1.41  tff(c_162, plain, (![A_121, B_122, C_123]: (r1_orders_2(A_121, B_122, k10_lattice3(A_121, B_122, C_123)) | ~m1_subset_1(k10_lattice3(A_121, B_122, C_123), u1_struct_0(A_121)) | ~m1_subset_1(C_123, u1_struct_0(A_121)) | ~m1_subset_1(B_122, u1_struct_0(A_121)) | ~l1_orders_2(A_121) | ~v1_lattice3(A_121) | ~v5_orders_2(A_121) | v2_struct_0(A_121))), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.66/1.41  tff(c_171, plain, (![A_127, B_128, C_129]: (r1_orders_2(A_127, B_128, k10_lattice3(A_127, B_128, C_129)) | ~v1_lattice3(A_127) | ~v5_orders_2(A_127) | v2_struct_0(A_127) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_orders_2(A_127))), inference(resolution, [status(thm)], [c_10, c_162])).
% 2.66/1.41  tff(c_102, plain, (![A_91, B_92, C_93]: (r3_orders_2(A_91, B_92, C_93) | ~r1_orders_2(A_91, B_92, C_93) | ~m1_subset_1(C_93, u1_struct_0(A_91)) | ~m1_subset_1(B_92, u1_struct_0(A_91)) | ~l1_orders_2(A_91) | ~v3_orders_2(A_91) | v2_struct_0(A_91))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.41  tff(c_106, plain, (![A_59, B_92, C_93]: (r3_orders_2(k2_yellow_1(A_59), B_92, C_93) | ~r1_orders_2(k2_yellow_1(A_59), B_92, C_93) | ~m1_subset_1(C_93, A_59) | ~m1_subset_1(B_92, u1_struct_0(k2_yellow_1(A_59))) | ~l1_orders_2(k2_yellow_1(A_59)) | ~v3_orders_2(k2_yellow_1(A_59)) | v2_struct_0(k2_yellow_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_102])).
% 2.66/1.41  tff(c_115, plain, (![A_97, B_98, C_99]: (r3_orders_2(k2_yellow_1(A_97), B_98, C_99) | ~r1_orders_2(k2_yellow_1(A_97), B_98, C_99) | ~m1_subset_1(C_99, A_97) | ~m1_subset_1(B_98, A_97) | v2_struct_0(k2_yellow_1(A_97)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_38, c_106])).
% 2.66/1.41  tff(c_119, plain, (![B_98, C_99, A_97]: (r1_tarski(B_98, C_99) | v1_xboole_0(A_97) | ~r1_orders_2(k2_yellow_1(A_97), B_98, C_99) | ~m1_subset_1(C_99, A_97) | ~m1_subset_1(B_98, A_97) | v2_struct_0(k2_yellow_1(A_97)))), inference(resolution, [status(thm)], [c_115, c_57])).
% 2.66/1.41  tff(c_175, plain, (![B_128, A_97, C_129]: (r1_tarski(B_128, k10_lattice3(k2_yellow_1(A_97), B_128, C_129)) | v1_xboole_0(A_97) | ~m1_subset_1(k10_lattice3(k2_yellow_1(A_97), B_128, C_129), A_97) | ~m1_subset_1(B_128, A_97) | ~v1_lattice3(k2_yellow_1(A_97)) | ~v5_orders_2(k2_yellow_1(A_97)) | v2_struct_0(k2_yellow_1(A_97)) | ~m1_subset_1(C_129, u1_struct_0(k2_yellow_1(A_97))) | ~m1_subset_1(B_128, u1_struct_0(k2_yellow_1(A_97))) | ~l1_orders_2(k2_yellow_1(A_97)))), inference(resolution, [status(thm)], [c_171, c_119])).
% 2.66/1.41  tff(c_184, plain, (![B_133, A_134, C_135]: (r1_tarski(B_133, k10_lattice3(k2_yellow_1(A_134), B_133, C_135)) | v1_xboole_0(A_134) | ~m1_subset_1(k10_lattice3(k2_yellow_1(A_134), B_133, C_135), A_134) | ~v1_lattice3(k2_yellow_1(A_134)) | v2_struct_0(k2_yellow_1(A_134)) | ~m1_subset_1(C_135, A_134) | ~m1_subset_1(B_133, A_134))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_38, c_38, c_36, c_175])).
% 2.66/1.41  tff(c_196, plain, (![B_140, A_141, C_142]: (r1_tarski(B_140, k10_lattice3(k2_yellow_1(A_141), B_140, C_142)) | v1_xboole_0(A_141) | ~v1_lattice3(k2_yellow_1(A_141)) | v2_struct_0(k2_yellow_1(A_141)) | ~m1_subset_1(C_142, A_141) | ~m1_subset_1(B_140, A_141))), inference(resolution, [status(thm)], [c_101, c_184])).
% 2.66/1.41  tff(c_84, plain, (![A_79, C_80, B_81]: (r1_tarski(k2_xboole_0(A_79, C_80), B_81) | ~r1_tarski(C_80, B_81) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.41  tff(c_46, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_4'), k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_137])).
% 2.66/1.41  tff(c_88, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_84, c_46])).
% 2.66/1.41  tff(c_89, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_88])).
% 2.66/1.41  tff(c_199, plain, (v1_xboole_0('#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_196, c_89])).
% 2.66/1.41  tff(c_202, plain, (v1_xboole_0('#skF_2') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_56, c_52, c_199])).
% 2.66/1.41  tff(c_203, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_202])).
% 2.66/1.41  tff(c_8, plain, (![A_7]: (~v2_struct_0(A_7) | ~v1_lattice3(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.66/1.41  tff(c_206, plain, (~v1_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_203, c_8])).
% 2.66/1.41  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_52, c_206])).
% 2.66/1.41  tff(c_211, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_88])).
% 2.66/1.41  tff(c_288, plain, (v1_xboole_0('#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_285, c_211])).
% 2.66/1.41  tff(c_291, plain, (v1_xboole_0('#skF_2') | v2_struct_0(k2_yellow_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_56, c_52, c_288])).
% 2.66/1.41  tff(c_292, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_54, c_291])).
% 2.66/1.41  tff(c_295, plain, (~v1_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_292, c_8])).
% 2.66/1.41  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_52, c_295])).
% 2.66/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.41  
% 2.66/1.41  Inference rules
% 2.66/1.41  ----------------------
% 2.66/1.41  #Ref     : 0
% 2.66/1.41  #Sup     : 43
% 2.66/1.41  #Fact    : 0
% 2.66/1.41  #Define  : 0
% 2.66/1.41  #Split   : 1
% 2.66/1.41  #Chain   : 0
% 2.66/1.41  #Close   : 0
% 2.66/1.41  
% 2.66/1.41  Ordering : KBO
% 2.66/1.41  
% 2.66/1.41  Simplification rules
% 2.66/1.41  ----------------------
% 2.66/1.41  #Subsume      : 7
% 2.66/1.41  #Demod        : 74
% 2.66/1.41  #Tautology    : 11
% 2.66/1.41  #SimpNegUnit  : 2
% 2.66/1.41  #BackRed      : 0
% 2.66/1.41  
% 2.66/1.41  #Partial instantiations: 0
% 2.66/1.41  #Strategies tried      : 1
% 2.66/1.41  
% 2.66/1.41  Timing (in seconds)
% 2.66/1.41  ----------------------
% 2.66/1.42  Preprocessing        : 0.34
% 2.66/1.42  Parsing              : 0.19
% 2.66/1.42  CNF conversion       : 0.03
% 2.66/1.42  Main loop            : 0.26
% 2.66/1.42  Inferencing          : 0.10
% 2.66/1.42  Reduction            : 0.07
% 2.66/1.42  Demodulation         : 0.05
% 2.66/1.42  BG Simplification    : 0.02
% 2.66/1.42  Subsumption          : 0.05
% 2.66/1.42  Abstraction          : 0.01
% 2.66/1.42  MUC search           : 0.00
% 2.66/1.42  Cooper               : 0.00
% 2.66/1.42  Total                : 0.64
% 2.66/1.42  Index Insertion      : 0.00
% 2.66/1.42  Index Deletion       : 0.00
% 2.66/1.42  Index Matching       : 0.00
% 2.66/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
