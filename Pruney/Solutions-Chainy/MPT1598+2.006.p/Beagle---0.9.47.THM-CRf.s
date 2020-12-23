%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:21 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 421 expanded)
%              Number of leaves         :   36 ( 175 expanded)
%              Depth                    :   13
%              Number of atoms          :  317 (1208 expanded)
%              Number of equality atoms :   15 ( 208 expanded)
%              Maximal formula depth    :   16 (   5 average)
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

tff(f_125,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v1_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k2_xboole_0(B,C),k10_lattice3(k2_yellow_1(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_101,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k10_lattice3(A,B,C) = k10_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_lattice3)).

tff(f_87,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

tff(f_121,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_138,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_42,plain,(
    ! [A_66] : u1_struct_0(k2_yellow_1(A_66)) = A_66 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_60,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_59,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54])).

tff(c_28,plain,(
    ! [A_63] : l1_orders_2(k2_yellow_1(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_332,plain,(
    ! [A_143,B_144,C_145] :
      ( m1_subset_1(k10_lattice3(A_143,B_144,C_145),u1_struct_0(A_143))
      | ~ m1_subset_1(C_145,u1_struct_0(A_143))
      | ~ m1_subset_1(B_144,u1_struct_0(A_143))
      | ~ l1_orders_2(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_335,plain,(
    ! [A_66,B_144,C_145] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(A_66),B_144,C_145),A_66)
      | ~ m1_subset_1(C_145,u1_struct_0(k2_yellow_1(A_66)))
      | ~ m1_subset_1(B_144,u1_struct_0(k2_yellow_1(A_66)))
      | ~ l1_orders_2(k2_yellow_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_332])).

tff(c_337,plain,(
    ! [A_66,B_144,C_145] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(A_66),B_144,C_145),A_66)
      | ~ m1_subset_1(C_145,A_66)
      | ~ m1_subset_1(B_144,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_42,c_335])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_36,plain,(
    ! [A_64] : v5_orders_2(k2_yellow_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_56,plain,(
    v1_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_373,plain,(
    ! [A_164,C_165,B_166] :
      ( k10_lattice3(A_164,C_165,B_166) = k10_lattice3(A_164,B_166,C_165)
      | ~ m1_subset_1(C_165,u1_struct_0(A_164))
      | ~ m1_subset_1(B_166,u1_struct_0(A_164))
      | ~ l1_orders_2(A_164)
      | ~ v1_lattice3(A_164)
      | ~ v5_orders_2(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_380,plain,(
    ! [A_66,C_165,B_166] :
      ( k10_lattice3(k2_yellow_1(A_66),C_165,B_166) = k10_lattice3(k2_yellow_1(A_66),B_166,C_165)
      | ~ m1_subset_1(C_165,A_66)
      | ~ m1_subset_1(B_166,u1_struct_0(k2_yellow_1(A_66)))
      | ~ l1_orders_2(k2_yellow_1(A_66))
      | ~ v1_lattice3(k2_yellow_1(A_66))
      | ~ v5_orders_2(k2_yellow_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_373])).

tff(c_385,plain,(
    ! [A_167,C_168,B_169] :
      ( k10_lattice3(k2_yellow_1(A_167),C_168,B_169) = k10_lattice3(k2_yellow_1(A_167),B_169,C_168)
      | ~ m1_subset_1(C_168,A_167)
      | ~ m1_subset_1(B_169,A_167)
      | ~ v1_lattice3(k2_yellow_1(A_167)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_42,c_380])).

tff(c_388,plain,(
    ! [C_168,B_169] :
      ( k10_lattice3(k2_yellow_1('#skF_2'),C_168,B_169) = k10_lattice3(k2_yellow_1('#skF_2'),B_169,C_168)
      | ~ m1_subset_1(C_168,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_385])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k10_lattice3(A_7,B_8,C_9),u1_struct_0(A_7))
      | ~ m1_subset_1(C_9,u1_struct_0(A_7))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_468,plain,(
    ! [A_172,C_173,B_174] :
      ( r1_orders_2(A_172,C_173,k10_lattice3(A_172,B_174,C_173))
      | ~ m1_subset_1(k10_lattice3(A_172,B_174,C_173),u1_struct_0(A_172))
      | ~ m1_subset_1(C_173,u1_struct_0(A_172))
      | ~ m1_subset_1(B_174,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v1_lattice3(A_172)
      | ~ v5_orders_2(A_172)
      | v2_struct_0(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_491,plain,(
    ! [A_175,C_176,B_177] :
      ( r1_orders_2(A_175,C_176,k10_lattice3(A_175,B_177,C_176))
      | ~ v1_lattice3(A_175)
      | ~ v5_orders_2(A_175)
      | v2_struct_0(A_175)
      | ~ m1_subset_1(C_176,u1_struct_0(A_175))
      | ~ m1_subset_1(B_177,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175) ) ),
    inference(resolution,[status(thm)],[c_8,c_468])).

tff(c_498,plain,(
    ! [C_168,B_169] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_168,k10_lattice3(k2_yellow_1('#skF_2'),C_168,B_169))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_168,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_169,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_168,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_491])).

tff(c_506,plain,(
    ! [C_168,B_169] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_168,k10_lattice3(k2_yellow_1('#skF_2'),C_168,B_169))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_168,'#skF_2')
      | ~ m1_subset_1(B_169,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_42,c_36,c_56,c_498])).

tff(c_509,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_506])).

tff(c_40,plain,(
    ! [A_65] :
      ( ~ v2_struct_0(k2_yellow_1(A_65))
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_512,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_509,c_40])).

tff(c_516,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_512])).

tff(c_518,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_535,plain,(
    ! [C_181,B_182] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_181,k10_lattice3(k2_yellow_1('#skF_2'),C_181,B_182))
      | ~ m1_subset_1(C_181,'#skF_2')
      | ~ m1_subset_1(B_182,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_506])).

tff(c_32,plain,(
    ! [A_64] : v3_orders_2(k2_yellow_1(A_64)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_346,plain,(
    ! [A_155,B_156,C_157] :
      ( r3_orders_2(A_155,B_156,C_157)
      | ~ r1_orders_2(A_155,B_156,C_157)
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v3_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_353,plain,(
    ! [A_66,B_156,C_157] :
      ( r3_orders_2(k2_yellow_1(A_66),B_156,C_157)
      | ~ r1_orders_2(k2_yellow_1(A_66),B_156,C_157)
      | ~ m1_subset_1(C_157,A_66)
      | ~ m1_subset_1(B_156,u1_struct_0(k2_yellow_1(A_66)))
      | ~ l1_orders_2(k2_yellow_1(A_66))
      | ~ v3_orders_2(k2_yellow_1(A_66))
      | v2_struct_0(k2_yellow_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_346])).

tff(c_358,plain,(
    ! [A_158,B_159,C_160] :
      ( r3_orders_2(k2_yellow_1(A_158),B_159,C_160)
      | ~ r1_orders_2(k2_yellow_1(A_158),B_159,C_160)
      | ~ m1_subset_1(C_160,A_158)
      | ~ m1_subset_1(B_159,A_158)
      | v2_struct_0(k2_yellow_1(A_158)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_42,c_353])).

tff(c_48,plain,(
    ! [B_71,C_73,A_67] :
      ( r1_tarski(B_71,C_73)
      | ~ r3_orders_2(k2_yellow_1(A_67),B_71,C_73)
      | ~ m1_subset_1(C_73,u1_struct_0(k2_yellow_1(A_67)))
      | ~ m1_subset_1(B_71,u1_struct_0(k2_yellow_1(A_67)))
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_61,plain,(
    ! [B_71,C_73,A_67] :
      ( r1_tarski(B_71,C_73)
      | ~ r3_orders_2(k2_yellow_1(A_67),B_71,C_73)
      | ~ m1_subset_1(C_73,A_67)
      | ~ m1_subset_1(B_71,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_48])).

tff(c_367,plain,(
    ! [B_159,C_160,A_158] :
      ( r1_tarski(B_159,C_160)
      | v1_xboole_0(A_158)
      | ~ r1_orders_2(k2_yellow_1(A_158),B_159,C_160)
      | ~ m1_subset_1(C_160,A_158)
      | ~ m1_subset_1(B_159,A_158)
      | v2_struct_0(k2_yellow_1(A_158)) ) ),
    inference(resolution,[status(thm)],[c_358,c_61])).

tff(c_538,plain,(
    ! [C_181,B_182] :
      ( r1_tarski(C_181,k10_lattice3(k2_yellow_1('#skF_2'),C_181,B_182))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_181,B_182),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_181,'#skF_2')
      | ~ m1_subset_1(B_182,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_535,c_367])).

tff(c_549,plain,(
    ! [C_183,B_184] :
      ( r1_tarski(C_183,k10_lattice3(k2_yellow_1('#skF_2'),C_183,B_184))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_183,B_184),'#skF_2')
      | ~ m1_subset_1(C_183,'#skF_2')
      | ~ m1_subset_1(B_184,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_518,c_58,c_538])).

tff(c_389,plain,(
    ! [C_170,B_171] :
      ( k10_lattice3(k2_yellow_1('#skF_2'),C_170,B_171) = k10_lattice3(k2_yellow_1('#skF_2'),B_171,C_170)
      | ~ m1_subset_1(C_170,'#skF_2')
      | ~ m1_subset_1(B_171,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_385])).

tff(c_101,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1(k10_lattice3(A_95,B_96,C_97),u1_struct_0(A_95))
      | ~ m1_subset_1(C_97,u1_struct_0(A_95))
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    ! [A_66,B_96,C_97] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(A_66),B_96,C_97),A_66)
      | ~ m1_subset_1(C_97,u1_struct_0(k2_yellow_1(A_66)))
      | ~ m1_subset_1(B_96,u1_struct_0(k2_yellow_1(A_66)))
      | ~ l1_orders_2(k2_yellow_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_101])).

tff(c_106,plain,(
    ! [A_66,B_96,C_97] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1(A_66),B_96,C_97),A_66)
      | ~ m1_subset_1(C_97,A_66)
      | ~ m1_subset_1(B_96,A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_42,c_104])).

tff(c_107,plain,(
    ! [A_98,C_99,B_100] :
      ( k10_lattice3(A_98,C_99,B_100) = k10_lattice3(A_98,B_100,C_99)
      | ~ m1_subset_1(C_99,u1_struct_0(A_98))
      | ~ m1_subset_1(B_100,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v1_lattice3(A_98)
      | ~ v5_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_111,plain,(
    ! [A_66,C_99,B_100] :
      ( k10_lattice3(k2_yellow_1(A_66),C_99,B_100) = k10_lattice3(k2_yellow_1(A_66),B_100,C_99)
      | ~ m1_subset_1(C_99,A_66)
      | ~ m1_subset_1(B_100,u1_struct_0(k2_yellow_1(A_66)))
      | ~ l1_orders_2(k2_yellow_1(A_66))
      | ~ v1_lattice3(k2_yellow_1(A_66))
      | ~ v5_orders_2(k2_yellow_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_107])).

tff(c_120,plain,(
    ! [A_104,C_105,B_106] :
      ( k10_lattice3(k2_yellow_1(A_104),C_105,B_106) = k10_lattice3(k2_yellow_1(A_104),B_106,C_105)
      | ~ m1_subset_1(C_105,A_104)
      | ~ m1_subset_1(B_106,A_104)
      | ~ v1_lattice3(k2_yellow_1(A_104)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_28,c_42,c_111])).

tff(c_123,plain,(
    ! [C_105,B_106] :
      ( k10_lattice3(k2_yellow_1('#skF_2'),C_105,B_106) = k10_lattice3(k2_yellow_1('#skF_2'),B_106,C_105)
      | ~ m1_subset_1(C_105,'#skF_2')
      | ~ m1_subset_1(B_106,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_120])).

tff(c_231,plain,(
    ! [A_124,B_125,C_126] :
      ( r1_orders_2(A_124,B_125,k10_lattice3(A_124,B_125,C_126))
      | ~ m1_subset_1(k10_lattice3(A_124,B_125,C_126),u1_struct_0(A_124))
      | ~ m1_subset_1(C_126,u1_struct_0(A_124))
      | ~ m1_subset_1(B_125,u1_struct_0(A_124))
      | ~ l1_orders_2(A_124)
      | ~ v1_lattice3(A_124)
      | ~ v5_orders_2(A_124)
      | v2_struct_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_247,plain,(
    ! [A_127,B_128,C_129] :
      ( r1_orders_2(A_127,B_128,k10_lattice3(A_127,B_128,C_129))
      | ~ v1_lattice3(A_127)
      | ~ v5_orders_2(A_127)
      | v2_struct_0(A_127)
      | ~ m1_subset_1(C_129,u1_struct_0(A_127))
      | ~ m1_subset_1(B_128,u1_struct_0(A_127))
      | ~ l1_orders_2(A_127) ) ),
    inference(resolution,[status(thm)],[c_8,c_231])).

tff(c_254,plain,(
    ! [B_106,C_105] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_106,k10_lattice3(k2_yellow_1('#skF_2'),C_105,B_106))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_105,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_106,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_105,'#skF_2')
      | ~ m1_subset_1(B_106,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_247])).

tff(c_262,plain,(
    ! [B_106,C_105] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_106,k10_lattice3(k2_yellow_1('#skF_2'),C_105,B_106))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_105,'#skF_2')
      | ~ m1_subset_1(B_106,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_42,c_42,c_36,c_56,c_254])).

tff(c_265,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_262])).

tff(c_284,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_265,c_40])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_284])).

tff(c_290,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_291,plain,(
    ! [B_133,C_134] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_133,k10_lattice3(k2_yellow_1('#skF_2'),C_134,B_133))
      | ~ m1_subset_1(C_134,'#skF_2')
      | ~ m1_subset_1(B_133,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_262])).

tff(c_193,plain,(
    ! [A_109,B_110,C_111] :
      ( r3_orders_2(A_109,B_110,C_111)
      | ~ r1_orders_2(A_109,B_110,C_111)
      | ~ m1_subset_1(C_111,u1_struct_0(A_109))
      | ~ m1_subset_1(B_110,u1_struct_0(A_109))
      | ~ l1_orders_2(A_109)
      | ~ v3_orders_2(A_109)
      | v2_struct_0(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_200,plain,(
    ! [A_66,B_110,C_111] :
      ( r3_orders_2(k2_yellow_1(A_66),B_110,C_111)
      | ~ r1_orders_2(k2_yellow_1(A_66),B_110,C_111)
      | ~ m1_subset_1(C_111,A_66)
      | ~ m1_subset_1(B_110,u1_struct_0(k2_yellow_1(A_66)))
      | ~ l1_orders_2(k2_yellow_1(A_66))
      | ~ v3_orders_2(k2_yellow_1(A_66))
      | v2_struct_0(k2_yellow_1(A_66)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_193])).

tff(c_209,plain,(
    ! [A_112,B_113,C_114] :
      ( r3_orders_2(k2_yellow_1(A_112),B_113,C_114)
      | ~ r1_orders_2(k2_yellow_1(A_112),B_113,C_114)
      | ~ m1_subset_1(C_114,A_112)
      | ~ m1_subset_1(B_113,A_112)
      | v2_struct_0(k2_yellow_1(A_112)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_42,c_200])).

tff(c_213,plain,(
    ! [B_113,C_114,A_112] :
      ( r1_tarski(B_113,C_114)
      | v1_xboole_0(A_112)
      | ~ r1_orders_2(k2_yellow_1(A_112),B_113,C_114)
      | ~ m1_subset_1(C_114,A_112)
      | ~ m1_subset_1(B_113,A_112)
      | v2_struct_0(k2_yellow_1(A_112)) ) ),
    inference(resolution,[status(thm)],[c_209,c_61])).

tff(c_294,plain,(
    ! [B_133,C_134] :
      ( r1_tarski(B_133,k10_lattice3(k2_yellow_1('#skF_2'),C_134,B_133))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_134,B_133),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_134,'#skF_2')
      | ~ m1_subset_1(B_133,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_291,c_213])).

tff(c_304,plain,(
    ! [B_135,C_136] :
      ( r1_tarski(B_135,k10_lattice3(k2_yellow_1('#skF_2'),C_136,B_135))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),C_136,B_135),'#skF_2')
      | ~ m1_subset_1(C_136,'#skF_2')
      | ~ m1_subset_1(B_135,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_290,c_58,c_294])).

tff(c_124,plain,(
    ! [C_107,B_108] :
      ( k10_lattice3(k2_yellow_1('#skF_2'),C_107,B_108) = k10_lattice3(k2_yellow_1('#skF_2'),B_108,C_107)
      | ~ m1_subset_1(C_107,'#skF_2')
      | ~ m1_subset_1(B_108,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_120])).

tff(c_89,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(k2_xboole_0(A_86,C_87),B_88)
      | ~ r1_tarski(C_87,B_88)
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_4'),k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_93,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_89,c_50])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_151,plain,
    ( ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_94])).

tff(c_182,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_151])).

tff(c_307,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_304,c_182])).

tff(c_316,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_307])).

tff(c_319,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_106,c_316])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_319])).

tff(c_324,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_425,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'))
    | ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_324])).

tff(c_459,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_425])).

tff(c_552,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_549,c_459])).

tff(c_561,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_552])).

tff(c_564,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_337,c_561])).

tff(c_568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:18:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.45  
% 2.97/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.45  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.97/1.45  
% 2.97/1.45  %Foreground sorts:
% 2.97/1.45  
% 2.97/1.45  
% 2.97/1.45  %Background operators:
% 2.97/1.45  
% 2.97/1.45  
% 2.97/1.45  %Foreground operators:
% 2.97/1.45  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.97/1.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.97/1.45  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.97/1.45  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.45  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.97/1.45  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 2.97/1.45  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.97/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.45  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 2.97/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.45  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.97/1.45  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.97/1.45  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.45  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.97/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.45  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.97/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.97/1.45  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.97/1.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.97/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.45  
% 3.15/1.47  tff(f_125, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.15/1.47  tff(f_152, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v1_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k2_xboole_0(B, C), k10_lattice3(k2_yellow_1(A), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_1)).
% 3.15/1.47  tff(f_105, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.15/1.47  tff(f_54, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 3.15/1.47  tff(f_113, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.15/1.47  tff(f_101, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k10_lattice3(A, B, C) = k10_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_lattice3)).
% 3.15/1.47  tff(f_87, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k10_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 3.15/1.47  tff(f_121, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.15/1.47  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.15/1.47  tff(f_138, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.15/1.47  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.15/1.47  tff(c_42, plain, (![A_66]: (u1_struct_0(k2_yellow_1(A_66))=A_66)), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.15/1.47  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.15/1.47  tff(c_60, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52])).
% 3.15/1.47  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.15/1.47  tff(c_59, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54])).
% 3.15/1.47  tff(c_28, plain, (![A_63]: (l1_orders_2(k2_yellow_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.15/1.47  tff(c_332, plain, (![A_143, B_144, C_145]: (m1_subset_1(k10_lattice3(A_143, B_144, C_145), u1_struct_0(A_143)) | ~m1_subset_1(C_145, u1_struct_0(A_143)) | ~m1_subset_1(B_144, u1_struct_0(A_143)) | ~l1_orders_2(A_143))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.47  tff(c_335, plain, (![A_66, B_144, C_145]: (m1_subset_1(k10_lattice3(k2_yellow_1(A_66), B_144, C_145), A_66) | ~m1_subset_1(C_145, u1_struct_0(k2_yellow_1(A_66))) | ~m1_subset_1(B_144, u1_struct_0(k2_yellow_1(A_66))) | ~l1_orders_2(k2_yellow_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_332])).
% 3.15/1.47  tff(c_337, plain, (![A_66, B_144, C_145]: (m1_subset_1(k10_lattice3(k2_yellow_1(A_66), B_144, C_145), A_66) | ~m1_subset_1(C_145, A_66) | ~m1_subset_1(B_144, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_42, c_335])).
% 3.15/1.47  tff(c_58, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.15/1.47  tff(c_36, plain, (![A_64]: (v5_orders_2(k2_yellow_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.15/1.47  tff(c_56, plain, (v1_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.15/1.47  tff(c_373, plain, (![A_164, C_165, B_166]: (k10_lattice3(A_164, C_165, B_166)=k10_lattice3(A_164, B_166, C_165) | ~m1_subset_1(C_165, u1_struct_0(A_164)) | ~m1_subset_1(B_166, u1_struct_0(A_164)) | ~l1_orders_2(A_164) | ~v1_lattice3(A_164) | ~v5_orders_2(A_164))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.15/1.47  tff(c_380, plain, (![A_66, C_165, B_166]: (k10_lattice3(k2_yellow_1(A_66), C_165, B_166)=k10_lattice3(k2_yellow_1(A_66), B_166, C_165) | ~m1_subset_1(C_165, A_66) | ~m1_subset_1(B_166, u1_struct_0(k2_yellow_1(A_66))) | ~l1_orders_2(k2_yellow_1(A_66)) | ~v1_lattice3(k2_yellow_1(A_66)) | ~v5_orders_2(k2_yellow_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_373])).
% 3.15/1.47  tff(c_385, plain, (![A_167, C_168, B_169]: (k10_lattice3(k2_yellow_1(A_167), C_168, B_169)=k10_lattice3(k2_yellow_1(A_167), B_169, C_168) | ~m1_subset_1(C_168, A_167) | ~m1_subset_1(B_169, A_167) | ~v1_lattice3(k2_yellow_1(A_167)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_42, c_380])).
% 3.15/1.47  tff(c_388, plain, (![C_168, B_169]: (k10_lattice3(k2_yellow_1('#skF_2'), C_168, B_169)=k10_lattice3(k2_yellow_1('#skF_2'), B_169, C_168) | ~m1_subset_1(C_168, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_385])).
% 3.15/1.47  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k10_lattice3(A_7, B_8, C_9), u1_struct_0(A_7)) | ~m1_subset_1(C_9, u1_struct_0(A_7)) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.47  tff(c_468, plain, (![A_172, C_173, B_174]: (r1_orders_2(A_172, C_173, k10_lattice3(A_172, B_174, C_173)) | ~m1_subset_1(k10_lattice3(A_172, B_174, C_173), u1_struct_0(A_172)) | ~m1_subset_1(C_173, u1_struct_0(A_172)) | ~m1_subset_1(B_174, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v1_lattice3(A_172) | ~v5_orders_2(A_172) | v2_struct_0(A_172))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.15/1.47  tff(c_491, plain, (![A_175, C_176, B_177]: (r1_orders_2(A_175, C_176, k10_lattice3(A_175, B_177, C_176)) | ~v1_lattice3(A_175) | ~v5_orders_2(A_175) | v2_struct_0(A_175) | ~m1_subset_1(C_176, u1_struct_0(A_175)) | ~m1_subset_1(B_177, u1_struct_0(A_175)) | ~l1_orders_2(A_175))), inference(resolution, [status(thm)], [c_8, c_468])).
% 3.15/1.47  tff(c_498, plain, (![C_168, B_169]: (r1_orders_2(k2_yellow_1('#skF_2'), C_168, k10_lattice3(k2_yellow_1('#skF_2'), C_168, B_169)) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_168, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_169, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_168, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_388, c_491])).
% 3.15/1.47  tff(c_506, plain, (![C_168, B_169]: (r1_orders_2(k2_yellow_1('#skF_2'), C_168, k10_lattice3(k2_yellow_1('#skF_2'), C_168, B_169)) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_168, '#skF_2') | ~m1_subset_1(B_169, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_42, c_36, c_56, c_498])).
% 3.15/1.47  tff(c_509, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_506])).
% 3.15/1.47  tff(c_40, plain, (![A_65]: (~v2_struct_0(k2_yellow_1(A_65)) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.15/1.48  tff(c_512, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_509, c_40])).
% 3.15/1.48  tff(c_516, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_512])).
% 3.15/1.48  tff(c_518, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_506])).
% 3.15/1.48  tff(c_535, plain, (![C_181, B_182]: (r1_orders_2(k2_yellow_1('#skF_2'), C_181, k10_lattice3(k2_yellow_1('#skF_2'), C_181, B_182)) | ~m1_subset_1(C_181, '#skF_2') | ~m1_subset_1(B_182, '#skF_2'))), inference(splitRight, [status(thm)], [c_506])).
% 3.15/1.48  tff(c_32, plain, (![A_64]: (v3_orders_2(k2_yellow_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.15/1.48  tff(c_346, plain, (![A_155, B_156, C_157]: (r3_orders_2(A_155, B_156, C_157) | ~r1_orders_2(A_155, B_156, C_157) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v3_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.48  tff(c_353, plain, (![A_66, B_156, C_157]: (r3_orders_2(k2_yellow_1(A_66), B_156, C_157) | ~r1_orders_2(k2_yellow_1(A_66), B_156, C_157) | ~m1_subset_1(C_157, A_66) | ~m1_subset_1(B_156, u1_struct_0(k2_yellow_1(A_66))) | ~l1_orders_2(k2_yellow_1(A_66)) | ~v3_orders_2(k2_yellow_1(A_66)) | v2_struct_0(k2_yellow_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_346])).
% 3.15/1.48  tff(c_358, plain, (![A_158, B_159, C_160]: (r3_orders_2(k2_yellow_1(A_158), B_159, C_160) | ~r1_orders_2(k2_yellow_1(A_158), B_159, C_160) | ~m1_subset_1(C_160, A_158) | ~m1_subset_1(B_159, A_158) | v2_struct_0(k2_yellow_1(A_158)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_42, c_353])).
% 3.15/1.48  tff(c_48, plain, (![B_71, C_73, A_67]: (r1_tarski(B_71, C_73) | ~r3_orders_2(k2_yellow_1(A_67), B_71, C_73) | ~m1_subset_1(C_73, u1_struct_0(k2_yellow_1(A_67))) | ~m1_subset_1(B_71, u1_struct_0(k2_yellow_1(A_67))) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.15/1.48  tff(c_61, plain, (![B_71, C_73, A_67]: (r1_tarski(B_71, C_73) | ~r3_orders_2(k2_yellow_1(A_67), B_71, C_73) | ~m1_subset_1(C_73, A_67) | ~m1_subset_1(B_71, A_67) | v1_xboole_0(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_48])).
% 3.15/1.48  tff(c_367, plain, (![B_159, C_160, A_158]: (r1_tarski(B_159, C_160) | v1_xboole_0(A_158) | ~r1_orders_2(k2_yellow_1(A_158), B_159, C_160) | ~m1_subset_1(C_160, A_158) | ~m1_subset_1(B_159, A_158) | v2_struct_0(k2_yellow_1(A_158)))), inference(resolution, [status(thm)], [c_358, c_61])).
% 3.15/1.48  tff(c_538, plain, (![C_181, B_182]: (r1_tarski(C_181, k10_lattice3(k2_yellow_1('#skF_2'), C_181, B_182)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_181, B_182), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_181, '#skF_2') | ~m1_subset_1(B_182, '#skF_2'))), inference(resolution, [status(thm)], [c_535, c_367])).
% 3.15/1.48  tff(c_549, plain, (![C_183, B_184]: (r1_tarski(C_183, k10_lattice3(k2_yellow_1('#skF_2'), C_183, B_184)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_183, B_184), '#skF_2') | ~m1_subset_1(C_183, '#skF_2') | ~m1_subset_1(B_184, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_518, c_58, c_538])).
% 3.15/1.48  tff(c_389, plain, (![C_170, B_171]: (k10_lattice3(k2_yellow_1('#skF_2'), C_170, B_171)=k10_lattice3(k2_yellow_1('#skF_2'), B_171, C_170) | ~m1_subset_1(C_170, '#skF_2') | ~m1_subset_1(B_171, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_385])).
% 3.15/1.48  tff(c_101, plain, (![A_95, B_96, C_97]: (m1_subset_1(k10_lattice3(A_95, B_96, C_97), u1_struct_0(A_95)) | ~m1_subset_1(C_97, u1_struct_0(A_95)) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.48  tff(c_104, plain, (![A_66, B_96, C_97]: (m1_subset_1(k10_lattice3(k2_yellow_1(A_66), B_96, C_97), A_66) | ~m1_subset_1(C_97, u1_struct_0(k2_yellow_1(A_66))) | ~m1_subset_1(B_96, u1_struct_0(k2_yellow_1(A_66))) | ~l1_orders_2(k2_yellow_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_101])).
% 3.15/1.48  tff(c_106, plain, (![A_66, B_96, C_97]: (m1_subset_1(k10_lattice3(k2_yellow_1(A_66), B_96, C_97), A_66) | ~m1_subset_1(C_97, A_66) | ~m1_subset_1(B_96, A_66))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_42, c_104])).
% 3.15/1.48  tff(c_107, plain, (![A_98, C_99, B_100]: (k10_lattice3(A_98, C_99, B_100)=k10_lattice3(A_98, B_100, C_99) | ~m1_subset_1(C_99, u1_struct_0(A_98)) | ~m1_subset_1(B_100, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v1_lattice3(A_98) | ~v5_orders_2(A_98))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.15/1.48  tff(c_111, plain, (![A_66, C_99, B_100]: (k10_lattice3(k2_yellow_1(A_66), C_99, B_100)=k10_lattice3(k2_yellow_1(A_66), B_100, C_99) | ~m1_subset_1(C_99, A_66) | ~m1_subset_1(B_100, u1_struct_0(k2_yellow_1(A_66))) | ~l1_orders_2(k2_yellow_1(A_66)) | ~v1_lattice3(k2_yellow_1(A_66)) | ~v5_orders_2(k2_yellow_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_107])).
% 3.15/1.48  tff(c_120, plain, (![A_104, C_105, B_106]: (k10_lattice3(k2_yellow_1(A_104), C_105, B_106)=k10_lattice3(k2_yellow_1(A_104), B_106, C_105) | ~m1_subset_1(C_105, A_104) | ~m1_subset_1(B_106, A_104) | ~v1_lattice3(k2_yellow_1(A_104)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_28, c_42, c_111])).
% 3.15/1.48  tff(c_123, plain, (![C_105, B_106]: (k10_lattice3(k2_yellow_1('#skF_2'), C_105, B_106)=k10_lattice3(k2_yellow_1('#skF_2'), B_106, C_105) | ~m1_subset_1(C_105, '#skF_2') | ~m1_subset_1(B_106, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_120])).
% 3.15/1.48  tff(c_231, plain, (![A_124, B_125, C_126]: (r1_orders_2(A_124, B_125, k10_lattice3(A_124, B_125, C_126)) | ~m1_subset_1(k10_lattice3(A_124, B_125, C_126), u1_struct_0(A_124)) | ~m1_subset_1(C_126, u1_struct_0(A_124)) | ~m1_subset_1(B_125, u1_struct_0(A_124)) | ~l1_orders_2(A_124) | ~v1_lattice3(A_124) | ~v5_orders_2(A_124) | v2_struct_0(A_124))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.15/1.48  tff(c_247, plain, (![A_127, B_128, C_129]: (r1_orders_2(A_127, B_128, k10_lattice3(A_127, B_128, C_129)) | ~v1_lattice3(A_127) | ~v5_orders_2(A_127) | v2_struct_0(A_127) | ~m1_subset_1(C_129, u1_struct_0(A_127)) | ~m1_subset_1(B_128, u1_struct_0(A_127)) | ~l1_orders_2(A_127))), inference(resolution, [status(thm)], [c_8, c_231])).
% 3.15/1.48  tff(c_254, plain, (![B_106, C_105]: (r1_orders_2(k2_yellow_1('#skF_2'), B_106, k10_lattice3(k2_yellow_1('#skF_2'), C_105, B_106)) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_105, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_106, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_105, '#skF_2') | ~m1_subset_1(B_106, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_247])).
% 3.15/1.48  tff(c_262, plain, (![B_106, C_105]: (r1_orders_2(k2_yellow_1('#skF_2'), B_106, k10_lattice3(k2_yellow_1('#skF_2'), C_105, B_106)) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_105, '#skF_2') | ~m1_subset_1(B_106, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_42, c_42, c_36, c_56, c_254])).
% 3.15/1.48  tff(c_265, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_262])).
% 3.15/1.48  tff(c_284, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_265, c_40])).
% 3.15/1.48  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_284])).
% 3.15/1.48  tff(c_290, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_262])).
% 3.15/1.48  tff(c_291, plain, (![B_133, C_134]: (r1_orders_2(k2_yellow_1('#skF_2'), B_133, k10_lattice3(k2_yellow_1('#skF_2'), C_134, B_133)) | ~m1_subset_1(C_134, '#skF_2') | ~m1_subset_1(B_133, '#skF_2'))), inference(splitRight, [status(thm)], [c_262])).
% 3.15/1.48  tff(c_193, plain, (![A_109, B_110, C_111]: (r3_orders_2(A_109, B_110, C_111) | ~r1_orders_2(A_109, B_110, C_111) | ~m1_subset_1(C_111, u1_struct_0(A_109)) | ~m1_subset_1(B_110, u1_struct_0(A_109)) | ~l1_orders_2(A_109) | ~v3_orders_2(A_109) | v2_struct_0(A_109))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.48  tff(c_200, plain, (![A_66, B_110, C_111]: (r3_orders_2(k2_yellow_1(A_66), B_110, C_111) | ~r1_orders_2(k2_yellow_1(A_66), B_110, C_111) | ~m1_subset_1(C_111, A_66) | ~m1_subset_1(B_110, u1_struct_0(k2_yellow_1(A_66))) | ~l1_orders_2(k2_yellow_1(A_66)) | ~v3_orders_2(k2_yellow_1(A_66)) | v2_struct_0(k2_yellow_1(A_66)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_193])).
% 3.15/1.48  tff(c_209, plain, (![A_112, B_113, C_114]: (r3_orders_2(k2_yellow_1(A_112), B_113, C_114) | ~r1_orders_2(k2_yellow_1(A_112), B_113, C_114) | ~m1_subset_1(C_114, A_112) | ~m1_subset_1(B_113, A_112) | v2_struct_0(k2_yellow_1(A_112)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_42, c_200])).
% 3.15/1.48  tff(c_213, plain, (![B_113, C_114, A_112]: (r1_tarski(B_113, C_114) | v1_xboole_0(A_112) | ~r1_orders_2(k2_yellow_1(A_112), B_113, C_114) | ~m1_subset_1(C_114, A_112) | ~m1_subset_1(B_113, A_112) | v2_struct_0(k2_yellow_1(A_112)))), inference(resolution, [status(thm)], [c_209, c_61])).
% 3.15/1.48  tff(c_294, plain, (![B_133, C_134]: (r1_tarski(B_133, k10_lattice3(k2_yellow_1('#skF_2'), C_134, B_133)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_134, B_133), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_134, '#skF_2') | ~m1_subset_1(B_133, '#skF_2'))), inference(resolution, [status(thm)], [c_291, c_213])).
% 3.15/1.48  tff(c_304, plain, (![B_135, C_136]: (r1_tarski(B_135, k10_lattice3(k2_yellow_1('#skF_2'), C_136, B_135)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), C_136, B_135), '#skF_2') | ~m1_subset_1(C_136, '#skF_2') | ~m1_subset_1(B_135, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_290, c_58, c_294])).
% 3.15/1.48  tff(c_124, plain, (![C_107, B_108]: (k10_lattice3(k2_yellow_1('#skF_2'), C_107, B_108)=k10_lattice3(k2_yellow_1('#skF_2'), B_108, C_107) | ~m1_subset_1(C_107, '#skF_2') | ~m1_subset_1(B_108, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_120])).
% 3.15/1.48  tff(c_89, plain, (![A_86, C_87, B_88]: (r1_tarski(k2_xboole_0(A_86, C_87), B_88) | ~r1_tarski(C_87, B_88) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.48  tff(c_50, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_4'), k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.15/1.48  tff(c_93, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_89, c_50])).
% 3.15/1.48  tff(c_94, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_93])).
% 3.15/1.48  tff(c_151, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_124, c_94])).
% 3.15/1.48  tff(c_182, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_151])).
% 3.15/1.48  tff(c_307, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_304, c_182])).
% 3.15/1.48  tff(c_316, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_307])).
% 3.15/1.48  tff(c_319, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_106, c_316])).
% 3.15/1.48  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_319])).
% 3.15/1.48  tff(c_324, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_93])).
% 3.15/1.48  tff(c_425, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3')) | ~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_389, c_324])).
% 3.15/1.48  tff(c_459, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_425])).
% 3.15/1.48  tff(c_552, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_549, c_459])).
% 3.15/1.48  tff(c_561, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_552])).
% 3.15/1.48  tff(c_564, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_337, c_561])).
% 3.15/1.48  tff(c_568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_564])).
% 3.15/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  Inference rules
% 3.15/1.48  ----------------------
% 3.15/1.48  #Ref     : 0
% 3.15/1.48  #Sup     : 105
% 3.15/1.48  #Fact    : 0
% 3.15/1.48  #Define  : 0
% 3.15/1.48  #Split   : 3
% 3.15/1.48  #Chain   : 0
% 3.15/1.48  #Close   : 0
% 3.15/1.48  
% 3.15/1.48  Ordering : KBO
% 3.15/1.48  
% 3.15/1.48  Simplification rules
% 3.15/1.48  ----------------------
% 3.15/1.48  #Subsume      : 17
% 3.15/1.48  #Demod        : 180
% 3.15/1.48  #Tautology    : 29
% 3.15/1.48  #SimpNegUnit  : 5
% 3.15/1.48  #BackRed      : 0
% 3.15/1.48  
% 3.15/1.48  #Partial instantiations: 0
% 3.15/1.48  #Strategies tried      : 1
% 3.15/1.48  
% 3.15/1.48  Timing (in seconds)
% 3.15/1.48  ----------------------
% 3.15/1.48  Preprocessing        : 0.34
% 3.15/1.48  Parsing              : 0.18
% 3.15/1.48  CNF conversion       : 0.03
% 3.15/1.48  Main loop            : 0.34
% 3.15/1.48  Inferencing          : 0.12
% 3.15/1.48  Reduction            : 0.11
% 3.15/1.48  Demodulation         : 0.08
% 3.15/1.48  BG Simplification    : 0.02
% 3.15/1.48  Subsumption          : 0.06
% 3.15/1.48  Abstraction          : 0.02
% 3.15/1.48  MUC search           : 0.00
% 3.15/1.48  Cooper               : 0.00
% 3.15/1.48  Total                : 0.73
% 3.15/1.48  Index Insertion      : 0.00
% 3.15/1.48  Index Deletion       : 0.00
% 3.15/1.48  Index Matching       : 0.00
% 3.15/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
