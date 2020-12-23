%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:24 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 420 expanded)
%              Number of leaves         :   37 ( 175 expanded)
%              Depth                    :   15
%              Number of atoms          :  501 (1213 expanded)
%              Number of equality atoms :   65 ( 261 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_126,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_139,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_110,axiom,(
    ! [A] :
      ( ( v3_orders_2(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( B = k12_lattice3(A,B,C)
              <=> r3_orders_2(A,B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_yellow_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_73,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( v4_orders_2(A)
                   => k11_lattice3(A,k11_lattice3(A,B,C),D) = k11_lattice3(A,B,k11_lattice3(A,C,D)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_lattice3)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_36,plain,(
    ! [A_45] : u1_struct_0(k2_yellow_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_54,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_53,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_48])).

tff(c_26,plain,(
    ! [A_43] : l1_orders_2(k2_yellow_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_880,plain,(
    ! [A_161,B_162,C_163] :
      ( m1_subset_1(k11_lattice3(A_161,B_162,C_163),u1_struct_0(A_161))
      | ~ m1_subset_1(C_163,u1_struct_0(A_161))
      | ~ m1_subset_1(B_162,u1_struct_0(A_161))
      | ~ l1_orders_2(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_883,plain,(
    ! [A_45,B_162,C_163] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_45),B_162,C_163),A_45)
      | ~ m1_subset_1(C_163,u1_struct_0(k2_yellow_1(A_45)))
      | ~ m1_subset_1(B_162,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_880])).

tff(c_885,plain,(
    ! [A_45,B_162,C_163] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_45),B_162,C_163),A_45)
      | ~ m1_subset_1(C_163,A_45)
      | ~ m1_subset_1(B_162,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_36,c_883])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    v2_lattice3(k2_yellow_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_30,plain,(
    ! [A_44] : v3_orders_2(k2_yellow_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_34,plain,(
    ! [A_44] : v5_orders_2(k2_yellow_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    ! [A_46,B_50,C_52] :
      ( r3_orders_2(k2_yellow_1(A_46),B_50,C_52)
      | ~ r1_tarski(B_50,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(k2_yellow_1(A_46)))
      | ~ m1_subset_1(B_50,u1_struct_0(k2_yellow_1(A_46)))
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_56,plain,(
    ! [A_46,B_50,C_52] :
      ( r3_orders_2(k2_yellow_1(A_46),B_50,C_52)
      | ~ r1_tarski(B_50,C_52)
      | ~ m1_subset_1(C_52,A_46)
      | ~ m1_subset_1(B_50,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_40])).

tff(c_1039,plain,(
    ! [A_186,B_187,C_188] :
      ( k12_lattice3(A_186,B_187,C_188) = B_187
      | ~ r3_orders_2(A_186,B_187,C_188)
      | ~ m1_subset_1(C_188,u1_struct_0(A_186))
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_orders_2(A_186)
      | ~ v2_lattice3(A_186)
      | ~ v5_orders_2(A_186)
      | ~ v3_orders_2(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1041,plain,(
    ! [A_46,B_50,C_52] :
      ( k12_lattice3(k2_yellow_1(A_46),B_50,C_52) = B_50
      | ~ m1_subset_1(C_52,u1_struct_0(k2_yellow_1(A_46)))
      | ~ m1_subset_1(B_50,u1_struct_0(k2_yellow_1(A_46)))
      | ~ l1_orders_2(k2_yellow_1(A_46))
      | ~ v2_lattice3(k2_yellow_1(A_46))
      | ~ v5_orders_2(k2_yellow_1(A_46))
      | ~ v3_orders_2(k2_yellow_1(A_46))
      | ~ r1_tarski(B_50,C_52)
      | ~ m1_subset_1(C_52,A_46)
      | ~ m1_subset_1(B_50,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_56,c_1039])).

tff(c_1067,plain,(
    ! [A_196,B_197,C_198] :
      ( k12_lattice3(k2_yellow_1(A_196),B_197,C_198) = B_197
      | ~ v2_lattice3(k2_yellow_1(A_196))
      | ~ r1_tarski(B_197,C_198)
      | ~ m1_subset_1(C_198,A_196)
      | ~ m1_subset_1(B_197,A_196)
      | v1_xboole_0(A_196) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_26,c_36,c_36,c_1041])).

tff(c_1069,plain,(
    ! [B_197,C_198] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_197,C_198) = B_197
      | ~ r1_tarski(B_197,C_198)
      | ~ m1_subset_1(C_198,'#skF_1')
      | ~ m1_subset_1(B_197,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_1067])).

tff(c_1073,plain,(
    ! [B_199,C_200] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_199,C_200) = B_199
      | ~ r1_tarski(B_199,C_200)
      | ~ m1_subset_1(C_200,'#skF_1')
      | ~ m1_subset_1(B_199,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1069])).

tff(c_887,plain,(
    ! [A_167,B_168,C_169] :
      ( k12_lattice3(A_167,B_168,C_169) = k11_lattice3(A_167,B_168,C_169)
      | ~ m1_subset_1(C_169,u1_struct_0(A_167))
      | ~ m1_subset_1(B_168,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167)
      | ~ v2_lattice3(A_167)
      | ~ v5_orders_2(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_894,plain,(
    ! [A_45,B_168,C_169] :
      ( k12_lattice3(k2_yellow_1(A_45),B_168,C_169) = k11_lattice3(k2_yellow_1(A_45),B_168,C_169)
      | ~ m1_subset_1(C_169,A_45)
      | ~ m1_subset_1(B_168,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v2_lattice3(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_887])).

tff(c_899,plain,(
    ! [A_170,B_171,C_172] :
      ( k12_lattice3(k2_yellow_1(A_170),B_171,C_172) = k11_lattice3(k2_yellow_1(A_170),B_171,C_172)
      | ~ m1_subset_1(C_172,A_170)
      | ~ m1_subset_1(B_171,A_170)
      | ~ v2_lattice3(k2_yellow_1(A_170)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_36,c_894])).

tff(c_902,plain,(
    ! [B_171,C_172] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_171,C_172) = k11_lattice3(k2_yellow_1('#skF_1'),B_171,C_172)
      | ~ m1_subset_1(C_172,'#skF_1')
      | ~ m1_subset_1(B_171,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_899])).

tff(c_1170,plain,(
    ! [B_210,C_211] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_210,C_211) = B_210
      | ~ m1_subset_1(C_211,'#skF_1')
      | ~ m1_subset_1(B_210,'#skF_1')
      | ~ r1_tarski(B_210,C_211)
      | ~ m1_subset_1(C_211,'#skF_1')
      | ~ m1_subset_1(B_210,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1073,c_902])).

tff(c_912,plain,(
    ! [A_175,C_176,B_177] :
      ( k11_lattice3(A_175,C_176,B_177) = k11_lattice3(A_175,B_177,C_176)
      | ~ m1_subset_1(C_176,u1_struct_0(A_175))
      | ~ m1_subset_1(B_177,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | ~ v2_lattice3(A_175)
      | ~ v5_orders_2(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_919,plain,(
    ! [A_45,C_176,B_177] :
      ( k11_lattice3(k2_yellow_1(A_45),C_176,B_177) = k11_lattice3(k2_yellow_1(A_45),B_177,C_176)
      | ~ m1_subset_1(C_176,A_45)
      | ~ m1_subset_1(B_177,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v2_lattice3(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_912])).

tff(c_936,plain,(
    ! [A_181,C_182,B_183] :
      ( k11_lattice3(k2_yellow_1(A_181),C_182,B_183) = k11_lattice3(k2_yellow_1(A_181),B_183,C_182)
      | ~ m1_subset_1(C_182,A_181)
      | ~ m1_subset_1(B_183,A_181)
      | ~ v2_lattice3(k2_yellow_1(A_181)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_36,c_919])).

tff(c_939,plain,(
    ! [C_182,B_183] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_182,B_183) = k11_lattice3(k2_yellow_1('#skF_1'),B_183,C_182)
      | ~ m1_subset_1(C_182,'#skF_1')
      | ~ m1_subset_1(B_183,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_936])).

tff(c_1382,plain,(
    ! [C_225,B_226] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_225,B_226) = B_226
      | ~ m1_subset_1(C_225,'#skF_1')
      | ~ m1_subset_1(B_226,'#skF_1')
      | ~ m1_subset_1(C_225,'#skF_1')
      | ~ m1_subset_1(B_226,'#skF_1')
      | ~ r1_tarski(B_226,C_225)
      | ~ m1_subset_1(C_225,'#skF_1')
      | ~ m1_subset_1(B_226,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1170,c_939])).

tff(c_32,plain,(
    ! [A_44] : v4_orders_2(k2_yellow_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1045,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k11_lattice3(A_189,k11_lattice3(A_189,B_190,C_191),D_192) = k11_lattice3(A_189,B_190,k11_lattice3(A_189,C_191,D_192))
      | ~ v4_orders_2(A_189)
      | ~ m1_subset_1(D_192,u1_struct_0(A_189))
      | ~ m1_subset_1(C_191,u1_struct_0(A_189))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | ~ v2_lattice3(A_189)
      | ~ v5_orders_2(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1052,plain,(
    ! [A_45,B_190,C_191,D_192] :
      ( k11_lattice3(k2_yellow_1(A_45),k11_lattice3(k2_yellow_1(A_45),B_190,C_191),D_192) = k11_lattice3(k2_yellow_1(A_45),B_190,k11_lattice3(k2_yellow_1(A_45),C_191,D_192))
      | ~ v4_orders_2(k2_yellow_1(A_45))
      | ~ m1_subset_1(D_192,A_45)
      | ~ m1_subset_1(C_191,u1_struct_0(k2_yellow_1(A_45)))
      | ~ m1_subset_1(B_190,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v2_lattice3(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1045])).

tff(c_1056,plain,(
    ! [A_45,B_190,C_191,D_192] :
      ( k11_lattice3(k2_yellow_1(A_45),k11_lattice3(k2_yellow_1(A_45),B_190,C_191),D_192) = k11_lattice3(k2_yellow_1(A_45),B_190,k11_lattice3(k2_yellow_1(A_45),C_191,D_192))
      | ~ m1_subset_1(D_192,A_45)
      | ~ m1_subset_1(C_191,A_45)
      | ~ m1_subset_1(B_190,A_45)
      | ~ v2_lattice3(k2_yellow_1(A_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_36,c_36,c_32,c_1052])).

tff(c_1401,plain,(
    ! [C_225,B_226,D_192] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_225,k11_lattice3(k2_yellow_1('#skF_1'),B_226,D_192)) = k11_lattice3(k2_yellow_1('#skF_1'),B_226,D_192)
      | ~ m1_subset_1(D_192,'#skF_1')
      | ~ m1_subset_1(B_226,'#skF_1')
      | ~ m1_subset_1(C_225,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_225,'#skF_1')
      | ~ m1_subset_1(B_226,'#skF_1')
      | ~ m1_subset_1(C_225,'#skF_1')
      | ~ m1_subset_1(B_226,'#skF_1')
      | ~ r1_tarski(B_226,C_225)
      | ~ m1_subset_1(C_225,'#skF_1')
      | ~ m1_subset_1(B_226,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1382,c_1056])).

tff(c_1496,plain,(
    ! [C_227,B_228,D_229] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_227,k11_lattice3(k2_yellow_1('#skF_1'),B_228,D_229)) = k11_lattice3(k2_yellow_1('#skF_1'),B_228,D_229)
      | ~ m1_subset_1(D_229,'#skF_1')
      | ~ r1_tarski(B_228,C_227)
      | ~ m1_subset_1(C_227,'#skF_1')
      | ~ m1_subset_1(B_228,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1401])).

tff(c_924,plain,(
    ! [A_178,B_179,C_180] :
      ( r3_orders_2(A_178,B_179,C_180)
      | k12_lattice3(A_178,B_179,C_180) != B_179
      | ~ m1_subset_1(C_180,u1_struct_0(A_178))
      | ~ m1_subset_1(B_179,u1_struct_0(A_178))
      | ~ l1_orders_2(A_178)
      | ~ v2_lattice3(A_178)
      | ~ v5_orders_2(A_178)
      | ~ v3_orders_2(A_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_931,plain,(
    ! [A_45,B_179,C_180] :
      ( r3_orders_2(k2_yellow_1(A_45),B_179,C_180)
      | k12_lattice3(k2_yellow_1(A_45),B_179,C_180) != B_179
      | ~ m1_subset_1(C_180,A_45)
      | ~ m1_subset_1(B_179,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v2_lattice3(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45))
      | ~ v3_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_924])).

tff(c_1057,plain,(
    ! [A_193,B_194,C_195] :
      ( r3_orders_2(k2_yellow_1(A_193),B_194,C_195)
      | k12_lattice3(k2_yellow_1(A_193),B_194,C_195) != B_194
      | ~ m1_subset_1(C_195,A_193)
      | ~ m1_subset_1(B_194,A_193)
      | ~ v2_lattice3(k2_yellow_1(A_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_26,c_36,c_931])).

tff(c_42,plain,(
    ! [B_50,C_52,A_46] :
      ( r1_tarski(B_50,C_52)
      | ~ r3_orders_2(k2_yellow_1(A_46),B_50,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(k2_yellow_1(A_46)))
      | ~ m1_subset_1(B_50,u1_struct_0(k2_yellow_1(A_46)))
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_55,plain,(
    ! [B_50,C_52,A_46] :
      ( r1_tarski(B_50,C_52)
      | ~ r3_orders_2(k2_yellow_1(A_46),B_50,C_52)
      | ~ m1_subset_1(C_52,A_46)
      | ~ m1_subset_1(B_50,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_42])).

tff(c_1088,plain,(
    ! [B_201,C_202,A_203] :
      ( r1_tarski(B_201,C_202)
      | v1_xboole_0(A_203)
      | k12_lattice3(k2_yellow_1(A_203),B_201,C_202) != B_201
      | ~ m1_subset_1(C_202,A_203)
      | ~ m1_subset_1(B_201,A_203)
      | ~ v2_lattice3(k2_yellow_1(A_203)) ) ),
    inference(resolution,[status(thm)],[c_1057,c_55])).

tff(c_1092,plain,(
    ! [B_171,C_172] :
      ( r1_tarski(B_171,C_172)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_171,C_172) != B_171
      | ~ m1_subset_1(C_172,'#skF_1')
      | ~ m1_subset_1(B_171,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_172,'#skF_1')
      | ~ m1_subset_1(B_171,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_902,c_1088])).

tff(c_1098,plain,(
    ! [B_171,C_172] :
      ( r1_tarski(B_171,C_172)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_171,C_172) != B_171
      | ~ m1_subset_1(C_172,'#skF_1')
      | ~ m1_subset_1(B_171,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1092])).

tff(c_1100,plain,(
    ! [B_204,C_205] :
      ( r1_tarski(B_204,C_205)
      | k11_lattice3(k2_yellow_1('#skF_1'),B_204,C_205) != B_204
      | ~ m1_subset_1(C_205,'#skF_1')
      | ~ m1_subset_1(B_204,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1098])).

tff(c_1103,plain,(
    ! [B_183,C_182] :
      ( r1_tarski(B_183,C_182)
      | k11_lattice3(k2_yellow_1('#skF_1'),C_182,B_183) != B_183
      | ~ m1_subset_1(C_182,'#skF_1')
      | ~ m1_subset_1(B_183,'#skF_1')
      | ~ m1_subset_1(C_182,'#skF_1')
      | ~ m1_subset_1(B_183,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_939,c_1100])).

tff(c_1604,plain,(
    ! [B_230,D_231,C_232] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),B_230,D_231),C_232)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),B_230,D_231),'#skF_1')
      | ~ m1_subset_1(D_231,'#skF_1')
      | ~ r1_tarski(B_230,C_232)
      | ~ m1_subset_1(C_232,'#skF_1')
      | ~ m1_subset_1(B_230,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_1103])).

tff(c_940,plain,(
    ! [C_184,B_185] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_184,B_185) = k11_lattice3(k2_yellow_1('#skF_1'),B_185,C_184)
      | ~ m1_subset_1(C_184,'#skF_1')
      | ~ m1_subset_1(B_185,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_936])).

tff(c_120,plain,(
    ! [A_75,B_76,C_77] :
      ( m1_subset_1(k11_lattice3(A_75,B_76,C_77),u1_struct_0(A_75))
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_123,plain,(
    ! [A_45,B_76,C_77] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_45),B_76,C_77),A_45)
      | ~ m1_subset_1(C_77,u1_struct_0(k2_yellow_1(A_45)))
      | ~ m1_subset_1(B_76,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_120])).

tff(c_125,plain,(
    ! [A_45,B_76,C_77] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_45),B_76,C_77),A_45)
      | ~ m1_subset_1(C_77,A_45)
      | ~ m1_subset_1(B_76,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36,c_36,c_123])).

tff(c_247,plain,(
    ! [A_103,B_104,C_105] :
      ( k12_lattice3(A_103,B_104,C_105) = B_104
      | ~ r3_orders_2(A_103,B_104,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v2_lattice3(A_103)
      | ~ v5_orders_2(A_103)
      | ~ v3_orders_2(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_249,plain,(
    ! [A_46,B_50,C_52] :
      ( k12_lattice3(k2_yellow_1(A_46),B_50,C_52) = B_50
      | ~ m1_subset_1(C_52,u1_struct_0(k2_yellow_1(A_46)))
      | ~ m1_subset_1(B_50,u1_struct_0(k2_yellow_1(A_46)))
      | ~ l1_orders_2(k2_yellow_1(A_46))
      | ~ v2_lattice3(k2_yellow_1(A_46))
      | ~ v5_orders_2(k2_yellow_1(A_46))
      | ~ v3_orders_2(k2_yellow_1(A_46))
      | ~ r1_tarski(B_50,C_52)
      | ~ m1_subset_1(C_52,A_46)
      | ~ m1_subset_1(B_50,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_56,c_247])).

tff(c_265,plain,(
    ! [A_109,B_110,C_111] :
      ( k12_lattice3(k2_yellow_1(A_109),B_110,C_111) = B_110
      | ~ v2_lattice3(k2_yellow_1(A_109))
      | ~ r1_tarski(B_110,C_111)
      | ~ m1_subset_1(C_111,A_109)
      | ~ m1_subset_1(B_110,A_109)
      | v1_xboole_0(A_109) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_26,c_36,c_36,c_249])).

tff(c_267,plain,(
    ! [B_110,C_111] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_110,C_111) = B_110
      | ~ r1_tarski(B_110,C_111)
      | ~ m1_subset_1(C_111,'#skF_1')
      | ~ m1_subset_1(B_110,'#skF_1')
      | v1_xboole_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_265])).

tff(c_271,plain,(
    ! [B_112,C_113] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_112,C_113) = B_112
      | ~ r1_tarski(B_112,C_113)
      | ~ m1_subset_1(C_113,'#skF_1')
      | ~ m1_subset_1(B_112,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_267])).

tff(c_133,plain,(
    ! [A_87,B_88,C_89] :
      ( k12_lattice3(A_87,B_88,C_89) = k11_lattice3(A_87,B_88,C_89)
      | ~ m1_subset_1(C_89,u1_struct_0(A_87))
      | ~ m1_subset_1(B_88,u1_struct_0(A_87))
      | ~ l1_orders_2(A_87)
      | ~ v2_lattice3(A_87)
      | ~ v5_orders_2(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_140,plain,(
    ! [A_45,B_88,C_89] :
      ( k12_lattice3(k2_yellow_1(A_45),B_88,C_89) = k11_lattice3(k2_yellow_1(A_45),B_88,C_89)
      | ~ m1_subset_1(C_89,A_45)
      | ~ m1_subset_1(B_88,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v2_lattice3(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_133])).

tff(c_145,plain,(
    ! [A_90,B_91,C_92] :
      ( k12_lattice3(k2_yellow_1(A_90),B_91,C_92) = k11_lattice3(k2_yellow_1(A_90),B_91,C_92)
      | ~ m1_subset_1(C_92,A_90)
      | ~ m1_subset_1(B_91,A_90)
      | ~ v2_lattice3(k2_yellow_1(A_90)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_36,c_140])).

tff(c_148,plain,(
    ! [B_91,C_92] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_91,C_92) = k11_lattice3(k2_yellow_1('#skF_1'),B_91,C_92)
      | ~ m1_subset_1(C_92,'#skF_1')
      | ~ m1_subset_1(B_91,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_145])).

tff(c_296,plain,(
    ! [B_117,C_118] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_117,C_118) = B_117
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1')
      | ~ r1_tarski(B_117,C_118)
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_148])).

tff(c_149,plain,(
    ! [A_93,C_94,B_95] :
      ( k11_lattice3(A_93,C_94,B_95) = k11_lattice3(A_93,B_95,C_94)
      | ~ m1_subset_1(C_94,u1_struct_0(A_93))
      | ~ m1_subset_1(B_95,u1_struct_0(A_93))
      | ~ l1_orders_2(A_93)
      | ~ v2_lattice3(A_93)
      | ~ v5_orders_2(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_156,plain,(
    ! [A_45,C_94,B_95] :
      ( k11_lattice3(k2_yellow_1(A_45),C_94,B_95) = k11_lattice3(k2_yellow_1(A_45),B_95,C_94)
      | ~ m1_subset_1(C_94,A_45)
      | ~ m1_subset_1(B_95,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v2_lattice3(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_149])).

tff(c_170,plain,(
    ! [A_98,C_99,B_100] :
      ( k11_lattice3(k2_yellow_1(A_98),C_99,B_100) = k11_lattice3(k2_yellow_1(A_98),B_100,C_99)
      | ~ m1_subset_1(C_99,A_98)
      | ~ m1_subset_1(B_100,A_98)
      | ~ v2_lattice3(k2_yellow_1(A_98)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_36,c_156])).

tff(c_173,plain,(
    ! [C_99,B_100] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_99,B_100) = k11_lattice3(k2_yellow_1('#skF_1'),B_100,C_99)
      | ~ m1_subset_1(C_99,'#skF_1')
      | ~ m1_subset_1(B_100,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_50,c_170])).

tff(c_308,plain,(
    ! [C_118,B_117] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_118,B_117) = B_117
      | ~ m1_subset_1(B_117,'#skF_1')
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1')
      | ~ r1_tarski(B_117,C_118)
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_173])).

tff(c_357,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k11_lattice3(A_122,k11_lattice3(A_122,B_123,C_124),D_125) = k11_lattice3(A_122,B_123,k11_lattice3(A_122,C_124,D_125))
      | ~ v4_orders_2(A_122)
      | ~ m1_subset_1(D_125,u1_struct_0(A_122))
      | ~ m1_subset_1(C_124,u1_struct_0(A_122))
      | ~ m1_subset_1(B_123,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v2_lattice3(A_122)
      | ~ v5_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_364,plain,(
    ! [A_45,B_123,C_124,D_125] :
      ( k11_lattice3(k2_yellow_1(A_45),k11_lattice3(k2_yellow_1(A_45),B_123,C_124),D_125) = k11_lattice3(k2_yellow_1(A_45),B_123,k11_lattice3(k2_yellow_1(A_45),C_124,D_125))
      | ~ v4_orders_2(k2_yellow_1(A_45))
      | ~ m1_subset_1(D_125,A_45)
      | ~ m1_subset_1(C_124,u1_struct_0(k2_yellow_1(A_45)))
      | ~ m1_subset_1(B_123,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v2_lattice3(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_357])).

tff(c_472,plain,(
    ! [A_139,B_140,C_141,D_142] :
      ( k11_lattice3(k2_yellow_1(A_139),k11_lattice3(k2_yellow_1(A_139),B_140,C_141),D_142) = k11_lattice3(k2_yellow_1(A_139),B_140,k11_lattice3(k2_yellow_1(A_139),C_141,D_142))
      | ~ m1_subset_1(D_142,A_139)
      | ~ m1_subset_1(C_141,A_139)
      | ~ m1_subset_1(B_140,A_139)
      | ~ v2_lattice3(k2_yellow_1(A_139)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_26,c_36,c_36,c_32,c_364])).

tff(c_517,plain,(
    ! [C_118,B_117,D_142] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_118,k11_lattice3(k2_yellow_1('#skF_1'),B_117,D_142)) = k11_lattice3(k2_yellow_1('#skF_1'),B_117,D_142)
      | ~ m1_subset_1(D_142,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1')
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_117,'#skF_1')
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1')
      | ~ r1_tarski(B_117,C_118)
      | ~ m1_subset_1(C_118,'#skF_1')
      | ~ m1_subset_1(B_117,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_472])).

tff(c_668,plain,(
    ! [C_146,B_147,D_148] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_146,k11_lattice3(k2_yellow_1('#skF_1'),B_147,D_148)) = k11_lattice3(k2_yellow_1('#skF_1'),B_147,D_148)
      | ~ m1_subset_1(D_148,'#skF_1')
      | ~ r1_tarski(B_147,C_146)
      | ~ m1_subset_1(C_146,'#skF_1')
      | ~ m1_subset_1(B_147,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_517])).

tff(c_253,plain,(
    ! [A_106,B_107,C_108] :
      ( r3_orders_2(A_106,B_107,C_108)
      | k12_lattice3(A_106,B_107,C_108) != B_107
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v2_lattice3(A_106)
      | ~ v5_orders_2(A_106)
      | ~ v3_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_260,plain,(
    ! [A_45,B_107,C_108] :
      ( r3_orders_2(k2_yellow_1(A_45),B_107,C_108)
      | k12_lattice3(k2_yellow_1(A_45),B_107,C_108) != B_107
      | ~ m1_subset_1(C_108,A_45)
      | ~ m1_subset_1(B_107,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v2_lattice3(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45))
      | ~ v3_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_253])).

tff(c_286,plain,(
    ! [A_114,B_115,C_116] :
      ( r3_orders_2(k2_yellow_1(A_114),B_115,C_116)
      | k12_lattice3(k2_yellow_1(A_114),B_115,C_116) != B_115
      | ~ m1_subset_1(C_116,A_114)
      | ~ m1_subset_1(B_115,A_114)
      | ~ v2_lattice3(k2_yellow_1(A_114)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34,c_26,c_36,c_260])).

tff(c_345,plain,(
    ! [B_119,C_120,A_121] :
      ( r1_tarski(B_119,C_120)
      | v1_xboole_0(A_121)
      | k12_lattice3(k2_yellow_1(A_121),B_119,C_120) != B_119
      | ~ m1_subset_1(C_120,A_121)
      | ~ m1_subset_1(B_119,A_121)
      | ~ v2_lattice3(k2_yellow_1(A_121)) ) ),
    inference(resolution,[status(thm)],[c_286,c_55])).

tff(c_349,plain,(
    ! [B_91,C_92] :
      ( r1_tarski(B_91,C_92)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_91,C_92) != B_91
      | ~ m1_subset_1(C_92,'#skF_1')
      | ~ m1_subset_1(B_91,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_92,'#skF_1')
      | ~ m1_subset_1(B_91,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_345])).

tff(c_355,plain,(
    ! [B_91,C_92] :
      ( r1_tarski(B_91,C_92)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_91,C_92) != B_91
      | ~ m1_subset_1(C_92,'#skF_1')
      | ~ m1_subset_1(B_91,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_349])).

tff(c_369,plain,(
    ! [B_126,C_127] :
      ( r1_tarski(B_126,C_127)
      | k11_lattice3(k2_yellow_1('#skF_1'),B_126,C_127) != B_126
      | ~ m1_subset_1(C_127,'#skF_1')
      | ~ m1_subset_1(B_126,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_355])).

tff(c_375,plain,(
    ! [B_100,C_99] :
      ( r1_tarski(B_100,C_99)
      | k11_lattice3(k2_yellow_1('#skF_1'),C_99,B_100) != B_100
      | ~ m1_subset_1(C_99,'#skF_1')
      | ~ m1_subset_1(B_100,'#skF_1')
      | ~ m1_subset_1(C_99,'#skF_1')
      | ~ m1_subset_1(B_100,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_369])).

tff(c_776,plain,(
    ! [B_149,D_150,C_151] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),B_149,D_150),C_151)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),B_149,D_150),'#skF_1')
      | ~ m1_subset_1(D_150,'#skF_1')
      | ~ r1_tarski(B_149,C_151)
      | ~ m1_subset_1(C_151,'#skF_1')
      | ~ m1_subset_1(B_149,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_668,c_375])).

tff(c_99,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k3_xboole_0(B_70,C_71))
      | ~ r1_tarski(A_69,C_71)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_106,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_99,c_44])).

tff(c_107,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_106])).

tff(c_785,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_776,c_107])).

tff(c_821,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_6,c_54,c_785])).

tff(c_843,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_125,c_821])).

tff(c_855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_54,c_843])).

tff(c_856,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_106])).

tff(c_982,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_940,c_856])).

tff(c_1020,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53,c_982])).

tff(c_1607,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_3','#skF_3')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1604,c_1020])).

tff(c_1643,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6,c_53,c_1607])).

tff(c_1664,plain,
    ( ~ m1_subset_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_885,c_1643])).

tff(c_1672,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_53,c_1664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:46:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.87  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.88  
% 4.45/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.88  %$ r3_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.45/1.88  
% 4.45/1.88  %Foreground sorts:
% 4.45/1.88  
% 4.45/1.88  
% 4.45/1.88  %Background operators:
% 4.45/1.88  
% 4.45/1.88  
% 4.45/1.88  %Foreground operators:
% 4.45/1.88  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.45/1.88  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.45/1.88  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.45/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.88  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.45/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.88  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.45/1.88  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.45/1.88  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.45/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.88  tff('#skF_3', type, '#skF_3': $i).
% 4.45/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.88  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.45/1.88  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.45/1.88  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.45/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.88  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.45/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.88  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.45/1.88  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.45/1.88  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.45/1.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.45/1.88  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.88  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.45/1.88  
% 4.45/1.91  tff(f_126, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 4.45/1.91  tff(f_153, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 4.45/1.91  tff(f_114, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.45/1.91  tff(f_47, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 4.45/1.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.45/1.91  tff(f_122, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.45/1.91  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.45/1.91  tff(f_110, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k12_lattice3(A, B, C)) <=> r3_orders_2(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_0)).
% 4.45/1.91  tff(f_59, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.45/1.91  tff(f_73, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 4.45/1.91  tff(f_92, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (v4_orders_2(A) => (k11_lattice3(A, k11_lattice3(A, B, C), D) = k11_lattice3(A, B, k11_lattice3(A, C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_lattice3)).
% 4.45/1.91  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.45/1.91  tff(c_36, plain, (![A_45]: (u1_struct_0(k2_yellow_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_126])).
% 4.45/1.91  tff(c_46, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.45/1.91  tff(c_54, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46])).
% 4.45/1.91  tff(c_48, plain, (m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.45/1.91  tff(c_53, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_48])).
% 4.45/1.91  tff(c_26, plain, (![A_43]: (l1_orders_2(k2_yellow_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.45/1.91  tff(c_880, plain, (![A_161, B_162, C_163]: (m1_subset_1(k11_lattice3(A_161, B_162, C_163), u1_struct_0(A_161)) | ~m1_subset_1(C_163, u1_struct_0(A_161)) | ~m1_subset_1(B_162, u1_struct_0(A_161)) | ~l1_orders_2(A_161))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.45/1.91  tff(c_883, plain, (![A_45, B_162, C_163]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_45), B_162, C_163), A_45) | ~m1_subset_1(C_163, u1_struct_0(k2_yellow_1(A_45))) | ~m1_subset_1(B_162, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_880])).
% 4.45/1.91  tff(c_885, plain, (![A_45, B_162, C_163]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_45), B_162, C_163), A_45) | ~m1_subset_1(C_163, A_45) | ~m1_subset_1(B_162, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_36, c_883])).
% 4.45/1.91  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.45/1.91  tff(c_50, plain, (v2_lattice3(k2_yellow_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.45/1.91  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.45/1.91  tff(c_30, plain, (![A_44]: (v3_orders_2(k2_yellow_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.45/1.91  tff(c_34, plain, (![A_44]: (v5_orders_2(k2_yellow_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.45/1.91  tff(c_40, plain, (![A_46, B_50, C_52]: (r3_orders_2(k2_yellow_1(A_46), B_50, C_52) | ~r1_tarski(B_50, C_52) | ~m1_subset_1(C_52, u1_struct_0(k2_yellow_1(A_46))) | ~m1_subset_1(B_50, u1_struct_0(k2_yellow_1(A_46))) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.45/1.91  tff(c_56, plain, (![A_46, B_50, C_52]: (r3_orders_2(k2_yellow_1(A_46), B_50, C_52) | ~r1_tarski(B_50, C_52) | ~m1_subset_1(C_52, A_46) | ~m1_subset_1(B_50, A_46) | v1_xboole_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_40])).
% 4.45/1.91  tff(c_1039, plain, (![A_186, B_187, C_188]: (k12_lattice3(A_186, B_187, C_188)=B_187 | ~r3_orders_2(A_186, B_187, C_188) | ~m1_subset_1(C_188, u1_struct_0(A_186)) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_orders_2(A_186) | ~v2_lattice3(A_186) | ~v5_orders_2(A_186) | ~v3_orders_2(A_186))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.45/1.91  tff(c_1041, plain, (![A_46, B_50, C_52]: (k12_lattice3(k2_yellow_1(A_46), B_50, C_52)=B_50 | ~m1_subset_1(C_52, u1_struct_0(k2_yellow_1(A_46))) | ~m1_subset_1(B_50, u1_struct_0(k2_yellow_1(A_46))) | ~l1_orders_2(k2_yellow_1(A_46)) | ~v2_lattice3(k2_yellow_1(A_46)) | ~v5_orders_2(k2_yellow_1(A_46)) | ~v3_orders_2(k2_yellow_1(A_46)) | ~r1_tarski(B_50, C_52) | ~m1_subset_1(C_52, A_46) | ~m1_subset_1(B_50, A_46) | v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_56, c_1039])).
% 4.45/1.91  tff(c_1067, plain, (![A_196, B_197, C_198]: (k12_lattice3(k2_yellow_1(A_196), B_197, C_198)=B_197 | ~v2_lattice3(k2_yellow_1(A_196)) | ~r1_tarski(B_197, C_198) | ~m1_subset_1(C_198, A_196) | ~m1_subset_1(B_197, A_196) | v1_xboole_0(A_196))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_26, c_36, c_36, c_1041])).
% 4.45/1.91  tff(c_1069, plain, (![B_197, C_198]: (k12_lattice3(k2_yellow_1('#skF_1'), B_197, C_198)=B_197 | ~r1_tarski(B_197, C_198) | ~m1_subset_1(C_198, '#skF_1') | ~m1_subset_1(B_197, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_1067])).
% 4.45/1.91  tff(c_1073, plain, (![B_199, C_200]: (k12_lattice3(k2_yellow_1('#skF_1'), B_199, C_200)=B_199 | ~r1_tarski(B_199, C_200) | ~m1_subset_1(C_200, '#skF_1') | ~m1_subset_1(B_199, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1069])).
% 4.45/1.91  tff(c_887, plain, (![A_167, B_168, C_169]: (k12_lattice3(A_167, B_168, C_169)=k11_lattice3(A_167, B_168, C_169) | ~m1_subset_1(C_169, u1_struct_0(A_167)) | ~m1_subset_1(B_168, u1_struct_0(A_167)) | ~l1_orders_2(A_167) | ~v2_lattice3(A_167) | ~v5_orders_2(A_167))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.45/1.91  tff(c_894, plain, (![A_45, B_168, C_169]: (k12_lattice3(k2_yellow_1(A_45), B_168, C_169)=k11_lattice3(k2_yellow_1(A_45), B_168, C_169) | ~m1_subset_1(C_169, A_45) | ~m1_subset_1(B_168, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v2_lattice3(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_887])).
% 4.45/1.91  tff(c_899, plain, (![A_170, B_171, C_172]: (k12_lattice3(k2_yellow_1(A_170), B_171, C_172)=k11_lattice3(k2_yellow_1(A_170), B_171, C_172) | ~m1_subset_1(C_172, A_170) | ~m1_subset_1(B_171, A_170) | ~v2_lattice3(k2_yellow_1(A_170)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_36, c_894])).
% 4.45/1.91  tff(c_902, plain, (![B_171, C_172]: (k12_lattice3(k2_yellow_1('#skF_1'), B_171, C_172)=k11_lattice3(k2_yellow_1('#skF_1'), B_171, C_172) | ~m1_subset_1(C_172, '#skF_1') | ~m1_subset_1(B_171, '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_899])).
% 4.45/1.91  tff(c_1170, plain, (![B_210, C_211]: (k11_lattice3(k2_yellow_1('#skF_1'), B_210, C_211)=B_210 | ~m1_subset_1(C_211, '#skF_1') | ~m1_subset_1(B_210, '#skF_1') | ~r1_tarski(B_210, C_211) | ~m1_subset_1(C_211, '#skF_1') | ~m1_subset_1(B_210, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1073, c_902])).
% 4.45/1.91  tff(c_912, plain, (![A_175, C_176, B_177]: (k11_lattice3(A_175, C_176, B_177)=k11_lattice3(A_175, B_177, C_176) | ~m1_subset_1(C_176, u1_struct_0(A_175)) | ~m1_subset_1(B_177, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | ~v2_lattice3(A_175) | ~v5_orders_2(A_175))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.45/1.91  tff(c_919, plain, (![A_45, C_176, B_177]: (k11_lattice3(k2_yellow_1(A_45), C_176, B_177)=k11_lattice3(k2_yellow_1(A_45), B_177, C_176) | ~m1_subset_1(C_176, A_45) | ~m1_subset_1(B_177, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v2_lattice3(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_912])).
% 4.45/1.91  tff(c_936, plain, (![A_181, C_182, B_183]: (k11_lattice3(k2_yellow_1(A_181), C_182, B_183)=k11_lattice3(k2_yellow_1(A_181), B_183, C_182) | ~m1_subset_1(C_182, A_181) | ~m1_subset_1(B_183, A_181) | ~v2_lattice3(k2_yellow_1(A_181)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_36, c_919])).
% 4.45/1.91  tff(c_939, plain, (![C_182, B_183]: (k11_lattice3(k2_yellow_1('#skF_1'), C_182, B_183)=k11_lattice3(k2_yellow_1('#skF_1'), B_183, C_182) | ~m1_subset_1(C_182, '#skF_1') | ~m1_subset_1(B_183, '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_936])).
% 4.45/1.91  tff(c_1382, plain, (![C_225, B_226]: (k11_lattice3(k2_yellow_1('#skF_1'), C_225, B_226)=B_226 | ~m1_subset_1(C_225, '#skF_1') | ~m1_subset_1(B_226, '#skF_1') | ~m1_subset_1(C_225, '#skF_1') | ~m1_subset_1(B_226, '#skF_1') | ~r1_tarski(B_226, C_225) | ~m1_subset_1(C_225, '#skF_1') | ~m1_subset_1(B_226, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1170, c_939])).
% 4.45/1.91  tff(c_32, plain, (![A_44]: (v4_orders_2(k2_yellow_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.45/1.91  tff(c_1045, plain, (![A_189, B_190, C_191, D_192]: (k11_lattice3(A_189, k11_lattice3(A_189, B_190, C_191), D_192)=k11_lattice3(A_189, B_190, k11_lattice3(A_189, C_191, D_192)) | ~v4_orders_2(A_189) | ~m1_subset_1(D_192, u1_struct_0(A_189)) | ~m1_subset_1(C_191, u1_struct_0(A_189)) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l1_orders_2(A_189) | ~v2_lattice3(A_189) | ~v5_orders_2(A_189))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.45/1.91  tff(c_1052, plain, (![A_45, B_190, C_191, D_192]: (k11_lattice3(k2_yellow_1(A_45), k11_lattice3(k2_yellow_1(A_45), B_190, C_191), D_192)=k11_lattice3(k2_yellow_1(A_45), B_190, k11_lattice3(k2_yellow_1(A_45), C_191, D_192)) | ~v4_orders_2(k2_yellow_1(A_45)) | ~m1_subset_1(D_192, A_45) | ~m1_subset_1(C_191, u1_struct_0(k2_yellow_1(A_45))) | ~m1_subset_1(B_190, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v2_lattice3(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1045])).
% 4.45/1.91  tff(c_1056, plain, (![A_45, B_190, C_191, D_192]: (k11_lattice3(k2_yellow_1(A_45), k11_lattice3(k2_yellow_1(A_45), B_190, C_191), D_192)=k11_lattice3(k2_yellow_1(A_45), B_190, k11_lattice3(k2_yellow_1(A_45), C_191, D_192)) | ~m1_subset_1(D_192, A_45) | ~m1_subset_1(C_191, A_45) | ~m1_subset_1(B_190, A_45) | ~v2_lattice3(k2_yellow_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_36, c_36, c_32, c_1052])).
% 4.45/1.91  tff(c_1401, plain, (![C_225, B_226, D_192]: (k11_lattice3(k2_yellow_1('#skF_1'), C_225, k11_lattice3(k2_yellow_1('#skF_1'), B_226, D_192))=k11_lattice3(k2_yellow_1('#skF_1'), B_226, D_192) | ~m1_subset_1(D_192, '#skF_1') | ~m1_subset_1(B_226, '#skF_1') | ~m1_subset_1(C_225, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_225, '#skF_1') | ~m1_subset_1(B_226, '#skF_1') | ~m1_subset_1(C_225, '#skF_1') | ~m1_subset_1(B_226, '#skF_1') | ~r1_tarski(B_226, C_225) | ~m1_subset_1(C_225, '#skF_1') | ~m1_subset_1(B_226, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1382, c_1056])).
% 4.45/1.91  tff(c_1496, plain, (![C_227, B_228, D_229]: (k11_lattice3(k2_yellow_1('#skF_1'), C_227, k11_lattice3(k2_yellow_1('#skF_1'), B_228, D_229))=k11_lattice3(k2_yellow_1('#skF_1'), B_228, D_229) | ~m1_subset_1(D_229, '#skF_1') | ~r1_tarski(B_228, C_227) | ~m1_subset_1(C_227, '#skF_1') | ~m1_subset_1(B_228, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1401])).
% 4.45/1.91  tff(c_924, plain, (![A_178, B_179, C_180]: (r3_orders_2(A_178, B_179, C_180) | k12_lattice3(A_178, B_179, C_180)!=B_179 | ~m1_subset_1(C_180, u1_struct_0(A_178)) | ~m1_subset_1(B_179, u1_struct_0(A_178)) | ~l1_orders_2(A_178) | ~v2_lattice3(A_178) | ~v5_orders_2(A_178) | ~v3_orders_2(A_178))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.45/1.91  tff(c_931, plain, (![A_45, B_179, C_180]: (r3_orders_2(k2_yellow_1(A_45), B_179, C_180) | k12_lattice3(k2_yellow_1(A_45), B_179, C_180)!=B_179 | ~m1_subset_1(C_180, A_45) | ~m1_subset_1(B_179, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v2_lattice3(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)) | ~v3_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_924])).
% 4.45/1.91  tff(c_1057, plain, (![A_193, B_194, C_195]: (r3_orders_2(k2_yellow_1(A_193), B_194, C_195) | k12_lattice3(k2_yellow_1(A_193), B_194, C_195)!=B_194 | ~m1_subset_1(C_195, A_193) | ~m1_subset_1(B_194, A_193) | ~v2_lattice3(k2_yellow_1(A_193)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_26, c_36, c_931])).
% 4.45/1.91  tff(c_42, plain, (![B_50, C_52, A_46]: (r1_tarski(B_50, C_52) | ~r3_orders_2(k2_yellow_1(A_46), B_50, C_52) | ~m1_subset_1(C_52, u1_struct_0(k2_yellow_1(A_46))) | ~m1_subset_1(B_50, u1_struct_0(k2_yellow_1(A_46))) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.45/1.91  tff(c_55, plain, (![B_50, C_52, A_46]: (r1_tarski(B_50, C_52) | ~r3_orders_2(k2_yellow_1(A_46), B_50, C_52) | ~m1_subset_1(C_52, A_46) | ~m1_subset_1(B_50, A_46) | v1_xboole_0(A_46))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_42])).
% 4.45/1.91  tff(c_1088, plain, (![B_201, C_202, A_203]: (r1_tarski(B_201, C_202) | v1_xboole_0(A_203) | k12_lattice3(k2_yellow_1(A_203), B_201, C_202)!=B_201 | ~m1_subset_1(C_202, A_203) | ~m1_subset_1(B_201, A_203) | ~v2_lattice3(k2_yellow_1(A_203)))), inference(resolution, [status(thm)], [c_1057, c_55])).
% 4.45/1.91  tff(c_1092, plain, (![B_171, C_172]: (r1_tarski(B_171, C_172) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_171, C_172)!=B_171 | ~m1_subset_1(C_172, '#skF_1') | ~m1_subset_1(B_171, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_172, '#skF_1') | ~m1_subset_1(B_171, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_902, c_1088])).
% 4.45/1.91  tff(c_1098, plain, (![B_171, C_172]: (r1_tarski(B_171, C_172) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_171, C_172)!=B_171 | ~m1_subset_1(C_172, '#skF_1') | ~m1_subset_1(B_171, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1092])).
% 4.45/1.91  tff(c_1100, plain, (![B_204, C_205]: (r1_tarski(B_204, C_205) | k11_lattice3(k2_yellow_1('#skF_1'), B_204, C_205)!=B_204 | ~m1_subset_1(C_205, '#skF_1') | ~m1_subset_1(B_204, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_52, c_1098])).
% 4.45/1.91  tff(c_1103, plain, (![B_183, C_182]: (r1_tarski(B_183, C_182) | k11_lattice3(k2_yellow_1('#skF_1'), C_182, B_183)!=B_183 | ~m1_subset_1(C_182, '#skF_1') | ~m1_subset_1(B_183, '#skF_1') | ~m1_subset_1(C_182, '#skF_1') | ~m1_subset_1(B_183, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_939, c_1100])).
% 4.45/1.91  tff(c_1604, plain, (![B_230, D_231, C_232]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), B_230, D_231), C_232) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), B_230, D_231), '#skF_1') | ~m1_subset_1(D_231, '#skF_1') | ~r1_tarski(B_230, C_232) | ~m1_subset_1(C_232, '#skF_1') | ~m1_subset_1(B_230, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1496, c_1103])).
% 4.45/1.91  tff(c_940, plain, (![C_184, B_185]: (k11_lattice3(k2_yellow_1('#skF_1'), C_184, B_185)=k11_lattice3(k2_yellow_1('#skF_1'), B_185, C_184) | ~m1_subset_1(C_184, '#skF_1') | ~m1_subset_1(B_185, '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_936])).
% 4.45/1.91  tff(c_120, plain, (![A_75, B_76, C_77]: (m1_subset_1(k11_lattice3(A_75, B_76, C_77), u1_struct_0(A_75)) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.45/1.91  tff(c_123, plain, (![A_45, B_76, C_77]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_45), B_76, C_77), A_45) | ~m1_subset_1(C_77, u1_struct_0(k2_yellow_1(A_45))) | ~m1_subset_1(B_76, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_120])).
% 4.45/1.91  tff(c_125, plain, (![A_45, B_76, C_77]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_45), B_76, C_77), A_45) | ~m1_subset_1(C_77, A_45) | ~m1_subset_1(B_76, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36, c_36, c_123])).
% 4.45/1.91  tff(c_247, plain, (![A_103, B_104, C_105]: (k12_lattice3(A_103, B_104, C_105)=B_104 | ~r3_orders_2(A_103, B_104, C_105) | ~m1_subset_1(C_105, u1_struct_0(A_103)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v2_lattice3(A_103) | ~v5_orders_2(A_103) | ~v3_orders_2(A_103))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.45/1.91  tff(c_249, plain, (![A_46, B_50, C_52]: (k12_lattice3(k2_yellow_1(A_46), B_50, C_52)=B_50 | ~m1_subset_1(C_52, u1_struct_0(k2_yellow_1(A_46))) | ~m1_subset_1(B_50, u1_struct_0(k2_yellow_1(A_46))) | ~l1_orders_2(k2_yellow_1(A_46)) | ~v2_lattice3(k2_yellow_1(A_46)) | ~v5_orders_2(k2_yellow_1(A_46)) | ~v3_orders_2(k2_yellow_1(A_46)) | ~r1_tarski(B_50, C_52) | ~m1_subset_1(C_52, A_46) | ~m1_subset_1(B_50, A_46) | v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_56, c_247])).
% 4.45/1.91  tff(c_265, plain, (![A_109, B_110, C_111]: (k12_lattice3(k2_yellow_1(A_109), B_110, C_111)=B_110 | ~v2_lattice3(k2_yellow_1(A_109)) | ~r1_tarski(B_110, C_111) | ~m1_subset_1(C_111, A_109) | ~m1_subset_1(B_110, A_109) | v1_xboole_0(A_109))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_26, c_36, c_36, c_249])).
% 4.45/1.91  tff(c_267, plain, (![B_110, C_111]: (k12_lattice3(k2_yellow_1('#skF_1'), B_110, C_111)=B_110 | ~r1_tarski(B_110, C_111) | ~m1_subset_1(C_111, '#skF_1') | ~m1_subset_1(B_110, '#skF_1') | v1_xboole_0('#skF_1'))), inference(resolution, [status(thm)], [c_50, c_265])).
% 4.45/1.91  tff(c_271, plain, (![B_112, C_113]: (k12_lattice3(k2_yellow_1('#skF_1'), B_112, C_113)=B_112 | ~r1_tarski(B_112, C_113) | ~m1_subset_1(C_113, '#skF_1') | ~m1_subset_1(B_112, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_52, c_267])).
% 4.45/1.91  tff(c_133, plain, (![A_87, B_88, C_89]: (k12_lattice3(A_87, B_88, C_89)=k11_lattice3(A_87, B_88, C_89) | ~m1_subset_1(C_89, u1_struct_0(A_87)) | ~m1_subset_1(B_88, u1_struct_0(A_87)) | ~l1_orders_2(A_87) | ~v2_lattice3(A_87) | ~v5_orders_2(A_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.45/1.91  tff(c_140, plain, (![A_45, B_88, C_89]: (k12_lattice3(k2_yellow_1(A_45), B_88, C_89)=k11_lattice3(k2_yellow_1(A_45), B_88, C_89) | ~m1_subset_1(C_89, A_45) | ~m1_subset_1(B_88, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v2_lattice3(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_133])).
% 4.45/1.91  tff(c_145, plain, (![A_90, B_91, C_92]: (k12_lattice3(k2_yellow_1(A_90), B_91, C_92)=k11_lattice3(k2_yellow_1(A_90), B_91, C_92) | ~m1_subset_1(C_92, A_90) | ~m1_subset_1(B_91, A_90) | ~v2_lattice3(k2_yellow_1(A_90)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_36, c_140])).
% 4.45/1.91  tff(c_148, plain, (![B_91, C_92]: (k12_lattice3(k2_yellow_1('#skF_1'), B_91, C_92)=k11_lattice3(k2_yellow_1('#skF_1'), B_91, C_92) | ~m1_subset_1(C_92, '#skF_1') | ~m1_subset_1(B_91, '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_145])).
% 4.45/1.91  tff(c_296, plain, (![B_117, C_118]: (k11_lattice3(k2_yellow_1('#skF_1'), B_117, C_118)=B_117 | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1') | ~r1_tarski(B_117, C_118) | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_271, c_148])).
% 4.45/1.91  tff(c_149, plain, (![A_93, C_94, B_95]: (k11_lattice3(A_93, C_94, B_95)=k11_lattice3(A_93, B_95, C_94) | ~m1_subset_1(C_94, u1_struct_0(A_93)) | ~m1_subset_1(B_95, u1_struct_0(A_93)) | ~l1_orders_2(A_93) | ~v2_lattice3(A_93) | ~v5_orders_2(A_93))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.45/1.91  tff(c_156, plain, (![A_45, C_94, B_95]: (k11_lattice3(k2_yellow_1(A_45), C_94, B_95)=k11_lattice3(k2_yellow_1(A_45), B_95, C_94) | ~m1_subset_1(C_94, A_45) | ~m1_subset_1(B_95, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v2_lattice3(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_149])).
% 4.45/1.91  tff(c_170, plain, (![A_98, C_99, B_100]: (k11_lattice3(k2_yellow_1(A_98), C_99, B_100)=k11_lattice3(k2_yellow_1(A_98), B_100, C_99) | ~m1_subset_1(C_99, A_98) | ~m1_subset_1(B_100, A_98) | ~v2_lattice3(k2_yellow_1(A_98)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_36, c_156])).
% 4.45/1.91  tff(c_173, plain, (![C_99, B_100]: (k11_lattice3(k2_yellow_1('#skF_1'), C_99, B_100)=k11_lattice3(k2_yellow_1('#skF_1'), B_100, C_99) | ~m1_subset_1(C_99, '#skF_1') | ~m1_subset_1(B_100, '#skF_1'))), inference(resolution, [status(thm)], [c_50, c_170])).
% 4.45/1.91  tff(c_308, plain, (![C_118, B_117]: (k11_lattice3(k2_yellow_1('#skF_1'), C_118, B_117)=B_117 | ~m1_subset_1(B_117, '#skF_1') | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1') | ~r1_tarski(B_117, C_118) | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_296, c_173])).
% 4.45/1.91  tff(c_357, plain, (![A_122, B_123, C_124, D_125]: (k11_lattice3(A_122, k11_lattice3(A_122, B_123, C_124), D_125)=k11_lattice3(A_122, B_123, k11_lattice3(A_122, C_124, D_125)) | ~v4_orders_2(A_122) | ~m1_subset_1(D_125, u1_struct_0(A_122)) | ~m1_subset_1(C_124, u1_struct_0(A_122)) | ~m1_subset_1(B_123, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v2_lattice3(A_122) | ~v5_orders_2(A_122))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.45/1.91  tff(c_364, plain, (![A_45, B_123, C_124, D_125]: (k11_lattice3(k2_yellow_1(A_45), k11_lattice3(k2_yellow_1(A_45), B_123, C_124), D_125)=k11_lattice3(k2_yellow_1(A_45), B_123, k11_lattice3(k2_yellow_1(A_45), C_124, D_125)) | ~v4_orders_2(k2_yellow_1(A_45)) | ~m1_subset_1(D_125, A_45) | ~m1_subset_1(C_124, u1_struct_0(k2_yellow_1(A_45))) | ~m1_subset_1(B_123, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v2_lattice3(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_357])).
% 4.45/1.91  tff(c_472, plain, (![A_139, B_140, C_141, D_142]: (k11_lattice3(k2_yellow_1(A_139), k11_lattice3(k2_yellow_1(A_139), B_140, C_141), D_142)=k11_lattice3(k2_yellow_1(A_139), B_140, k11_lattice3(k2_yellow_1(A_139), C_141, D_142)) | ~m1_subset_1(D_142, A_139) | ~m1_subset_1(C_141, A_139) | ~m1_subset_1(B_140, A_139) | ~v2_lattice3(k2_yellow_1(A_139)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_26, c_36, c_36, c_32, c_364])).
% 4.45/1.91  tff(c_517, plain, (![C_118, B_117, D_142]: (k11_lattice3(k2_yellow_1('#skF_1'), C_118, k11_lattice3(k2_yellow_1('#skF_1'), B_117, D_142))=k11_lattice3(k2_yellow_1('#skF_1'), B_117, D_142) | ~m1_subset_1(D_142, '#skF_1') | ~m1_subset_1(B_117, '#skF_1') | ~m1_subset_1(C_118, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_117, '#skF_1') | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1') | ~r1_tarski(B_117, C_118) | ~m1_subset_1(C_118, '#skF_1') | ~m1_subset_1(B_117, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_308, c_472])).
% 4.45/1.91  tff(c_668, plain, (![C_146, B_147, D_148]: (k11_lattice3(k2_yellow_1('#skF_1'), C_146, k11_lattice3(k2_yellow_1('#skF_1'), B_147, D_148))=k11_lattice3(k2_yellow_1('#skF_1'), B_147, D_148) | ~m1_subset_1(D_148, '#skF_1') | ~r1_tarski(B_147, C_146) | ~m1_subset_1(C_146, '#skF_1') | ~m1_subset_1(B_147, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_517])).
% 4.45/1.91  tff(c_253, plain, (![A_106, B_107, C_108]: (r3_orders_2(A_106, B_107, C_108) | k12_lattice3(A_106, B_107, C_108)!=B_107 | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v2_lattice3(A_106) | ~v5_orders_2(A_106) | ~v3_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.45/1.91  tff(c_260, plain, (![A_45, B_107, C_108]: (r3_orders_2(k2_yellow_1(A_45), B_107, C_108) | k12_lattice3(k2_yellow_1(A_45), B_107, C_108)!=B_107 | ~m1_subset_1(C_108, A_45) | ~m1_subset_1(B_107, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v2_lattice3(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)) | ~v3_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_253])).
% 4.45/1.91  tff(c_286, plain, (![A_114, B_115, C_116]: (r3_orders_2(k2_yellow_1(A_114), B_115, C_116) | k12_lattice3(k2_yellow_1(A_114), B_115, C_116)!=B_115 | ~m1_subset_1(C_116, A_114) | ~m1_subset_1(B_115, A_114) | ~v2_lattice3(k2_yellow_1(A_114)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34, c_26, c_36, c_260])).
% 4.45/1.91  tff(c_345, plain, (![B_119, C_120, A_121]: (r1_tarski(B_119, C_120) | v1_xboole_0(A_121) | k12_lattice3(k2_yellow_1(A_121), B_119, C_120)!=B_119 | ~m1_subset_1(C_120, A_121) | ~m1_subset_1(B_119, A_121) | ~v2_lattice3(k2_yellow_1(A_121)))), inference(resolution, [status(thm)], [c_286, c_55])).
% 4.45/1.91  tff(c_349, plain, (![B_91, C_92]: (r1_tarski(B_91, C_92) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_91, C_92)!=B_91 | ~m1_subset_1(C_92, '#skF_1') | ~m1_subset_1(B_91, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_92, '#skF_1') | ~m1_subset_1(B_91, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_148, c_345])).
% 4.45/1.91  tff(c_355, plain, (![B_91, C_92]: (r1_tarski(B_91, C_92) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_91, C_92)!=B_91 | ~m1_subset_1(C_92, '#skF_1') | ~m1_subset_1(B_91, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_349])).
% 4.45/1.91  tff(c_369, plain, (![B_126, C_127]: (r1_tarski(B_126, C_127) | k11_lattice3(k2_yellow_1('#skF_1'), B_126, C_127)!=B_126 | ~m1_subset_1(C_127, '#skF_1') | ~m1_subset_1(B_126, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_52, c_355])).
% 4.45/1.91  tff(c_375, plain, (![B_100, C_99]: (r1_tarski(B_100, C_99) | k11_lattice3(k2_yellow_1('#skF_1'), C_99, B_100)!=B_100 | ~m1_subset_1(C_99, '#skF_1') | ~m1_subset_1(B_100, '#skF_1') | ~m1_subset_1(C_99, '#skF_1') | ~m1_subset_1(B_100, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_173, c_369])).
% 4.45/1.91  tff(c_776, plain, (![B_149, D_150, C_151]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), B_149, D_150), C_151) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), B_149, D_150), '#skF_1') | ~m1_subset_1(D_150, '#skF_1') | ~r1_tarski(B_149, C_151) | ~m1_subset_1(C_151, '#skF_1') | ~m1_subset_1(B_149, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_668, c_375])).
% 4.45/1.91  tff(c_99, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k3_xboole_0(B_70, C_71)) | ~r1_tarski(A_69, C_71) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.45/1.91  tff(c_44, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.45/1.91  tff(c_106, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_99, c_44])).
% 4.45/1.91  tff(c_107, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_106])).
% 4.45/1.91  tff(c_785, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1') | ~r1_tarski('#skF_2', '#skF_2') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_776, c_107])).
% 4.45/1.91  tff(c_821, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_53, c_6, c_54, c_785])).
% 4.45/1.91  tff(c_843, plain, (~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_125, c_821])).
% 4.45/1.91  tff(c_855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_54, c_843])).
% 4.45/1.91  tff(c_856, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_106])).
% 4.45/1.91  tff(c_982, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_940, c_856])).
% 4.45/1.91  tff(c_1020, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_53, c_982])).
% 4.45/1.91  tff(c_1607, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_3', '#skF_3') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1604, c_1020])).
% 4.45/1.91  tff(c_1643, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6, c_53, c_1607])).
% 4.45/1.91  tff(c_1664, plain, (~m1_subset_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_885, c_1643])).
% 4.45/1.91  tff(c_1672, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_53, c_1664])).
% 4.45/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/1.91  
% 4.45/1.91  Inference rules
% 4.45/1.91  ----------------------
% 4.45/1.91  #Ref     : 0
% 4.45/1.91  #Sup     : 369
% 4.45/1.91  #Fact    : 0
% 4.45/1.91  #Define  : 0
% 4.45/1.91  #Split   : 3
% 4.45/1.91  #Chain   : 0
% 4.45/1.91  #Close   : 0
% 4.45/1.91  
% 4.45/1.91  Ordering : KBO
% 4.45/1.91  
% 4.45/1.91  Simplification rules
% 4.45/1.91  ----------------------
% 4.45/1.91  #Subsume      : 70
% 4.45/1.91  #Demod        : 387
% 4.45/1.91  #Tautology    : 90
% 4.45/1.91  #SimpNegUnit  : 7
% 4.45/1.91  #BackRed      : 0
% 4.45/1.91  
% 4.45/1.91  #Partial instantiations: 0
% 4.45/1.91  #Strategies tried      : 1
% 4.45/1.91  
% 4.45/1.91  Timing (in seconds)
% 4.45/1.91  ----------------------
% 4.45/1.91  Preprocessing        : 0.36
% 4.45/1.92  Parsing              : 0.19
% 4.45/1.92  CNF conversion       : 0.03
% 4.45/1.92  Main loop            : 0.76
% 4.45/1.92  Inferencing          : 0.28
% 4.45/1.92  Reduction            : 0.24
% 4.45/1.92  Demodulation         : 0.17
% 4.45/1.92  BG Simplification    : 0.04
% 4.45/1.92  Subsumption          : 0.15
% 4.45/1.92  Abstraction          : 0.05
% 4.45/1.92  MUC search           : 0.00
% 4.45/1.92  Cooper               : 0.00
% 4.45/1.92  Total                : 1.17
% 4.45/1.92  Index Insertion      : 0.00
% 4.45/1.92  Index Deletion       : 0.00
% 4.45/1.92  Index Matching       : 0.00
% 4.45/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
