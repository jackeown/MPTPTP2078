%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:24 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 490 expanded)
%              Number of leaves         :   39 ( 200 expanded)
%              Depth                    :   15
%              Number of atoms          :  483 (1322 expanded)
%              Number of equality atoms :   58 ( 267 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_140,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_167,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_128,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_136,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => r3_orders_2(A,B,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

tff(f_124,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_106,axiom,(
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

tff(f_87,axiom,(
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

tff(f_153,axiom,(
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
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    ! [A_47] : u1_struct_0(k2_yellow_1(A_47)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_52,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_46,plain,(
    m1_subset_1('#skF_2',u1_struct_0(k2_yellow_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_51,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_46])).

tff(c_24,plain,(
    ! [A_45] : l1_orders_2(k2_yellow_1(A_45)) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_852,plain,(
    ! [A_158,B_159,C_160] :
      ( m1_subset_1(k11_lattice3(A_158,B_159,C_160),u1_struct_0(A_158))
      | ~ m1_subset_1(C_160,u1_struct_0(A_158))
      | ~ m1_subset_1(B_159,u1_struct_0(A_158))
      | ~ l1_orders_2(A_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_855,plain,(
    ! [A_47,B_159,C_160] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_47),B_159,C_160),A_47)
      | ~ m1_subset_1(C_160,u1_struct_0(k2_yellow_1(A_47)))
      | ~ m1_subset_1(B_159,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_852])).

tff(c_857,plain,(
    ! [A_47,B_159,C_160] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_47),B_159,C_160),A_47)
      | ~ m1_subset_1(C_160,A_47)
      | ~ m1_subset_1(B_159,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34,c_34,c_855])).

tff(c_48,plain,(
    v2_lattice3(k2_yellow_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_28,plain,(
    ! [A_46] : v3_orders_2(k2_yellow_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_32,plain,(
    ! [A_46] : v5_orders_2(k2_yellow_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_859,plain,(
    ! [A_164,B_165,C_166] :
      ( r3_orders_2(A_164,B_165,B_165)
      | ~ m1_subset_1(C_166,u1_struct_0(A_164))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_orders_2(A_164)
      | ~ v3_orders_2(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_866,plain,(
    ! [A_47,B_165,C_166] :
      ( r3_orders_2(k2_yellow_1(A_47),B_165,B_165)
      | ~ m1_subset_1(C_166,A_47)
      | ~ m1_subset_1(B_165,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v3_orders_2(k2_yellow_1(A_47))
      | v2_struct_0(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_859])).

tff(c_883,plain,(
    ! [A_170,B_171,C_172] :
      ( r3_orders_2(k2_yellow_1(A_170),B_171,B_171)
      | ~ m1_subset_1(C_172,A_170)
      | ~ m1_subset_1(B_171,A_170)
      | v2_struct_0(k2_yellow_1(A_170)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_34,c_866])).

tff(c_894,plain,(
    ! [B_171] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_171,B_171)
      | ~ m1_subset_1(B_171,'#skF_1')
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_883])).

tff(c_896,plain,(
    v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_894])).

tff(c_8,plain,(
    ! [A_9] :
      ( ~ v2_struct_0(A_9)
      | ~ v2_lattice3(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_899,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_1'))
    | ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_896,c_8])).

tff(c_903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_48,c_899])).

tff(c_905,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_894])).

tff(c_895,plain,(
    ! [B_171] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_171,B_171)
      | ~ m1_subset_1(B_171,'#skF_1')
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_51,c_883])).

tff(c_906,plain,(
    v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_895])).

tff(c_907,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_905,c_906])).

tff(c_908,plain,(
    ! [B_171] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_171,B_171)
      | ~ m1_subset_1(B_171,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_895])).

tff(c_1053,plain,(
    ! [A_195,B_196,C_197] :
      ( k12_lattice3(A_195,B_196,C_197) = B_196
      | ~ r3_orders_2(A_195,B_196,C_197)
      | ~ m1_subset_1(C_197,u1_struct_0(A_195))
      | ~ m1_subset_1(B_196,u1_struct_0(A_195))
      | ~ l1_orders_2(A_195)
      | ~ v2_lattice3(A_195)
      | ~ v5_orders_2(A_195)
      | ~ v3_orders_2(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1055,plain,(
    ! [B_171] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_171,B_171) = B_171
      | ~ m1_subset_1(B_171,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1'))
      | ~ v3_orders_2(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_171,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_908,c_1053])).

tff(c_1071,plain,(
    ! [B_198] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_198,B_198) = B_198
      | ~ m1_subset_1(B_198,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_48,c_24,c_34,c_1055])).

tff(c_871,plain,(
    ! [A_167,B_168,C_169] :
      ( k12_lattice3(A_167,B_168,C_169) = k11_lattice3(A_167,B_168,C_169)
      | ~ m1_subset_1(C_169,u1_struct_0(A_167))
      | ~ m1_subset_1(B_168,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167)
      | ~ v2_lattice3(A_167)
      | ~ v5_orders_2(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_878,plain,(
    ! [A_47,B_168,C_169] :
      ( k12_lattice3(k2_yellow_1(A_47),B_168,C_169) = k11_lattice3(k2_yellow_1(A_47),B_168,C_169)
      | ~ m1_subset_1(C_169,A_47)
      | ~ m1_subset_1(B_168,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v2_lattice3(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_871])).

tff(c_957,plain,(
    ! [A_185,B_186,C_187] :
      ( k12_lattice3(k2_yellow_1(A_185),B_186,C_187) = k11_lattice3(k2_yellow_1(A_185),B_186,C_187)
      | ~ m1_subset_1(C_187,A_185)
      | ~ m1_subset_1(B_186,A_185)
      | ~ v2_lattice3(k2_yellow_1(A_185)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_34,c_878])).

tff(c_960,plain,(
    ! [B_186,C_187] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_186,C_187) = k11_lattice3(k2_yellow_1('#skF_1'),B_186,C_187)
      | ~ m1_subset_1(C_187,'#skF_1')
      | ~ m1_subset_1(B_186,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_957])).

tff(c_1077,plain,(
    ! [B_198] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_198,B_198) = B_198
      | ~ m1_subset_1(B_198,'#skF_1')
      | ~ m1_subset_1(B_198,'#skF_1')
      | ~ m1_subset_1(B_198,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1071,c_960])).

tff(c_30,plain,(
    ! [A_46] : v4_orders_2(k2_yellow_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1114,plain,(
    ! [A_203,B_204,C_205,D_206] :
      ( k11_lattice3(A_203,k11_lattice3(A_203,B_204,C_205),D_206) = k11_lattice3(A_203,B_204,k11_lattice3(A_203,C_205,D_206))
      | ~ v4_orders_2(A_203)
      | ~ m1_subset_1(D_206,u1_struct_0(A_203))
      | ~ m1_subset_1(C_205,u1_struct_0(A_203))
      | ~ m1_subset_1(B_204,u1_struct_0(A_203))
      | ~ l1_orders_2(A_203)
      | ~ v2_lattice3(A_203)
      | ~ v5_orders_2(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_1121,plain,(
    ! [A_47,B_204,C_205,D_206] :
      ( k11_lattice3(k2_yellow_1(A_47),k11_lattice3(k2_yellow_1(A_47),B_204,C_205),D_206) = k11_lattice3(k2_yellow_1(A_47),B_204,k11_lattice3(k2_yellow_1(A_47),C_205,D_206))
      | ~ v4_orders_2(k2_yellow_1(A_47))
      | ~ m1_subset_1(D_206,A_47)
      | ~ m1_subset_1(C_205,u1_struct_0(k2_yellow_1(A_47)))
      | ~ m1_subset_1(B_204,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v2_lattice3(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1114])).

tff(c_1368,plain,(
    ! [A_227,B_228,C_229,D_230] :
      ( k11_lattice3(k2_yellow_1(A_227),k11_lattice3(k2_yellow_1(A_227),B_228,C_229),D_230) = k11_lattice3(k2_yellow_1(A_227),B_228,k11_lattice3(k2_yellow_1(A_227),C_229,D_230))
      | ~ m1_subset_1(D_230,A_227)
      | ~ m1_subset_1(C_229,A_227)
      | ~ m1_subset_1(B_228,A_227)
      | ~ v2_lattice3(k2_yellow_1(A_227)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_34,c_34,c_30,c_1121])).

tff(c_1431,plain,(
    ! [B_198,D_230] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_198,k11_lattice3(k2_yellow_1('#skF_1'),B_198,D_230)) = k11_lattice3(k2_yellow_1('#skF_1'),B_198,D_230)
      | ~ m1_subset_1(D_230,'#skF_1')
      | ~ m1_subset_1(B_198,'#skF_1')
      | ~ m1_subset_1(B_198,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_198,'#skF_1')
      | ~ m1_subset_1(B_198,'#skF_1')
      | ~ m1_subset_1(B_198,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1077,c_1368])).

tff(c_1488,plain,(
    ! [B_231,D_232] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_231,k11_lattice3(k2_yellow_1('#skF_1'),B_231,D_232)) = k11_lattice3(k2_yellow_1('#skF_1'),B_231,D_232)
      | ~ m1_subset_1(D_232,'#skF_1')
      | ~ m1_subset_1(B_231,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1431])).

tff(c_917,plain,(
    ! [A_174,C_175,B_176] :
      ( k11_lattice3(A_174,C_175,B_176) = k11_lattice3(A_174,B_176,C_175)
      | ~ m1_subset_1(C_175,u1_struct_0(A_174))
      | ~ m1_subset_1(B_176,u1_struct_0(A_174))
      | ~ l1_orders_2(A_174)
      | ~ v2_lattice3(A_174)
      | ~ v5_orders_2(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_924,plain,(
    ! [A_47,C_175,B_176] :
      ( k11_lattice3(k2_yellow_1(A_47),C_175,B_176) = k11_lattice3(k2_yellow_1(A_47),B_176,C_175)
      | ~ m1_subset_1(C_175,A_47)
      | ~ m1_subset_1(B_176,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v2_lattice3(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_917])).

tff(c_970,plain,(
    ! [A_190,C_191,B_192] :
      ( k11_lattice3(k2_yellow_1(A_190),C_191,B_192) = k11_lattice3(k2_yellow_1(A_190),B_192,C_191)
      | ~ m1_subset_1(C_191,A_190)
      | ~ m1_subset_1(B_192,A_190)
      | ~ v2_lattice3(k2_yellow_1(A_190)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_34,c_924])).

tff(c_973,plain,(
    ! [C_191,B_192] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_191,B_192) = k11_lattice3(k2_yellow_1('#skF_1'),B_192,C_191)
      | ~ m1_subset_1(C_191,'#skF_1')
      | ~ m1_subset_1(B_192,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_970])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_945,plain,(
    ! [A_182,B_183,C_184] :
      ( r3_orders_2(A_182,B_183,C_184)
      | k12_lattice3(A_182,B_183,C_184) != B_183
      | ~ m1_subset_1(C_184,u1_struct_0(A_182))
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_orders_2(A_182)
      | ~ v2_lattice3(A_182)
      | ~ v5_orders_2(A_182)
      | ~ v3_orders_2(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_952,plain,(
    ! [A_47,B_183,C_184] :
      ( r3_orders_2(k2_yellow_1(A_47),B_183,C_184)
      | k12_lattice3(k2_yellow_1(A_47),B_183,C_184) != B_183
      | ~ m1_subset_1(C_184,A_47)
      | ~ m1_subset_1(B_183,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v2_lattice3(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47))
      | ~ v3_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_945])).

tff(c_1104,plain,(
    ! [A_200,B_201,C_202] :
      ( r3_orders_2(k2_yellow_1(A_200),B_201,C_202)
      | k12_lattice3(k2_yellow_1(A_200),B_201,C_202) != B_201
      | ~ m1_subset_1(C_202,A_200)
      | ~ m1_subset_1(B_201,A_200)
      | ~ v2_lattice3(k2_yellow_1(A_200)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_24,c_34,c_952])).

tff(c_40,plain,(
    ! [B_52,C_54,A_48] :
      ( r1_tarski(B_52,C_54)
      | ~ r3_orders_2(k2_yellow_1(A_48),B_52,C_54)
      | ~ m1_subset_1(C_54,u1_struct_0(k2_yellow_1(A_48)))
      | ~ m1_subset_1(B_52,u1_struct_0(k2_yellow_1(A_48)))
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_53,plain,(
    ! [B_52,C_54,A_48] :
      ( r1_tarski(B_52,C_54)
      | ~ r3_orders_2(k2_yellow_1(A_48),B_52,C_54)
      | ~ m1_subset_1(C_54,A_48)
      | ~ m1_subset_1(B_52,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_34,c_40])).

tff(c_1156,plain,(
    ! [B_212,C_213,A_214] :
      ( r1_tarski(B_212,C_213)
      | v1_xboole_0(A_214)
      | k12_lattice3(k2_yellow_1(A_214),B_212,C_213) != B_212
      | ~ m1_subset_1(C_213,A_214)
      | ~ m1_subset_1(B_212,A_214)
      | ~ v2_lattice3(k2_yellow_1(A_214)) ) ),
    inference(resolution,[status(thm)],[c_1104,c_53])).

tff(c_1162,plain,(
    ! [B_186,C_187] :
      ( r1_tarski(B_186,C_187)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_186,C_187) != B_186
      | ~ m1_subset_1(C_187,'#skF_1')
      | ~ m1_subset_1(B_186,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_187,'#skF_1')
      | ~ m1_subset_1(B_186,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_960,c_1156])).

tff(c_1172,plain,(
    ! [B_186,C_187] :
      ( r1_tarski(B_186,C_187)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_186,C_187) != B_186
      | ~ m1_subset_1(C_187,'#skF_1')
      | ~ m1_subset_1(B_186,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1162])).

tff(c_1174,plain,(
    ! [B_215,C_216] :
      ( r1_tarski(B_215,C_216)
      | k11_lattice3(k2_yellow_1('#skF_1'),B_215,C_216) != B_215
      | ~ m1_subset_1(C_216,'#skF_1')
      | ~ m1_subset_1(B_215,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1172])).

tff(c_1180,plain,(
    ! [B_192,C_191] :
      ( r1_tarski(B_192,C_191)
      | k11_lattice3(k2_yellow_1('#skF_1'),C_191,B_192) != B_192
      | ~ m1_subset_1(C_191,'#skF_1')
      | ~ m1_subset_1(B_192,'#skF_1')
      | ~ m1_subset_1(C_191,'#skF_1')
      | ~ m1_subset_1(B_192,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_973,c_1174])).

tff(c_1575,plain,(
    ! [B_233,D_234] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),B_233,D_234),B_233)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),B_233,D_234),'#skF_1')
      | ~ m1_subset_1(D_234,'#skF_1')
      | ~ m1_subset_1(B_233,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1488,c_1180])).

tff(c_974,plain,(
    ! [C_193,B_194] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_193,B_194) = k11_lattice3(k2_yellow_1('#skF_1'),B_194,C_193)
      | ~ m1_subset_1(C_193,'#skF_1')
      | ~ m1_subset_1(B_194,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_970])).

tff(c_101,plain,(
    ! [A_78,B_79,C_80] :
      ( m1_subset_1(k11_lattice3(A_78,B_79,C_80),u1_struct_0(A_78))
      | ~ m1_subset_1(C_80,u1_struct_0(A_78))
      | ~ m1_subset_1(B_79,u1_struct_0(A_78))
      | ~ l1_orders_2(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,(
    ! [A_47,B_79,C_80] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_47),B_79,C_80),A_47)
      | ~ m1_subset_1(C_80,u1_struct_0(k2_yellow_1(A_47)))
      | ~ m1_subset_1(B_79,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_101])).

tff(c_106,plain,(
    ! [A_47,B_79,C_80] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_47),B_79,C_80),A_47)
      | ~ m1_subset_1(C_80,A_47)
      | ~ m1_subset_1(B_79,A_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34,c_34,c_104])).

tff(c_108,plain,(
    ! [A_84,B_85,C_86] :
      ( r3_orders_2(A_84,B_85,B_85)
      | ~ m1_subset_1(C_86,u1_struct_0(A_84))
      | ~ m1_subset_1(B_85,u1_struct_0(A_84))
      | ~ l1_orders_2(A_84)
      | ~ v3_orders_2(A_84)
      | v2_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [A_47,B_85,C_86] :
      ( r3_orders_2(k2_yellow_1(A_47),B_85,B_85)
      | ~ m1_subset_1(C_86,A_47)
      | ~ m1_subset_1(B_85,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v3_orders_2(k2_yellow_1(A_47))
      | v2_struct_0(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_108])).

tff(c_120,plain,(
    ! [A_87,B_88,C_89] :
      ( r3_orders_2(k2_yellow_1(A_87),B_88,B_88)
      | ~ m1_subset_1(C_89,A_87)
      | ~ m1_subset_1(B_88,A_87)
      | v2_struct_0(k2_yellow_1(A_87)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_34,c_115])).

tff(c_131,plain,(
    ! [B_88] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_88,B_88)
      | ~ m1_subset_1(B_88,'#skF_1')
      | v2_struct_0(k2_yellow_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_52,c_120])).

tff(c_133,plain,(
    v2_struct_0(k2_yellow_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_136,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_1'))
    | ~ l1_orders_2(k2_yellow_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_133,c_8])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_48,c_136])).

tff(c_141,plain,(
    ! [B_88] :
      ( r3_orders_2(k2_yellow_1('#skF_1'),B_88,B_88)
      | ~ m1_subset_1(B_88,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_318,plain,(
    ! [A_125,B_126,C_127] :
      ( k12_lattice3(A_125,B_126,C_127) = B_126
      | ~ r3_orders_2(A_125,B_126,C_127)
      | ~ m1_subset_1(C_127,u1_struct_0(A_125))
      | ~ m1_subset_1(B_126,u1_struct_0(A_125))
      | ~ l1_orders_2(A_125)
      | ~ v2_lattice3(A_125)
      | ~ v5_orders_2(A_125)
      | ~ v3_orders_2(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_322,plain,(
    ! [B_88] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_88,B_88) = B_88
      | ~ m1_subset_1(B_88,u1_struct_0(k2_yellow_1('#skF_1')))
      | ~ l1_orders_2(k2_yellow_1('#skF_1'))
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ v5_orders_2(k2_yellow_1('#skF_1'))
      | ~ v3_orders_2(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_88,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_141,c_318])).

tff(c_334,plain,(
    ! [B_128] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_128,B_128) = B_128
      | ~ m1_subset_1(B_128,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_48,c_24,c_34,c_322])).

tff(c_143,plain,(
    ! [A_90,B_91,C_92] :
      ( k12_lattice3(A_90,B_91,C_92) = k11_lattice3(A_90,B_91,C_92)
      | ~ m1_subset_1(C_92,u1_struct_0(A_90))
      | ~ m1_subset_1(B_91,u1_struct_0(A_90))
      | ~ l1_orders_2(A_90)
      | ~ v2_lattice3(A_90)
      | ~ v5_orders_2(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_150,plain,(
    ! [A_47,B_91,C_92] :
      ( k12_lattice3(k2_yellow_1(A_47),B_91,C_92) = k11_lattice3(k2_yellow_1(A_47),B_91,C_92)
      | ~ m1_subset_1(C_92,A_47)
      | ~ m1_subset_1(B_91,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v2_lattice3(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_143])).

tff(c_179,plain,(
    ! [A_99,B_100,C_101] :
      ( k12_lattice3(k2_yellow_1(A_99),B_100,C_101) = k11_lattice3(k2_yellow_1(A_99),B_100,C_101)
      | ~ m1_subset_1(C_101,A_99)
      | ~ m1_subset_1(B_100,A_99)
      | ~ v2_lattice3(k2_yellow_1(A_99)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_34,c_150])).

tff(c_182,plain,(
    ! [B_100,C_101] :
      ( k12_lattice3(k2_yellow_1('#skF_1'),B_100,C_101) = k11_lattice3(k2_yellow_1('#skF_1'),B_100,C_101)
      | ~ m1_subset_1(C_101,'#skF_1')
      | ~ m1_subset_1(B_100,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_179])).

tff(c_342,plain,(
    ! [B_128] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_128,B_128) = B_128
      | ~ m1_subset_1(B_128,'#skF_1')
      | ~ m1_subset_1(B_128,'#skF_1')
      | ~ m1_subset_1(B_128,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_182])).

tff(c_484,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k11_lattice3(A_137,k11_lattice3(A_137,B_138,C_139),D_140) = k11_lattice3(A_137,B_138,k11_lattice3(A_137,C_139,D_140))
      | ~ v4_orders_2(A_137)
      | ~ m1_subset_1(D_140,u1_struct_0(A_137))
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v2_lattice3(A_137)
      | ~ v5_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_491,plain,(
    ! [A_47,B_138,C_139,D_140] :
      ( k11_lattice3(k2_yellow_1(A_47),k11_lattice3(k2_yellow_1(A_47),B_138,C_139),D_140) = k11_lattice3(k2_yellow_1(A_47),B_138,k11_lattice3(k2_yellow_1(A_47),C_139,D_140))
      | ~ v4_orders_2(k2_yellow_1(A_47))
      | ~ m1_subset_1(D_140,A_47)
      | ~ m1_subset_1(C_139,u1_struct_0(k2_yellow_1(A_47)))
      | ~ m1_subset_1(B_138,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v2_lattice3(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_484])).

tff(c_580,plain,(
    ! [A_147,B_148,C_149,D_150] :
      ( k11_lattice3(k2_yellow_1(A_147),k11_lattice3(k2_yellow_1(A_147),B_148,C_149),D_150) = k11_lattice3(k2_yellow_1(A_147),B_148,k11_lattice3(k2_yellow_1(A_147),C_149,D_150))
      | ~ m1_subset_1(D_150,A_147)
      | ~ m1_subset_1(C_149,A_147)
      | ~ m1_subset_1(B_148,A_147)
      | ~ v2_lattice3(k2_yellow_1(A_147)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_34,c_34,c_30,c_491])).

tff(c_643,plain,(
    ! [B_128,D_150] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_128,k11_lattice3(k2_yellow_1('#skF_1'),B_128,D_150)) = k11_lattice3(k2_yellow_1('#skF_1'),B_128,D_150)
      | ~ m1_subset_1(D_150,'#skF_1')
      | ~ m1_subset_1(B_128,'#skF_1')
      | ~ m1_subset_1(B_128,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(B_128,'#skF_1')
      | ~ m1_subset_1(B_128,'#skF_1')
      | ~ m1_subset_1(B_128,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_580])).

tff(c_700,plain,(
    ! [B_151,D_152] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),B_151,k11_lattice3(k2_yellow_1('#skF_1'),B_151,D_152)) = k11_lattice3(k2_yellow_1('#skF_1'),B_151,D_152)
      | ~ m1_subset_1(D_152,'#skF_1')
      | ~ m1_subset_1(B_151,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_643])).

tff(c_192,plain,(
    ! [A_104,C_105,B_106] :
      ( k11_lattice3(A_104,C_105,B_106) = k11_lattice3(A_104,B_106,C_105)
      | ~ m1_subset_1(C_105,u1_struct_0(A_104))
      | ~ m1_subset_1(B_106,u1_struct_0(A_104))
      | ~ l1_orders_2(A_104)
      | ~ v2_lattice3(A_104)
      | ~ v5_orders_2(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_199,plain,(
    ! [A_47,C_105,B_106] :
      ( k11_lattice3(k2_yellow_1(A_47),C_105,B_106) = k11_lattice3(k2_yellow_1(A_47),B_106,C_105)
      | ~ m1_subset_1(C_105,A_47)
      | ~ m1_subset_1(B_106,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v2_lattice3(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_192])).

tff(c_204,plain,(
    ! [A_107,C_108,B_109] :
      ( k11_lattice3(k2_yellow_1(A_107),C_108,B_109) = k11_lattice3(k2_yellow_1(A_107),B_109,C_108)
      | ~ m1_subset_1(C_108,A_107)
      | ~ m1_subset_1(B_109,A_107)
      | ~ v2_lattice3(k2_yellow_1(A_107)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_24,c_34,c_199])).

tff(c_207,plain,(
    ! [C_108,B_109] :
      ( k11_lattice3(k2_yellow_1('#skF_1'),C_108,B_109) = k11_lattice3(k2_yellow_1('#skF_1'),B_109,C_108)
      | ~ m1_subset_1(C_108,'#skF_1')
      | ~ m1_subset_1(B_109,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_48,c_204])).

tff(c_208,plain,(
    ! [A_110,B_111,C_112] :
      ( r3_orders_2(A_110,B_111,C_112)
      | k12_lattice3(A_110,B_111,C_112) != B_111
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ m1_subset_1(B_111,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110)
      | ~ v2_lattice3(A_110)
      | ~ v5_orders_2(A_110)
      | ~ v3_orders_2(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_215,plain,(
    ! [A_47,B_111,C_112] :
      ( r3_orders_2(k2_yellow_1(A_47),B_111,C_112)
      | k12_lattice3(k2_yellow_1(A_47),B_111,C_112) != B_111
      | ~ m1_subset_1(C_112,A_47)
      | ~ m1_subset_1(B_111,u1_struct_0(k2_yellow_1(A_47)))
      | ~ l1_orders_2(k2_yellow_1(A_47))
      | ~ v2_lattice3(k2_yellow_1(A_47))
      | ~ v5_orders_2(k2_yellow_1(A_47))
      | ~ v3_orders_2(k2_yellow_1(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_208])).

tff(c_293,plain,(
    ! [A_115,B_116,C_117] :
      ( r3_orders_2(k2_yellow_1(A_115),B_116,C_117)
      | k12_lattice3(k2_yellow_1(A_115),B_116,C_117) != B_116
      | ~ m1_subset_1(C_117,A_115)
      | ~ m1_subset_1(B_116,A_115)
      | ~ v2_lattice3(k2_yellow_1(A_115)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_24,c_34,c_215])).

tff(c_298,plain,(
    ! [B_118,C_119,A_120] :
      ( r1_tarski(B_118,C_119)
      | v1_xboole_0(A_120)
      | k12_lattice3(k2_yellow_1(A_120),B_118,C_119) != B_118
      | ~ m1_subset_1(C_119,A_120)
      | ~ m1_subset_1(B_118,A_120)
      | ~ v2_lattice3(k2_yellow_1(A_120)) ) ),
    inference(resolution,[status(thm)],[c_293,c_53])).

tff(c_300,plain,(
    ! [B_100,C_101] :
      ( r1_tarski(B_100,C_101)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_100,C_101) != B_100
      | ~ m1_subset_1(C_101,'#skF_1')
      | ~ m1_subset_1(B_100,'#skF_1')
      | ~ v2_lattice3(k2_yellow_1('#skF_1'))
      | ~ m1_subset_1(C_101,'#skF_1')
      | ~ m1_subset_1(B_100,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_298])).

tff(c_302,plain,(
    ! [B_100,C_101] :
      ( r1_tarski(B_100,C_101)
      | v1_xboole_0('#skF_1')
      | k11_lattice3(k2_yellow_1('#skF_1'),B_100,C_101) != B_100
      | ~ m1_subset_1(C_101,'#skF_1')
      | ~ m1_subset_1(B_100,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_300])).

tff(c_304,plain,(
    ! [B_121,C_122] :
      ( r1_tarski(B_121,C_122)
      | k11_lattice3(k2_yellow_1('#skF_1'),B_121,C_122) != B_121
      | ~ m1_subset_1(C_122,'#skF_1')
      | ~ m1_subset_1(B_121,'#skF_1') ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_302])).

tff(c_307,plain,(
    ! [B_109,C_108] :
      ( r1_tarski(B_109,C_108)
      | k11_lattice3(k2_yellow_1('#skF_1'),C_108,B_109) != B_109
      | ~ m1_subset_1(C_108,'#skF_1')
      | ~ m1_subset_1(B_109,'#skF_1')
      | ~ m1_subset_1(C_108,'#skF_1')
      | ~ m1_subset_1(B_109,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_304])).

tff(c_787,plain,(
    ! [B_153,D_154] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),B_153,D_154),B_153)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),B_153,D_154),'#skF_1')
      | ~ m1_subset_1(D_154,'#skF_1')
      | ~ m1_subset_1(B_153,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_700,c_307])).

tff(c_89,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k3_xboole_0(B_70,C_71))
      | ~ r1_tarski(A_69,C_71)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_93,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_3')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_89,c_42])).

tff(c_95,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_790,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_787,c_95])).

tff(c_815,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_52,c_790])).

tff(c_832,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_106,c_815])).

tff(c_844,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_52,c_832])).

tff(c_845,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_2','#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_1010,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_974,c_845])).

tff(c_1044,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_51,c_1010])).

tff(c_1578,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1575,c_1044])).

tff(c_1603,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'),'#skF_3','#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_51,c_1578])).

tff(c_1614,plain,
    ( ~ m1_subset_1('#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_857,c_1603])).

tff(c_1622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_51,c_1614])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:34 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.82  
% 4.11/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.82  %$ r3_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.11/1.82  
% 4.11/1.82  %Foreground sorts:
% 4.11/1.82  
% 4.11/1.82  
% 4.11/1.82  %Background operators:
% 4.11/1.82  
% 4.11/1.82  
% 4.11/1.82  %Foreground operators:
% 4.11/1.82  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.11/1.82  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.11/1.82  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.11/1.82  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.11/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.82  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.11/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.11/1.82  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.11/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.11/1.82  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 4.11/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.11/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.11/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.11/1.82  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.11/1.82  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.11/1.82  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.11/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.82  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.11/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.11/1.82  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.11/1.82  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.11/1.82  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.11/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.11/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.82  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.11/1.82  
% 4.11/1.84  tff(f_140, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 4.11/1.84  tff(f_167, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 4.11/1.84  tff(f_128, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.11/1.84  tff(f_61, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 4.11/1.84  tff(f_136, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.11/1.84  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => r3_orders_2(A, B, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r3_orders_2)).
% 4.11/1.84  tff(f_53, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 4.11/1.84  tff(f_124, axiom, (![A]: ((((v3_orders_2(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((B = k12_lattice3(A, B, C)) <=> r3_orders_2(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_yellow_0)).
% 4.11/1.84  tff(f_73, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 4.11/1.84  tff(f_106, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => (v4_orders_2(A) => (k11_lattice3(A, k11_lattice3(A, B, C), D) = k11_lattice3(A, B, k11_lattice3(A, C, D)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_lattice3)).
% 4.11/1.84  tff(f_87, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 4.11/1.84  tff(f_153, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.11/1.84  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.11/1.84  tff(c_34, plain, (![A_47]: (u1_struct_0(k2_yellow_1(A_47))=A_47)), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.11/1.84  tff(c_44, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.84  tff(c_52, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44])).
% 4.11/1.84  tff(c_46, plain, (m1_subset_1('#skF_2', u1_struct_0(k2_yellow_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.84  tff(c_51, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_46])).
% 4.11/1.84  tff(c_24, plain, (![A_45]: (l1_orders_2(k2_yellow_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.11/1.84  tff(c_852, plain, (![A_158, B_159, C_160]: (m1_subset_1(k11_lattice3(A_158, B_159, C_160), u1_struct_0(A_158)) | ~m1_subset_1(C_160, u1_struct_0(A_158)) | ~m1_subset_1(B_159, u1_struct_0(A_158)) | ~l1_orders_2(A_158))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.11/1.84  tff(c_855, plain, (![A_47, B_159, C_160]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_47), B_159, C_160), A_47) | ~m1_subset_1(C_160, u1_struct_0(k2_yellow_1(A_47))) | ~m1_subset_1(B_159, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_852])).
% 4.11/1.84  tff(c_857, plain, (![A_47, B_159, C_160]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_47), B_159, C_160), A_47) | ~m1_subset_1(C_160, A_47) | ~m1_subset_1(B_159, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34, c_34, c_855])).
% 4.11/1.84  tff(c_48, plain, (v2_lattice3(k2_yellow_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.84  tff(c_28, plain, (![A_46]: (v3_orders_2(k2_yellow_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.11/1.84  tff(c_32, plain, (![A_46]: (v5_orders_2(k2_yellow_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.11/1.84  tff(c_859, plain, (![A_164, B_165, C_166]: (r3_orders_2(A_164, B_165, B_165) | ~m1_subset_1(C_166, u1_struct_0(A_164)) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_orders_2(A_164) | ~v3_orders_2(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.11/1.84  tff(c_866, plain, (![A_47, B_165, C_166]: (r3_orders_2(k2_yellow_1(A_47), B_165, B_165) | ~m1_subset_1(C_166, A_47) | ~m1_subset_1(B_165, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v3_orders_2(k2_yellow_1(A_47)) | v2_struct_0(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_859])).
% 4.11/1.84  tff(c_883, plain, (![A_170, B_171, C_172]: (r3_orders_2(k2_yellow_1(A_170), B_171, B_171) | ~m1_subset_1(C_172, A_170) | ~m1_subset_1(B_171, A_170) | v2_struct_0(k2_yellow_1(A_170)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_34, c_866])).
% 4.11/1.84  tff(c_894, plain, (![B_171]: (r3_orders_2(k2_yellow_1('#skF_1'), B_171, B_171) | ~m1_subset_1(B_171, '#skF_1') | v2_struct_0(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_883])).
% 4.11/1.84  tff(c_896, plain, (v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_894])).
% 4.11/1.84  tff(c_8, plain, (![A_9]: (~v2_struct_0(A_9) | ~v2_lattice3(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.11/1.84  tff(c_899, plain, (~v2_lattice3(k2_yellow_1('#skF_1')) | ~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_896, c_8])).
% 4.11/1.84  tff(c_903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_48, c_899])).
% 4.11/1.84  tff(c_905, plain, (~v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitRight, [status(thm)], [c_894])).
% 4.11/1.84  tff(c_895, plain, (![B_171]: (r3_orders_2(k2_yellow_1('#skF_1'), B_171, B_171) | ~m1_subset_1(B_171, '#skF_1') | v2_struct_0(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_51, c_883])).
% 4.11/1.84  tff(c_906, plain, (v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_895])).
% 4.11/1.84  tff(c_907, plain, $false, inference(negUnitSimplification, [status(thm)], [c_905, c_906])).
% 4.11/1.84  tff(c_908, plain, (![B_171]: (r3_orders_2(k2_yellow_1('#skF_1'), B_171, B_171) | ~m1_subset_1(B_171, '#skF_1'))), inference(splitRight, [status(thm)], [c_895])).
% 4.11/1.84  tff(c_1053, plain, (![A_195, B_196, C_197]: (k12_lattice3(A_195, B_196, C_197)=B_196 | ~r3_orders_2(A_195, B_196, C_197) | ~m1_subset_1(C_197, u1_struct_0(A_195)) | ~m1_subset_1(B_196, u1_struct_0(A_195)) | ~l1_orders_2(A_195) | ~v2_lattice3(A_195) | ~v5_orders_2(A_195) | ~v3_orders_2(A_195))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.11/1.84  tff(c_1055, plain, (![B_171]: (k12_lattice3(k2_yellow_1('#skF_1'), B_171, B_171)=B_171 | ~m1_subset_1(B_171, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')) | ~v3_orders_2(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_171, '#skF_1'))), inference(resolution, [status(thm)], [c_908, c_1053])).
% 4.11/1.84  tff(c_1071, plain, (![B_198]: (k12_lattice3(k2_yellow_1('#skF_1'), B_198, B_198)=B_198 | ~m1_subset_1(B_198, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_48, c_24, c_34, c_1055])).
% 4.11/1.84  tff(c_871, plain, (![A_167, B_168, C_169]: (k12_lattice3(A_167, B_168, C_169)=k11_lattice3(A_167, B_168, C_169) | ~m1_subset_1(C_169, u1_struct_0(A_167)) | ~m1_subset_1(B_168, u1_struct_0(A_167)) | ~l1_orders_2(A_167) | ~v2_lattice3(A_167) | ~v5_orders_2(A_167))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.11/1.84  tff(c_878, plain, (![A_47, B_168, C_169]: (k12_lattice3(k2_yellow_1(A_47), B_168, C_169)=k11_lattice3(k2_yellow_1(A_47), B_168, C_169) | ~m1_subset_1(C_169, A_47) | ~m1_subset_1(B_168, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v2_lattice3(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_871])).
% 4.11/1.84  tff(c_957, plain, (![A_185, B_186, C_187]: (k12_lattice3(k2_yellow_1(A_185), B_186, C_187)=k11_lattice3(k2_yellow_1(A_185), B_186, C_187) | ~m1_subset_1(C_187, A_185) | ~m1_subset_1(B_186, A_185) | ~v2_lattice3(k2_yellow_1(A_185)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_34, c_878])).
% 4.11/1.84  tff(c_960, plain, (![B_186, C_187]: (k12_lattice3(k2_yellow_1('#skF_1'), B_186, C_187)=k11_lattice3(k2_yellow_1('#skF_1'), B_186, C_187) | ~m1_subset_1(C_187, '#skF_1') | ~m1_subset_1(B_186, '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_957])).
% 4.11/1.84  tff(c_1077, plain, (![B_198]: (k11_lattice3(k2_yellow_1('#skF_1'), B_198, B_198)=B_198 | ~m1_subset_1(B_198, '#skF_1') | ~m1_subset_1(B_198, '#skF_1') | ~m1_subset_1(B_198, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1071, c_960])).
% 4.11/1.84  tff(c_30, plain, (![A_46]: (v4_orders_2(k2_yellow_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_136])).
% 4.11/1.84  tff(c_1114, plain, (![A_203, B_204, C_205, D_206]: (k11_lattice3(A_203, k11_lattice3(A_203, B_204, C_205), D_206)=k11_lattice3(A_203, B_204, k11_lattice3(A_203, C_205, D_206)) | ~v4_orders_2(A_203) | ~m1_subset_1(D_206, u1_struct_0(A_203)) | ~m1_subset_1(C_205, u1_struct_0(A_203)) | ~m1_subset_1(B_204, u1_struct_0(A_203)) | ~l1_orders_2(A_203) | ~v2_lattice3(A_203) | ~v5_orders_2(A_203))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.11/1.84  tff(c_1121, plain, (![A_47, B_204, C_205, D_206]: (k11_lattice3(k2_yellow_1(A_47), k11_lattice3(k2_yellow_1(A_47), B_204, C_205), D_206)=k11_lattice3(k2_yellow_1(A_47), B_204, k11_lattice3(k2_yellow_1(A_47), C_205, D_206)) | ~v4_orders_2(k2_yellow_1(A_47)) | ~m1_subset_1(D_206, A_47) | ~m1_subset_1(C_205, u1_struct_0(k2_yellow_1(A_47))) | ~m1_subset_1(B_204, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v2_lattice3(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1114])).
% 4.11/1.84  tff(c_1368, plain, (![A_227, B_228, C_229, D_230]: (k11_lattice3(k2_yellow_1(A_227), k11_lattice3(k2_yellow_1(A_227), B_228, C_229), D_230)=k11_lattice3(k2_yellow_1(A_227), B_228, k11_lattice3(k2_yellow_1(A_227), C_229, D_230)) | ~m1_subset_1(D_230, A_227) | ~m1_subset_1(C_229, A_227) | ~m1_subset_1(B_228, A_227) | ~v2_lattice3(k2_yellow_1(A_227)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_34, c_34, c_30, c_1121])).
% 4.11/1.84  tff(c_1431, plain, (![B_198, D_230]: (k11_lattice3(k2_yellow_1('#skF_1'), B_198, k11_lattice3(k2_yellow_1('#skF_1'), B_198, D_230))=k11_lattice3(k2_yellow_1('#skF_1'), B_198, D_230) | ~m1_subset_1(D_230, '#skF_1') | ~m1_subset_1(B_198, '#skF_1') | ~m1_subset_1(B_198, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_198, '#skF_1') | ~m1_subset_1(B_198, '#skF_1') | ~m1_subset_1(B_198, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1077, c_1368])).
% 4.11/1.84  tff(c_1488, plain, (![B_231, D_232]: (k11_lattice3(k2_yellow_1('#skF_1'), B_231, k11_lattice3(k2_yellow_1('#skF_1'), B_231, D_232))=k11_lattice3(k2_yellow_1('#skF_1'), B_231, D_232) | ~m1_subset_1(D_232, '#skF_1') | ~m1_subset_1(B_231, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1431])).
% 4.11/1.84  tff(c_917, plain, (![A_174, C_175, B_176]: (k11_lattice3(A_174, C_175, B_176)=k11_lattice3(A_174, B_176, C_175) | ~m1_subset_1(C_175, u1_struct_0(A_174)) | ~m1_subset_1(B_176, u1_struct_0(A_174)) | ~l1_orders_2(A_174) | ~v2_lattice3(A_174) | ~v5_orders_2(A_174))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.84  tff(c_924, plain, (![A_47, C_175, B_176]: (k11_lattice3(k2_yellow_1(A_47), C_175, B_176)=k11_lattice3(k2_yellow_1(A_47), B_176, C_175) | ~m1_subset_1(C_175, A_47) | ~m1_subset_1(B_176, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v2_lattice3(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_917])).
% 4.11/1.84  tff(c_970, plain, (![A_190, C_191, B_192]: (k11_lattice3(k2_yellow_1(A_190), C_191, B_192)=k11_lattice3(k2_yellow_1(A_190), B_192, C_191) | ~m1_subset_1(C_191, A_190) | ~m1_subset_1(B_192, A_190) | ~v2_lattice3(k2_yellow_1(A_190)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_34, c_924])).
% 4.11/1.84  tff(c_973, plain, (![C_191, B_192]: (k11_lattice3(k2_yellow_1('#skF_1'), C_191, B_192)=k11_lattice3(k2_yellow_1('#skF_1'), B_192, C_191) | ~m1_subset_1(C_191, '#skF_1') | ~m1_subset_1(B_192, '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_970])).
% 4.11/1.84  tff(c_50, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.84  tff(c_945, plain, (![A_182, B_183, C_184]: (r3_orders_2(A_182, B_183, C_184) | k12_lattice3(A_182, B_183, C_184)!=B_183 | ~m1_subset_1(C_184, u1_struct_0(A_182)) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~l1_orders_2(A_182) | ~v2_lattice3(A_182) | ~v5_orders_2(A_182) | ~v3_orders_2(A_182))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.11/1.84  tff(c_952, plain, (![A_47, B_183, C_184]: (r3_orders_2(k2_yellow_1(A_47), B_183, C_184) | k12_lattice3(k2_yellow_1(A_47), B_183, C_184)!=B_183 | ~m1_subset_1(C_184, A_47) | ~m1_subset_1(B_183, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v2_lattice3(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)) | ~v3_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_945])).
% 4.11/1.84  tff(c_1104, plain, (![A_200, B_201, C_202]: (r3_orders_2(k2_yellow_1(A_200), B_201, C_202) | k12_lattice3(k2_yellow_1(A_200), B_201, C_202)!=B_201 | ~m1_subset_1(C_202, A_200) | ~m1_subset_1(B_201, A_200) | ~v2_lattice3(k2_yellow_1(A_200)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_24, c_34, c_952])).
% 4.11/1.84  tff(c_40, plain, (![B_52, C_54, A_48]: (r1_tarski(B_52, C_54) | ~r3_orders_2(k2_yellow_1(A_48), B_52, C_54) | ~m1_subset_1(C_54, u1_struct_0(k2_yellow_1(A_48))) | ~m1_subset_1(B_52, u1_struct_0(k2_yellow_1(A_48))) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_153])).
% 4.11/1.84  tff(c_53, plain, (![B_52, C_54, A_48]: (r1_tarski(B_52, C_54) | ~r3_orders_2(k2_yellow_1(A_48), B_52, C_54) | ~m1_subset_1(C_54, A_48) | ~m1_subset_1(B_52, A_48) | v1_xboole_0(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_34, c_40])).
% 4.11/1.84  tff(c_1156, plain, (![B_212, C_213, A_214]: (r1_tarski(B_212, C_213) | v1_xboole_0(A_214) | k12_lattice3(k2_yellow_1(A_214), B_212, C_213)!=B_212 | ~m1_subset_1(C_213, A_214) | ~m1_subset_1(B_212, A_214) | ~v2_lattice3(k2_yellow_1(A_214)))), inference(resolution, [status(thm)], [c_1104, c_53])).
% 4.11/1.84  tff(c_1162, plain, (![B_186, C_187]: (r1_tarski(B_186, C_187) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_186, C_187)!=B_186 | ~m1_subset_1(C_187, '#skF_1') | ~m1_subset_1(B_186, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_187, '#skF_1') | ~m1_subset_1(B_186, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_960, c_1156])).
% 4.11/1.84  tff(c_1172, plain, (![B_186, C_187]: (r1_tarski(B_186, C_187) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_186, C_187)!=B_186 | ~m1_subset_1(C_187, '#skF_1') | ~m1_subset_1(B_186, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1162])).
% 4.11/1.84  tff(c_1174, plain, (![B_215, C_216]: (r1_tarski(B_215, C_216) | k11_lattice3(k2_yellow_1('#skF_1'), B_215, C_216)!=B_215 | ~m1_subset_1(C_216, '#skF_1') | ~m1_subset_1(B_215, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_1172])).
% 4.11/1.84  tff(c_1180, plain, (![B_192, C_191]: (r1_tarski(B_192, C_191) | k11_lattice3(k2_yellow_1('#skF_1'), C_191, B_192)!=B_192 | ~m1_subset_1(C_191, '#skF_1') | ~m1_subset_1(B_192, '#skF_1') | ~m1_subset_1(C_191, '#skF_1') | ~m1_subset_1(B_192, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_973, c_1174])).
% 4.11/1.84  tff(c_1575, plain, (![B_233, D_234]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), B_233, D_234), B_233) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), B_233, D_234), '#skF_1') | ~m1_subset_1(D_234, '#skF_1') | ~m1_subset_1(B_233, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1488, c_1180])).
% 4.11/1.84  tff(c_974, plain, (![C_193, B_194]: (k11_lattice3(k2_yellow_1('#skF_1'), C_193, B_194)=k11_lattice3(k2_yellow_1('#skF_1'), B_194, C_193) | ~m1_subset_1(C_193, '#skF_1') | ~m1_subset_1(B_194, '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_970])).
% 4.11/1.84  tff(c_101, plain, (![A_78, B_79, C_80]: (m1_subset_1(k11_lattice3(A_78, B_79, C_80), u1_struct_0(A_78)) | ~m1_subset_1(C_80, u1_struct_0(A_78)) | ~m1_subset_1(B_79, u1_struct_0(A_78)) | ~l1_orders_2(A_78))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.11/1.84  tff(c_104, plain, (![A_47, B_79, C_80]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_47), B_79, C_80), A_47) | ~m1_subset_1(C_80, u1_struct_0(k2_yellow_1(A_47))) | ~m1_subset_1(B_79, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_101])).
% 4.11/1.84  tff(c_106, plain, (![A_47, B_79, C_80]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_47), B_79, C_80), A_47) | ~m1_subset_1(C_80, A_47) | ~m1_subset_1(B_79, A_47))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34, c_34, c_104])).
% 4.11/1.84  tff(c_108, plain, (![A_84, B_85, C_86]: (r3_orders_2(A_84, B_85, B_85) | ~m1_subset_1(C_86, u1_struct_0(A_84)) | ~m1_subset_1(B_85, u1_struct_0(A_84)) | ~l1_orders_2(A_84) | ~v3_orders_2(A_84) | v2_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.11/1.84  tff(c_115, plain, (![A_47, B_85, C_86]: (r3_orders_2(k2_yellow_1(A_47), B_85, B_85) | ~m1_subset_1(C_86, A_47) | ~m1_subset_1(B_85, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v3_orders_2(k2_yellow_1(A_47)) | v2_struct_0(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_108])).
% 4.11/1.84  tff(c_120, plain, (![A_87, B_88, C_89]: (r3_orders_2(k2_yellow_1(A_87), B_88, B_88) | ~m1_subset_1(C_89, A_87) | ~m1_subset_1(B_88, A_87) | v2_struct_0(k2_yellow_1(A_87)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_34, c_115])).
% 4.11/1.84  tff(c_131, plain, (![B_88]: (r3_orders_2(k2_yellow_1('#skF_1'), B_88, B_88) | ~m1_subset_1(B_88, '#skF_1') | v2_struct_0(k2_yellow_1('#skF_1')))), inference(resolution, [status(thm)], [c_52, c_120])).
% 4.11/1.84  tff(c_133, plain, (v2_struct_0(k2_yellow_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_131])).
% 4.11/1.84  tff(c_136, plain, (~v2_lattice3(k2_yellow_1('#skF_1')) | ~l1_orders_2(k2_yellow_1('#skF_1'))), inference(resolution, [status(thm)], [c_133, c_8])).
% 4.11/1.84  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_48, c_136])).
% 4.11/1.84  tff(c_141, plain, (![B_88]: (r3_orders_2(k2_yellow_1('#skF_1'), B_88, B_88) | ~m1_subset_1(B_88, '#skF_1'))), inference(splitRight, [status(thm)], [c_131])).
% 4.11/1.84  tff(c_318, plain, (![A_125, B_126, C_127]: (k12_lattice3(A_125, B_126, C_127)=B_126 | ~r3_orders_2(A_125, B_126, C_127) | ~m1_subset_1(C_127, u1_struct_0(A_125)) | ~m1_subset_1(B_126, u1_struct_0(A_125)) | ~l1_orders_2(A_125) | ~v2_lattice3(A_125) | ~v5_orders_2(A_125) | ~v3_orders_2(A_125))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.11/1.84  tff(c_322, plain, (![B_88]: (k12_lattice3(k2_yellow_1('#skF_1'), B_88, B_88)=B_88 | ~m1_subset_1(B_88, u1_struct_0(k2_yellow_1('#skF_1'))) | ~l1_orders_2(k2_yellow_1('#skF_1')) | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~v5_orders_2(k2_yellow_1('#skF_1')) | ~v3_orders_2(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_88, '#skF_1'))), inference(resolution, [status(thm)], [c_141, c_318])).
% 4.11/1.84  tff(c_334, plain, (![B_128]: (k12_lattice3(k2_yellow_1('#skF_1'), B_128, B_128)=B_128 | ~m1_subset_1(B_128, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_48, c_24, c_34, c_322])).
% 4.11/1.84  tff(c_143, plain, (![A_90, B_91, C_92]: (k12_lattice3(A_90, B_91, C_92)=k11_lattice3(A_90, B_91, C_92) | ~m1_subset_1(C_92, u1_struct_0(A_90)) | ~m1_subset_1(B_91, u1_struct_0(A_90)) | ~l1_orders_2(A_90) | ~v2_lattice3(A_90) | ~v5_orders_2(A_90))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.11/1.84  tff(c_150, plain, (![A_47, B_91, C_92]: (k12_lattice3(k2_yellow_1(A_47), B_91, C_92)=k11_lattice3(k2_yellow_1(A_47), B_91, C_92) | ~m1_subset_1(C_92, A_47) | ~m1_subset_1(B_91, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v2_lattice3(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_143])).
% 4.11/1.84  tff(c_179, plain, (![A_99, B_100, C_101]: (k12_lattice3(k2_yellow_1(A_99), B_100, C_101)=k11_lattice3(k2_yellow_1(A_99), B_100, C_101) | ~m1_subset_1(C_101, A_99) | ~m1_subset_1(B_100, A_99) | ~v2_lattice3(k2_yellow_1(A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_34, c_150])).
% 4.11/1.84  tff(c_182, plain, (![B_100, C_101]: (k12_lattice3(k2_yellow_1('#skF_1'), B_100, C_101)=k11_lattice3(k2_yellow_1('#skF_1'), B_100, C_101) | ~m1_subset_1(C_101, '#skF_1') | ~m1_subset_1(B_100, '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_179])).
% 4.11/1.84  tff(c_342, plain, (![B_128]: (k11_lattice3(k2_yellow_1('#skF_1'), B_128, B_128)=B_128 | ~m1_subset_1(B_128, '#skF_1') | ~m1_subset_1(B_128, '#skF_1') | ~m1_subset_1(B_128, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_334, c_182])).
% 4.11/1.84  tff(c_484, plain, (![A_137, B_138, C_139, D_140]: (k11_lattice3(A_137, k11_lattice3(A_137, B_138, C_139), D_140)=k11_lattice3(A_137, B_138, k11_lattice3(A_137, C_139, D_140)) | ~v4_orders_2(A_137) | ~m1_subset_1(D_140, u1_struct_0(A_137)) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v2_lattice3(A_137) | ~v5_orders_2(A_137))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.11/1.84  tff(c_491, plain, (![A_47, B_138, C_139, D_140]: (k11_lattice3(k2_yellow_1(A_47), k11_lattice3(k2_yellow_1(A_47), B_138, C_139), D_140)=k11_lattice3(k2_yellow_1(A_47), B_138, k11_lattice3(k2_yellow_1(A_47), C_139, D_140)) | ~v4_orders_2(k2_yellow_1(A_47)) | ~m1_subset_1(D_140, A_47) | ~m1_subset_1(C_139, u1_struct_0(k2_yellow_1(A_47))) | ~m1_subset_1(B_138, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v2_lattice3(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_484])).
% 4.11/1.84  tff(c_580, plain, (![A_147, B_148, C_149, D_150]: (k11_lattice3(k2_yellow_1(A_147), k11_lattice3(k2_yellow_1(A_147), B_148, C_149), D_150)=k11_lattice3(k2_yellow_1(A_147), B_148, k11_lattice3(k2_yellow_1(A_147), C_149, D_150)) | ~m1_subset_1(D_150, A_147) | ~m1_subset_1(C_149, A_147) | ~m1_subset_1(B_148, A_147) | ~v2_lattice3(k2_yellow_1(A_147)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_34, c_34, c_30, c_491])).
% 4.11/1.84  tff(c_643, plain, (![B_128, D_150]: (k11_lattice3(k2_yellow_1('#skF_1'), B_128, k11_lattice3(k2_yellow_1('#skF_1'), B_128, D_150))=k11_lattice3(k2_yellow_1('#skF_1'), B_128, D_150) | ~m1_subset_1(D_150, '#skF_1') | ~m1_subset_1(B_128, '#skF_1') | ~m1_subset_1(B_128, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(B_128, '#skF_1') | ~m1_subset_1(B_128, '#skF_1') | ~m1_subset_1(B_128, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_580])).
% 4.11/1.84  tff(c_700, plain, (![B_151, D_152]: (k11_lattice3(k2_yellow_1('#skF_1'), B_151, k11_lattice3(k2_yellow_1('#skF_1'), B_151, D_152))=k11_lattice3(k2_yellow_1('#skF_1'), B_151, D_152) | ~m1_subset_1(D_152, '#skF_1') | ~m1_subset_1(B_151, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_643])).
% 4.11/1.84  tff(c_192, plain, (![A_104, C_105, B_106]: (k11_lattice3(A_104, C_105, B_106)=k11_lattice3(A_104, B_106, C_105) | ~m1_subset_1(C_105, u1_struct_0(A_104)) | ~m1_subset_1(B_106, u1_struct_0(A_104)) | ~l1_orders_2(A_104) | ~v2_lattice3(A_104) | ~v5_orders_2(A_104))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.11/1.84  tff(c_199, plain, (![A_47, C_105, B_106]: (k11_lattice3(k2_yellow_1(A_47), C_105, B_106)=k11_lattice3(k2_yellow_1(A_47), B_106, C_105) | ~m1_subset_1(C_105, A_47) | ~m1_subset_1(B_106, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v2_lattice3(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_192])).
% 4.11/1.84  tff(c_204, plain, (![A_107, C_108, B_109]: (k11_lattice3(k2_yellow_1(A_107), C_108, B_109)=k11_lattice3(k2_yellow_1(A_107), B_109, C_108) | ~m1_subset_1(C_108, A_107) | ~m1_subset_1(B_109, A_107) | ~v2_lattice3(k2_yellow_1(A_107)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_24, c_34, c_199])).
% 4.11/1.84  tff(c_207, plain, (![C_108, B_109]: (k11_lattice3(k2_yellow_1('#skF_1'), C_108, B_109)=k11_lattice3(k2_yellow_1('#skF_1'), B_109, C_108) | ~m1_subset_1(C_108, '#skF_1') | ~m1_subset_1(B_109, '#skF_1'))), inference(resolution, [status(thm)], [c_48, c_204])).
% 4.11/1.84  tff(c_208, plain, (![A_110, B_111, C_112]: (r3_orders_2(A_110, B_111, C_112) | k12_lattice3(A_110, B_111, C_112)!=B_111 | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~m1_subset_1(B_111, u1_struct_0(A_110)) | ~l1_orders_2(A_110) | ~v2_lattice3(A_110) | ~v5_orders_2(A_110) | ~v3_orders_2(A_110))), inference(cnfTransformation, [status(thm)], [f_124])).
% 4.11/1.84  tff(c_215, plain, (![A_47, B_111, C_112]: (r3_orders_2(k2_yellow_1(A_47), B_111, C_112) | k12_lattice3(k2_yellow_1(A_47), B_111, C_112)!=B_111 | ~m1_subset_1(C_112, A_47) | ~m1_subset_1(B_111, u1_struct_0(k2_yellow_1(A_47))) | ~l1_orders_2(k2_yellow_1(A_47)) | ~v2_lattice3(k2_yellow_1(A_47)) | ~v5_orders_2(k2_yellow_1(A_47)) | ~v3_orders_2(k2_yellow_1(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_208])).
% 4.11/1.84  tff(c_293, plain, (![A_115, B_116, C_117]: (r3_orders_2(k2_yellow_1(A_115), B_116, C_117) | k12_lattice3(k2_yellow_1(A_115), B_116, C_117)!=B_116 | ~m1_subset_1(C_117, A_115) | ~m1_subset_1(B_116, A_115) | ~v2_lattice3(k2_yellow_1(A_115)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_24, c_34, c_215])).
% 4.11/1.84  tff(c_298, plain, (![B_118, C_119, A_120]: (r1_tarski(B_118, C_119) | v1_xboole_0(A_120) | k12_lattice3(k2_yellow_1(A_120), B_118, C_119)!=B_118 | ~m1_subset_1(C_119, A_120) | ~m1_subset_1(B_118, A_120) | ~v2_lattice3(k2_yellow_1(A_120)))), inference(resolution, [status(thm)], [c_293, c_53])).
% 4.11/1.84  tff(c_300, plain, (![B_100, C_101]: (r1_tarski(B_100, C_101) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_100, C_101)!=B_100 | ~m1_subset_1(C_101, '#skF_1') | ~m1_subset_1(B_100, '#skF_1') | ~v2_lattice3(k2_yellow_1('#skF_1')) | ~m1_subset_1(C_101, '#skF_1') | ~m1_subset_1(B_100, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_298])).
% 4.11/1.84  tff(c_302, plain, (![B_100, C_101]: (r1_tarski(B_100, C_101) | v1_xboole_0('#skF_1') | k11_lattice3(k2_yellow_1('#skF_1'), B_100, C_101)!=B_100 | ~m1_subset_1(C_101, '#skF_1') | ~m1_subset_1(B_100, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_300])).
% 4.11/1.84  tff(c_304, plain, (![B_121, C_122]: (r1_tarski(B_121, C_122) | k11_lattice3(k2_yellow_1('#skF_1'), B_121, C_122)!=B_121 | ~m1_subset_1(C_122, '#skF_1') | ~m1_subset_1(B_121, '#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_50, c_302])).
% 4.11/1.84  tff(c_307, plain, (![B_109, C_108]: (r1_tarski(B_109, C_108) | k11_lattice3(k2_yellow_1('#skF_1'), C_108, B_109)!=B_109 | ~m1_subset_1(C_108, '#skF_1') | ~m1_subset_1(B_109, '#skF_1') | ~m1_subset_1(C_108, '#skF_1') | ~m1_subset_1(B_109, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_304])).
% 4.11/1.84  tff(c_787, plain, (![B_153, D_154]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), B_153, D_154), B_153) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), B_153, D_154), '#skF_1') | ~m1_subset_1(D_154, '#skF_1') | ~m1_subset_1(B_153, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_700, c_307])).
% 4.11/1.84  tff(c_89, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k3_xboole_0(B_70, C_71)) | ~r1_tarski(A_69, C_71) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.11/1.84  tff(c_42, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 4.11/1.84  tff(c_93, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_3') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_89, c_42])).
% 4.11/1.84  tff(c_95, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_93])).
% 4.11/1.84  tff(c_790, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_787, c_95])).
% 4.11/1.84  tff(c_815, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_52, c_790])).
% 4.11/1.84  tff(c_832, plain, (~m1_subset_1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_106, c_815])).
% 4.11/1.84  tff(c_844, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_52, c_832])).
% 4.11/1.84  tff(c_845, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_2', '#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_93])).
% 4.11/1.84  tff(c_1010, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_974, c_845])).
% 4.11/1.84  tff(c_1044, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_51, c_1010])).
% 4.11/1.84  tff(c_1578, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1575, c_1044])).
% 4.11/1.84  tff(c_1603, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_1'), '#skF_3', '#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_51, c_1578])).
% 4.11/1.84  tff(c_1614, plain, (~m1_subset_1('#skF_2', '#skF_1') | ~m1_subset_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_857, c_1603])).
% 4.11/1.84  tff(c_1622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_51, c_1614])).
% 4.11/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.11/1.84  
% 4.11/1.84  Inference rules
% 4.11/1.84  ----------------------
% 4.11/1.84  #Ref     : 0
% 4.11/1.84  #Sup     : 351
% 4.11/1.84  #Fact    : 0
% 4.11/1.84  #Define  : 0
% 4.11/1.84  #Split   : 6
% 4.11/1.84  #Chain   : 0
% 4.11/1.84  #Close   : 0
% 4.11/1.84  
% 4.11/1.84  Ordering : KBO
% 4.11/1.84  
% 4.11/1.84  Simplification rules
% 4.11/1.84  ----------------------
% 4.11/1.84  #Subsume      : 88
% 4.11/1.84  #Demod        : 355
% 4.11/1.84  #Tautology    : 107
% 4.11/1.84  #SimpNegUnit  : 17
% 4.11/1.84  #BackRed      : 0
% 4.11/1.84  
% 4.11/1.84  #Partial instantiations: 0
% 4.11/1.84  #Strategies tried      : 1
% 4.11/1.84  
% 4.11/1.84  Timing (in seconds)
% 4.11/1.84  ----------------------
% 4.11/1.85  Preprocessing        : 0.45
% 4.11/1.85  Parsing              : 0.25
% 4.11/1.85  CNF conversion       : 0.03
% 4.11/1.85  Main loop            : 0.53
% 4.11/1.85  Inferencing          : 0.20
% 4.11/1.85  Reduction            : 0.17
% 4.11/1.85  Demodulation         : 0.12
% 4.11/1.85  BG Simplification    : 0.04
% 4.11/1.85  Subsumption          : 0.09
% 4.11/1.85  Abstraction          : 0.04
% 4.11/1.85  MUC search           : 0.00
% 4.11/1.85  Cooper               : 0.00
% 4.11/1.85  Total                : 1.03
% 4.11/1.85  Index Insertion      : 0.00
% 4.11/1.85  Index Deletion       : 0.00
% 4.11/1.85  Index Matching       : 0.00
% 4.11/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
