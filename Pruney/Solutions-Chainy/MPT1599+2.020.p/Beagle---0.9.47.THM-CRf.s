%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:25 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 419 expanded)
%              Number of leaves         :   38 ( 174 expanded)
%              Depth                    :   13
%              Number of atoms          :  363 (1219 expanded)
%              Number of equality atoms :   20 ( 201 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k11_lattice3,type,(
    k11_lattice3: ( $i * $i * $i ) > $i )).

tff(k12_lattice3,type,(
    k12_lattice3: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_165,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_118,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_114,axiom,(
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
                 => ( D = k12_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

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

tff(f_151,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_134,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => k11_lattice3(A,B,C) = k11_lattice3(A,C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_44,plain,(
    ! [A_69] : u1_struct_0(k2_yellow_1(A_69)) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_61,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_62,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54])).

tff(c_58,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_38,plain,(
    ! [A_67] : v5_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_30,plain,(
    ! [A_66] : l1_orders_2(k2_yellow_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_497,plain,(
    ! [A_189,B_190,C_191] :
      ( k12_lattice3(A_189,B_190,C_191) = k11_lattice3(A_189,B_190,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_189))
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | ~ v2_lattice3(A_189)
      | ~ v5_orders_2(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_504,plain,(
    ! [A_69,B_190,C_191] :
      ( k12_lattice3(k2_yellow_1(A_69),B_190,C_191) = k11_lattice3(k2_yellow_1(A_69),B_190,C_191)
      | ~ m1_subset_1(C_191,A_69)
      | ~ m1_subset_1(B_190,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v2_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_497])).

tff(c_509,plain,(
    ! [A_192,B_193,C_194] :
      ( k12_lattice3(k2_yellow_1(A_192),B_193,C_194) = k11_lattice3(k2_yellow_1(A_192),B_193,C_194)
      | ~ m1_subset_1(C_194,A_192)
      | ~ m1_subset_1(B_193,A_192)
      | ~ v2_lattice3(k2_yellow_1(A_192)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_504])).

tff(c_513,plain,(
    ! [B_195,C_196] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_195,C_196) = k11_lattice3(k2_yellow_1('#skF_2'),B_195,C_196)
      | ~ m1_subset_1(C_196,'#skF_2')
      | ~ m1_subset_1(B_195,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_509])).

tff(c_370,plain,(
    ! [A_160,B_161,C_162] :
      ( m1_subset_1(k12_lattice3(A_160,B_161,C_162),u1_struct_0(A_160))
      | ~ m1_subset_1(C_162,u1_struct_0(A_160))
      | ~ m1_subset_1(B_161,u1_struct_0(A_160))
      | ~ l1_orders_2(A_160)
      | ~ v2_lattice3(A_160)
      | ~ v5_orders_2(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_373,plain,(
    ! [A_69,B_161,C_162] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_69),B_161,C_162),A_69)
      | ~ m1_subset_1(C_162,u1_struct_0(k2_yellow_1(A_69)))
      | ~ m1_subset_1(B_161,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v2_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_370])).

tff(c_375,plain,(
    ! [A_69,B_161,C_162] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_69),B_161,C_162),A_69)
      | ~ m1_subset_1(C_162,A_69)
      | ~ m1_subset_1(B_161,A_69)
      | ~ v2_lattice3(k2_yellow_1(A_69)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_373])).

tff(c_519,plain,(
    ! [B_195,C_196] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_195,C_196),'#skF_2')
      | ~ m1_subset_1(C_196,'#skF_2')
      | ~ m1_subset_1(B_195,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_196,'#skF_2')
      | ~ m1_subset_1(B_195,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_375])).

tff(c_528,plain,(
    ! [B_195,C_196] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_195,C_196),'#skF_2')
      | ~ m1_subset_1(C_196,'#skF_2')
      | ~ m1_subset_1(B_195,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_519])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_512,plain,(
    ! [B_193,C_194] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_193,C_194) = k11_lattice3(k2_yellow_1('#skF_2'),B_193,C_194)
      | ~ m1_subset_1(C_194,'#skF_2')
      | ~ m1_subset_1(B_193,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_509])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k12_lattice3(A_7,B_8,C_9),u1_struct_0(A_7))
      | ~ m1_subset_1(C_9,u1_struct_0(A_7))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7)
      | ~ v2_lattice3(A_7)
      | ~ v5_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_539,plain,(
    ! [A_199,B_200,C_201] :
      ( r1_orders_2(A_199,k12_lattice3(A_199,B_200,C_201),C_201)
      | ~ m1_subset_1(k12_lattice3(A_199,B_200,C_201),u1_struct_0(A_199))
      | ~ m1_subset_1(C_201,u1_struct_0(A_199))
      | ~ m1_subset_1(B_200,u1_struct_0(A_199))
      | ~ l1_orders_2(A_199)
      | ~ v2_lattice3(A_199)
      | ~ v5_orders_2(A_199) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_563,plain,(
    ! [A_205,B_206,C_207] :
      ( r1_orders_2(A_205,k12_lattice3(A_205,B_206,C_207),C_207)
      | ~ m1_subset_1(C_207,u1_struct_0(A_205))
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205)
      | ~ v2_lattice3(A_205)
      | ~ v5_orders_2(A_205) ) ),
    inference(resolution,[status(thm)],[c_8,c_539])).

tff(c_570,plain,(
    ! [B_193,C_194] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_193,C_194),C_194)
      | ~ m1_subset_1(C_194,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_193,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_194,'#skF_2')
      | ~ m1_subset_1(B_193,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_563])).

tff(c_576,plain,(
    ! [B_208,C_209] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_208,C_209),C_209)
      | ~ m1_subset_1(C_209,'#skF_2')
      | ~ m1_subset_1(B_208,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_570])).

tff(c_34,plain,(
    ! [A_67] : v3_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_470,plain,(
    ! [A_180,B_181,C_182] :
      ( r3_orders_2(A_180,B_181,C_182)
      | ~ r1_orders_2(A_180,B_181,C_182)
      | ~ m1_subset_1(C_182,u1_struct_0(A_180))
      | ~ m1_subset_1(B_181,u1_struct_0(A_180))
      | ~ l1_orders_2(A_180)
      | ~ v3_orders_2(A_180)
      | v2_struct_0(A_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_477,plain,(
    ! [A_69,B_181,C_182] :
      ( r3_orders_2(k2_yellow_1(A_69),B_181,C_182)
      | ~ r1_orders_2(k2_yellow_1(A_69),B_181,C_182)
      | ~ m1_subset_1(C_182,A_69)
      | ~ m1_subset_1(B_181,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v3_orders_2(k2_yellow_1(A_69))
      | v2_struct_0(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_470])).

tff(c_482,plain,(
    ! [A_183,B_184,C_185] :
      ( r3_orders_2(k2_yellow_1(A_183),B_184,C_185)
      | ~ r1_orders_2(k2_yellow_1(A_183),B_184,C_185)
      | ~ m1_subset_1(C_185,A_183)
      | ~ m1_subset_1(B_184,A_183)
      | v2_struct_0(k2_yellow_1(A_183)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_477])).

tff(c_50,plain,(
    ! [B_74,C_76,A_70] :
      ( r1_tarski(B_74,C_76)
      | ~ r3_orders_2(k2_yellow_1(A_70),B_74,C_76)
      | ~ m1_subset_1(C_76,u1_struct_0(k2_yellow_1(A_70)))
      | ~ m1_subset_1(B_74,u1_struct_0(k2_yellow_1(A_70)))
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_63,plain,(
    ! [B_74,C_76,A_70] :
      ( r1_tarski(B_74,C_76)
      | ~ r3_orders_2(k2_yellow_1(A_70),B_74,C_76)
      | ~ m1_subset_1(C_76,A_70)
      | ~ m1_subset_1(B_74,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_50])).

tff(c_491,plain,(
    ! [B_184,C_185,A_183] :
      ( r1_tarski(B_184,C_185)
      | v1_xboole_0(A_183)
      | ~ r1_orders_2(k2_yellow_1(A_183),B_184,C_185)
      | ~ m1_subset_1(C_185,A_183)
      | ~ m1_subset_1(B_184,A_183)
      | v2_struct_0(k2_yellow_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_482,c_63])).

tff(c_579,plain,(
    ! [B_208,C_209] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_208,C_209),C_209)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_208,C_209),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_209,'#skF_2')
      | ~ m1_subset_1(B_208,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_576,c_491])).

tff(c_588,plain,(
    ! [B_208,C_209] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_208,C_209),C_209)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_208,C_209),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_209,'#skF_2')
      | ~ m1_subset_1(B_208,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_579])).

tff(c_602,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_588])).

tff(c_42,plain,(
    ! [A_68] :
      ( ~ v2_struct_0(k2_yellow_1(A_68))
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_605,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_602,c_42])).

tff(c_609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_605])).

tff(c_625,plain,(
    ! [B_215,C_216] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_215,C_216),C_216)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_215,C_216),'#skF_2')
      | ~ m1_subset_1(C_216,'#skF_2')
      | ~ m1_subset_1(B_215,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_588])).

tff(c_186,plain,(
    ! [A_118,B_119,C_120] :
      ( k12_lattice3(A_118,B_119,C_120) = k11_lattice3(A_118,B_119,C_120)
      | ~ m1_subset_1(C_120,u1_struct_0(A_118))
      | ~ m1_subset_1(B_119,u1_struct_0(A_118))
      | ~ l1_orders_2(A_118)
      | ~ v2_lattice3(A_118)
      | ~ v5_orders_2(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_193,plain,(
    ! [A_69,B_119,C_120] :
      ( k12_lattice3(k2_yellow_1(A_69),B_119,C_120) = k11_lattice3(k2_yellow_1(A_69),B_119,C_120)
      | ~ m1_subset_1(C_120,A_69)
      | ~ m1_subset_1(B_119,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v2_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_186])).

tff(c_202,plain,(
    ! [A_121,B_122,C_123] :
      ( k12_lattice3(k2_yellow_1(A_121),B_122,C_123) = k11_lattice3(k2_yellow_1(A_121),B_122,C_123)
      | ~ m1_subset_1(C_123,A_121)
      | ~ m1_subset_1(B_122,A_121)
      | ~ v2_lattice3(k2_yellow_1(A_121)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_193])).

tff(c_206,plain,(
    ! [B_124,C_125] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_124,C_125) = k11_lattice3(k2_yellow_1('#skF_2'),B_124,C_125)
      | ~ m1_subset_1(C_125,'#skF_2')
      | ~ m1_subset_1(B_124,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_202])).

tff(c_103,plain,(
    ! [A_98,B_99,C_100] :
      ( m1_subset_1(k12_lattice3(A_98,B_99,C_100),u1_struct_0(A_98))
      | ~ m1_subset_1(C_100,u1_struct_0(A_98))
      | ~ m1_subset_1(B_99,u1_struct_0(A_98))
      | ~ l1_orders_2(A_98)
      | ~ v2_lattice3(A_98)
      | ~ v5_orders_2(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_106,plain,(
    ! [A_69,B_99,C_100] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_69),B_99,C_100),A_69)
      | ~ m1_subset_1(C_100,u1_struct_0(k2_yellow_1(A_69)))
      | ~ m1_subset_1(B_99,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v2_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_108,plain,(
    ! [A_69,B_99,C_100] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_69),B_99,C_100),A_69)
      | ~ m1_subset_1(C_100,A_69)
      | ~ m1_subset_1(B_99,A_69)
      | ~ v2_lattice3(k2_yellow_1(A_69)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_106])).

tff(c_212,plain,(
    ! [B_124,C_125] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_124,C_125),'#skF_2')
      | ~ m1_subset_1(C_125,'#skF_2')
      | ~ m1_subset_1(B_124,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_125,'#skF_2')
      | ~ m1_subset_1(B_124,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_108])).

tff(c_221,plain,(
    ! [B_124,C_125] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_124,C_125),'#skF_2')
      | ~ m1_subset_1(C_125,'#skF_2')
      | ~ m1_subset_1(B_124,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_212])).

tff(c_205,plain,(
    ! [B_122,C_123] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_122,C_123) = k11_lattice3(k2_yellow_1('#skF_2'),B_122,C_123)
      | ~ m1_subset_1(C_123,'#skF_2')
      | ~ m1_subset_1(B_122,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_202])).

tff(c_244,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_orders_2(A_131,k12_lattice3(A_131,B_132,C_133),C_133)
      | ~ m1_subset_1(k12_lattice3(A_131,B_132,C_133),u1_struct_0(A_131))
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131)
      | ~ v2_lattice3(A_131)
      | ~ v5_orders_2(A_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_271,plain,(
    ! [A_140,B_141,C_142] :
      ( r1_orders_2(A_140,k12_lattice3(A_140,B_141,C_142),C_142)
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v2_lattice3(A_140)
      | ~ v5_orders_2(A_140) ) ),
    inference(resolution,[status(thm)],[c_8,c_244])).

tff(c_278,plain,(
    ! [B_122,C_123] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_122,C_123),C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_122,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_123,'#skF_2')
      | ~ m1_subset_1(B_122,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_271])).

tff(c_284,plain,(
    ! [B_143,C_144] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_143,C_144),C_144)
      | ~ m1_subset_1(C_144,'#skF_2')
      | ~ m1_subset_1(B_143,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_278])).

tff(c_232,plain,(
    ! [A_128,B_129,C_130] :
      ( r3_orders_2(A_128,B_129,C_130)
      | ~ r1_orders_2(A_128,B_129,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v3_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_239,plain,(
    ! [A_69,B_129,C_130] :
      ( r3_orders_2(k2_yellow_1(A_69),B_129,C_130)
      | ~ r1_orders_2(k2_yellow_1(A_69),B_129,C_130)
      | ~ m1_subset_1(C_130,A_69)
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v3_orders_2(k2_yellow_1(A_69))
      | v2_struct_0(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_232])).

tff(c_256,plain,(
    ! [A_134,B_135,C_136] :
      ( r3_orders_2(k2_yellow_1(A_134),B_135,C_136)
      | ~ r1_orders_2(k2_yellow_1(A_134),B_135,C_136)
      | ~ m1_subset_1(C_136,A_134)
      | ~ m1_subset_1(B_135,A_134)
      | v2_struct_0(k2_yellow_1(A_134)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_239])).

tff(c_265,plain,(
    ! [B_135,C_136,A_134] :
      ( r1_tarski(B_135,C_136)
      | v1_xboole_0(A_134)
      | ~ r1_orders_2(k2_yellow_1(A_134),B_135,C_136)
      | ~ m1_subset_1(C_136,A_134)
      | ~ m1_subset_1(B_135,A_134)
      | v2_struct_0(k2_yellow_1(A_134)) ) ),
    inference(resolution,[status(thm)],[c_256,c_63])).

tff(c_287,plain,(
    ! [B_143,C_144] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_143,C_144),C_144)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_143,C_144),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_144,'#skF_2')
      | ~ m1_subset_1(B_143,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_284,c_265])).

tff(c_296,plain,(
    ! [B_143,C_144] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_143,C_144),C_144)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_143,C_144),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_144,'#skF_2')
      | ~ m1_subset_1(B_143,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_287])).

tff(c_320,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_323,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_320,c_42])).

tff(c_327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_323])).

tff(c_342,plain,(
    ! [B_152,C_153] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_152,C_153),C_153)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_152,C_153),'#skF_2')
      | ~ m1_subset_1(C_153,'#skF_2')
      | ~ m1_subset_1(B_152,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_117,plain,(
    ! [A_110,C_111,B_112] :
      ( k11_lattice3(A_110,C_111,B_112) = k11_lattice3(A_110,B_112,C_111)
      | ~ m1_subset_1(C_111,u1_struct_0(A_110))
      | ~ m1_subset_1(B_112,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110)
      | ~ v2_lattice3(A_110)
      | ~ v5_orders_2(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_124,plain,(
    ! [A_69,C_111,B_112] :
      ( k11_lattice3(k2_yellow_1(A_69),C_111,B_112) = k11_lattice3(k2_yellow_1(A_69),B_112,C_111)
      | ~ m1_subset_1(C_111,A_69)
      | ~ m1_subset_1(B_112,u1_struct_0(k2_yellow_1(A_69)))
      | ~ l1_orders_2(k2_yellow_1(A_69))
      | ~ v2_lattice3(k2_yellow_1(A_69))
      | ~ v5_orders_2(k2_yellow_1(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_117])).

tff(c_129,plain,(
    ! [A_113,C_114,B_115] :
      ( k11_lattice3(k2_yellow_1(A_113),C_114,B_115) = k11_lattice3(k2_yellow_1(A_113),B_115,C_114)
      | ~ m1_subset_1(C_114,A_113)
      | ~ m1_subset_1(B_115,A_113)
      | ~ v2_lattice3(k2_yellow_1(A_113)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_124])).

tff(c_133,plain,(
    ! [C_116,B_117] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_116,B_117) = k11_lattice3(k2_yellow_1('#skF_2'),B_117,C_116)
      | ~ m1_subset_1(C_116,'#skF_2')
      | ~ m1_subset_1(B_117,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_129])).

tff(c_91,plain,(
    ! [A_89,B_90,C_91] :
      ( r1_tarski(A_89,k3_xboole_0(B_90,C_91))
      | ~ r1_tarski(A_89,C_91)
      | ~ r1_tarski(A_89,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_95,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_91,c_52])).

tff(c_96,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_148,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_96])).

tff(c_175,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_148])).

tff(c_345,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_342,c_175])).

tff(c_354,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_61,c_345])).

tff(c_357,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_221,c_354])).

tff(c_361,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_61,c_357])).

tff(c_362,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_628,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_625,c_362])).

tff(c_637,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_628])).

tff(c_640,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_528,c_637])).

tff(c_650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_640])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.46  
% 3.03/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.46  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.03/1.46  
% 3.03/1.46  %Foreground sorts:
% 3.03/1.46  
% 3.03/1.46  
% 3.03/1.46  %Background operators:
% 3.03/1.46  
% 3.03/1.46  
% 3.03/1.46  %Foreground operators:
% 3.03/1.46  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.03/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.03/1.46  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.03/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.03/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.46  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.03/1.46  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.03/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.03/1.46  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.03/1.46  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.03/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.46  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.03/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.03/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.03/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.46  tff('#skF_4', type, '#skF_4': $i).
% 3.03/1.46  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.03/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.03/1.46  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.03/1.46  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.03/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.03/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.03/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.03/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.46  
% 3.17/1.48  tff(f_138, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.17/1.48  tff(f_165, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.17/1.48  tff(f_126, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.17/1.48  tff(f_118, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.17/1.48  tff(f_70, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.17/1.48  tff(f_58, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 3.17/1.48  tff(f_114, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k12_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_0)).
% 3.17/1.48  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.17/1.48  tff(f_151, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.17/1.48  tff(f_134, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.17/1.48  tff(f_84, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_lattice3)).
% 3.17/1.48  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.17/1.48  tff(c_44, plain, (![A_69]: (u1_struct_0(k2_yellow_1(A_69))=A_69)), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.17/1.48  tff(c_56, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.17/1.48  tff(c_61, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 3.17/1.48  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.17/1.48  tff(c_62, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54])).
% 3.17/1.48  tff(c_58, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.17/1.48  tff(c_38, plain, (![A_67]: (v5_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.17/1.48  tff(c_30, plain, (![A_66]: (l1_orders_2(k2_yellow_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.17/1.48  tff(c_497, plain, (![A_189, B_190, C_191]: (k12_lattice3(A_189, B_190, C_191)=k11_lattice3(A_189, B_190, C_191) | ~m1_subset_1(C_191, u1_struct_0(A_189)) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l1_orders_2(A_189) | ~v2_lattice3(A_189) | ~v5_orders_2(A_189))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.48  tff(c_504, plain, (![A_69, B_190, C_191]: (k12_lattice3(k2_yellow_1(A_69), B_190, C_191)=k11_lattice3(k2_yellow_1(A_69), B_190, C_191) | ~m1_subset_1(C_191, A_69) | ~m1_subset_1(B_190, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v2_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_497])).
% 3.17/1.48  tff(c_509, plain, (![A_192, B_193, C_194]: (k12_lattice3(k2_yellow_1(A_192), B_193, C_194)=k11_lattice3(k2_yellow_1(A_192), B_193, C_194) | ~m1_subset_1(C_194, A_192) | ~m1_subset_1(B_193, A_192) | ~v2_lattice3(k2_yellow_1(A_192)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_504])).
% 3.17/1.48  tff(c_513, plain, (![B_195, C_196]: (k12_lattice3(k2_yellow_1('#skF_2'), B_195, C_196)=k11_lattice3(k2_yellow_1('#skF_2'), B_195, C_196) | ~m1_subset_1(C_196, '#skF_2') | ~m1_subset_1(B_195, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_509])).
% 3.17/1.48  tff(c_370, plain, (![A_160, B_161, C_162]: (m1_subset_1(k12_lattice3(A_160, B_161, C_162), u1_struct_0(A_160)) | ~m1_subset_1(C_162, u1_struct_0(A_160)) | ~m1_subset_1(B_161, u1_struct_0(A_160)) | ~l1_orders_2(A_160) | ~v2_lattice3(A_160) | ~v5_orders_2(A_160))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.17/1.48  tff(c_373, plain, (![A_69, B_161, C_162]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_69), B_161, C_162), A_69) | ~m1_subset_1(C_162, u1_struct_0(k2_yellow_1(A_69))) | ~m1_subset_1(B_161, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v2_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_370])).
% 3.17/1.48  tff(c_375, plain, (![A_69, B_161, C_162]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_69), B_161, C_162), A_69) | ~m1_subset_1(C_162, A_69) | ~m1_subset_1(B_161, A_69) | ~v2_lattice3(k2_yellow_1(A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_373])).
% 3.17/1.48  tff(c_519, plain, (![B_195, C_196]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_195, C_196), '#skF_2') | ~m1_subset_1(C_196, '#skF_2') | ~m1_subset_1(B_195, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_196, '#skF_2') | ~m1_subset_1(B_195, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_513, c_375])).
% 3.17/1.48  tff(c_528, plain, (![B_195, C_196]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_195, C_196), '#skF_2') | ~m1_subset_1(C_196, '#skF_2') | ~m1_subset_1(B_195, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_519])).
% 3.17/1.48  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.17/1.48  tff(c_512, plain, (![B_193, C_194]: (k12_lattice3(k2_yellow_1('#skF_2'), B_193, C_194)=k11_lattice3(k2_yellow_1('#skF_2'), B_193, C_194) | ~m1_subset_1(C_194, '#skF_2') | ~m1_subset_1(B_193, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_509])).
% 3.17/1.48  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k12_lattice3(A_7, B_8, C_9), u1_struct_0(A_7)) | ~m1_subset_1(C_9, u1_struct_0(A_7)) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_orders_2(A_7) | ~v2_lattice3(A_7) | ~v5_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.17/1.48  tff(c_539, plain, (![A_199, B_200, C_201]: (r1_orders_2(A_199, k12_lattice3(A_199, B_200, C_201), C_201) | ~m1_subset_1(k12_lattice3(A_199, B_200, C_201), u1_struct_0(A_199)) | ~m1_subset_1(C_201, u1_struct_0(A_199)) | ~m1_subset_1(B_200, u1_struct_0(A_199)) | ~l1_orders_2(A_199) | ~v2_lattice3(A_199) | ~v5_orders_2(A_199))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.48  tff(c_563, plain, (![A_205, B_206, C_207]: (r1_orders_2(A_205, k12_lattice3(A_205, B_206, C_207), C_207) | ~m1_subset_1(C_207, u1_struct_0(A_205)) | ~m1_subset_1(B_206, u1_struct_0(A_205)) | ~l1_orders_2(A_205) | ~v2_lattice3(A_205) | ~v5_orders_2(A_205))), inference(resolution, [status(thm)], [c_8, c_539])).
% 3.17/1.48  tff(c_570, plain, (![B_193, C_194]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_193, C_194), C_194) | ~m1_subset_1(C_194, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_193, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_194, '#skF_2') | ~m1_subset_1(B_193, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_512, c_563])).
% 3.17/1.48  tff(c_576, plain, (![B_208, C_209]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_208, C_209), C_209) | ~m1_subset_1(C_209, '#skF_2') | ~m1_subset_1(B_208, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_570])).
% 3.17/1.48  tff(c_34, plain, (![A_67]: (v3_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.17/1.48  tff(c_470, plain, (![A_180, B_181, C_182]: (r3_orders_2(A_180, B_181, C_182) | ~r1_orders_2(A_180, B_181, C_182) | ~m1_subset_1(C_182, u1_struct_0(A_180)) | ~m1_subset_1(B_181, u1_struct_0(A_180)) | ~l1_orders_2(A_180) | ~v3_orders_2(A_180) | v2_struct_0(A_180))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.17/1.48  tff(c_477, plain, (![A_69, B_181, C_182]: (r3_orders_2(k2_yellow_1(A_69), B_181, C_182) | ~r1_orders_2(k2_yellow_1(A_69), B_181, C_182) | ~m1_subset_1(C_182, A_69) | ~m1_subset_1(B_181, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v3_orders_2(k2_yellow_1(A_69)) | v2_struct_0(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_470])).
% 3.17/1.48  tff(c_482, plain, (![A_183, B_184, C_185]: (r3_orders_2(k2_yellow_1(A_183), B_184, C_185) | ~r1_orders_2(k2_yellow_1(A_183), B_184, C_185) | ~m1_subset_1(C_185, A_183) | ~m1_subset_1(B_184, A_183) | v2_struct_0(k2_yellow_1(A_183)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_477])).
% 3.17/1.48  tff(c_50, plain, (![B_74, C_76, A_70]: (r1_tarski(B_74, C_76) | ~r3_orders_2(k2_yellow_1(A_70), B_74, C_76) | ~m1_subset_1(C_76, u1_struct_0(k2_yellow_1(A_70))) | ~m1_subset_1(B_74, u1_struct_0(k2_yellow_1(A_70))) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_151])).
% 3.17/1.48  tff(c_63, plain, (![B_74, C_76, A_70]: (r1_tarski(B_74, C_76) | ~r3_orders_2(k2_yellow_1(A_70), B_74, C_76) | ~m1_subset_1(C_76, A_70) | ~m1_subset_1(B_74, A_70) | v1_xboole_0(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_50])).
% 3.17/1.48  tff(c_491, plain, (![B_184, C_185, A_183]: (r1_tarski(B_184, C_185) | v1_xboole_0(A_183) | ~r1_orders_2(k2_yellow_1(A_183), B_184, C_185) | ~m1_subset_1(C_185, A_183) | ~m1_subset_1(B_184, A_183) | v2_struct_0(k2_yellow_1(A_183)))), inference(resolution, [status(thm)], [c_482, c_63])).
% 3.17/1.48  tff(c_579, plain, (![B_208, C_209]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_208, C_209), C_209) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_208, C_209), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_209, '#skF_2') | ~m1_subset_1(B_208, '#skF_2'))), inference(resolution, [status(thm)], [c_576, c_491])).
% 3.17/1.48  tff(c_588, plain, (![B_208, C_209]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_208, C_209), C_209) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_208, C_209), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_209, '#skF_2') | ~m1_subset_1(B_208, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_579])).
% 3.17/1.48  tff(c_602, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_588])).
% 3.17/1.48  tff(c_42, plain, (![A_68]: (~v2_struct_0(k2_yellow_1(A_68)) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.17/1.48  tff(c_605, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_602, c_42])).
% 3.17/1.48  tff(c_609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_605])).
% 3.17/1.48  tff(c_625, plain, (![B_215, C_216]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_215, C_216), C_216) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_215, C_216), '#skF_2') | ~m1_subset_1(C_216, '#skF_2') | ~m1_subset_1(B_215, '#skF_2'))), inference(splitRight, [status(thm)], [c_588])).
% 3.17/1.48  tff(c_186, plain, (![A_118, B_119, C_120]: (k12_lattice3(A_118, B_119, C_120)=k11_lattice3(A_118, B_119, C_120) | ~m1_subset_1(C_120, u1_struct_0(A_118)) | ~m1_subset_1(B_119, u1_struct_0(A_118)) | ~l1_orders_2(A_118) | ~v2_lattice3(A_118) | ~v5_orders_2(A_118))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.17/1.48  tff(c_193, plain, (![A_69, B_119, C_120]: (k12_lattice3(k2_yellow_1(A_69), B_119, C_120)=k11_lattice3(k2_yellow_1(A_69), B_119, C_120) | ~m1_subset_1(C_120, A_69) | ~m1_subset_1(B_119, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v2_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_186])).
% 3.17/1.48  tff(c_202, plain, (![A_121, B_122, C_123]: (k12_lattice3(k2_yellow_1(A_121), B_122, C_123)=k11_lattice3(k2_yellow_1(A_121), B_122, C_123) | ~m1_subset_1(C_123, A_121) | ~m1_subset_1(B_122, A_121) | ~v2_lattice3(k2_yellow_1(A_121)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_193])).
% 3.17/1.48  tff(c_206, plain, (![B_124, C_125]: (k12_lattice3(k2_yellow_1('#skF_2'), B_124, C_125)=k11_lattice3(k2_yellow_1('#skF_2'), B_124, C_125) | ~m1_subset_1(C_125, '#skF_2') | ~m1_subset_1(B_124, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_202])).
% 3.17/1.48  tff(c_103, plain, (![A_98, B_99, C_100]: (m1_subset_1(k12_lattice3(A_98, B_99, C_100), u1_struct_0(A_98)) | ~m1_subset_1(C_100, u1_struct_0(A_98)) | ~m1_subset_1(B_99, u1_struct_0(A_98)) | ~l1_orders_2(A_98) | ~v2_lattice3(A_98) | ~v5_orders_2(A_98))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.17/1.48  tff(c_106, plain, (![A_69, B_99, C_100]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_69), B_99, C_100), A_69) | ~m1_subset_1(C_100, u1_struct_0(k2_yellow_1(A_69))) | ~m1_subset_1(B_99, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v2_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_103])).
% 3.17/1.48  tff(c_108, plain, (![A_69, B_99, C_100]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_69), B_99, C_100), A_69) | ~m1_subset_1(C_100, A_69) | ~m1_subset_1(B_99, A_69) | ~v2_lattice3(k2_yellow_1(A_69)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_106])).
% 3.17/1.48  tff(c_212, plain, (![B_124, C_125]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_124, C_125), '#skF_2') | ~m1_subset_1(C_125, '#skF_2') | ~m1_subset_1(B_124, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_125, '#skF_2') | ~m1_subset_1(B_124, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_206, c_108])).
% 3.17/1.48  tff(c_221, plain, (![B_124, C_125]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_124, C_125), '#skF_2') | ~m1_subset_1(C_125, '#skF_2') | ~m1_subset_1(B_124, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_212])).
% 3.17/1.48  tff(c_205, plain, (![B_122, C_123]: (k12_lattice3(k2_yellow_1('#skF_2'), B_122, C_123)=k11_lattice3(k2_yellow_1('#skF_2'), B_122, C_123) | ~m1_subset_1(C_123, '#skF_2') | ~m1_subset_1(B_122, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_202])).
% 3.17/1.48  tff(c_244, plain, (![A_131, B_132, C_133]: (r1_orders_2(A_131, k12_lattice3(A_131, B_132, C_133), C_133) | ~m1_subset_1(k12_lattice3(A_131, B_132, C_133), u1_struct_0(A_131)) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l1_orders_2(A_131) | ~v2_lattice3(A_131) | ~v5_orders_2(A_131))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.17/1.48  tff(c_271, plain, (![A_140, B_141, C_142]: (r1_orders_2(A_140, k12_lattice3(A_140, B_141, C_142), C_142) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v2_lattice3(A_140) | ~v5_orders_2(A_140))), inference(resolution, [status(thm)], [c_8, c_244])).
% 3.17/1.48  tff(c_278, plain, (![B_122, C_123]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_122, C_123), C_123) | ~m1_subset_1(C_123, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_122, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_123, '#skF_2') | ~m1_subset_1(B_122, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_205, c_271])).
% 3.17/1.48  tff(c_284, plain, (![B_143, C_144]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_143, C_144), C_144) | ~m1_subset_1(C_144, '#skF_2') | ~m1_subset_1(B_143, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_278])).
% 3.17/1.48  tff(c_232, plain, (![A_128, B_129, C_130]: (r3_orders_2(A_128, B_129, C_130) | ~r1_orders_2(A_128, B_129, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v3_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.17/1.48  tff(c_239, plain, (![A_69, B_129, C_130]: (r3_orders_2(k2_yellow_1(A_69), B_129, C_130) | ~r1_orders_2(k2_yellow_1(A_69), B_129, C_130) | ~m1_subset_1(C_130, A_69) | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v3_orders_2(k2_yellow_1(A_69)) | v2_struct_0(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_232])).
% 3.17/1.48  tff(c_256, plain, (![A_134, B_135, C_136]: (r3_orders_2(k2_yellow_1(A_134), B_135, C_136) | ~r1_orders_2(k2_yellow_1(A_134), B_135, C_136) | ~m1_subset_1(C_136, A_134) | ~m1_subset_1(B_135, A_134) | v2_struct_0(k2_yellow_1(A_134)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_239])).
% 3.17/1.48  tff(c_265, plain, (![B_135, C_136, A_134]: (r1_tarski(B_135, C_136) | v1_xboole_0(A_134) | ~r1_orders_2(k2_yellow_1(A_134), B_135, C_136) | ~m1_subset_1(C_136, A_134) | ~m1_subset_1(B_135, A_134) | v2_struct_0(k2_yellow_1(A_134)))), inference(resolution, [status(thm)], [c_256, c_63])).
% 3.17/1.48  tff(c_287, plain, (![B_143, C_144]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_143, C_144), C_144) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_143, C_144), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_144, '#skF_2') | ~m1_subset_1(B_143, '#skF_2'))), inference(resolution, [status(thm)], [c_284, c_265])).
% 3.17/1.48  tff(c_296, plain, (![B_143, C_144]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_143, C_144), C_144) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_143, C_144), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_144, '#skF_2') | ~m1_subset_1(B_143, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_287])).
% 3.17/1.48  tff(c_320, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_296])).
% 3.17/1.48  tff(c_323, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_320, c_42])).
% 3.17/1.48  tff(c_327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_323])).
% 3.17/1.48  tff(c_342, plain, (![B_152, C_153]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_152, C_153), C_153) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_152, C_153), '#skF_2') | ~m1_subset_1(C_153, '#skF_2') | ~m1_subset_1(B_152, '#skF_2'))), inference(splitRight, [status(thm)], [c_296])).
% 3.17/1.48  tff(c_117, plain, (![A_110, C_111, B_112]: (k11_lattice3(A_110, C_111, B_112)=k11_lattice3(A_110, B_112, C_111) | ~m1_subset_1(C_111, u1_struct_0(A_110)) | ~m1_subset_1(B_112, u1_struct_0(A_110)) | ~l1_orders_2(A_110) | ~v2_lattice3(A_110) | ~v5_orders_2(A_110))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.17/1.48  tff(c_124, plain, (![A_69, C_111, B_112]: (k11_lattice3(k2_yellow_1(A_69), C_111, B_112)=k11_lattice3(k2_yellow_1(A_69), B_112, C_111) | ~m1_subset_1(C_111, A_69) | ~m1_subset_1(B_112, u1_struct_0(k2_yellow_1(A_69))) | ~l1_orders_2(k2_yellow_1(A_69)) | ~v2_lattice3(k2_yellow_1(A_69)) | ~v5_orders_2(k2_yellow_1(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_117])).
% 3.17/1.48  tff(c_129, plain, (![A_113, C_114, B_115]: (k11_lattice3(k2_yellow_1(A_113), C_114, B_115)=k11_lattice3(k2_yellow_1(A_113), B_115, C_114) | ~m1_subset_1(C_114, A_113) | ~m1_subset_1(B_115, A_113) | ~v2_lattice3(k2_yellow_1(A_113)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_124])).
% 3.17/1.48  tff(c_133, plain, (![C_116, B_117]: (k11_lattice3(k2_yellow_1('#skF_2'), C_116, B_117)=k11_lattice3(k2_yellow_1('#skF_2'), B_117, C_116) | ~m1_subset_1(C_116, '#skF_2') | ~m1_subset_1(B_117, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_129])).
% 3.17/1.48  tff(c_91, plain, (![A_89, B_90, C_91]: (r1_tarski(A_89, k3_xboole_0(B_90, C_91)) | ~r1_tarski(A_89, C_91) | ~r1_tarski(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.48  tff(c_52, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.17/1.48  tff(c_95, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_91, c_52])).
% 3.17/1.48  tff(c_96, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_95])).
% 3.17/1.48  tff(c_148, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_133, c_96])).
% 3.17/1.48  tff(c_175, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_148])).
% 3.17/1.48  tff(c_345, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_342, c_175])).
% 3.17/1.48  tff(c_354, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_61, c_345])).
% 3.17/1.48  tff(c_357, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_221, c_354])).
% 3.17/1.48  tff(c_361, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_61, c_357])).
% 3.17/1.48  tff(c_362, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_95])).
% 3.17/1.48  tff(c_628, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_625, c_362])).
% 3.17/1.48  tff(c_637, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_628])).
% 3.17/1.48  tff(c_640, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_528, c_637])).
% 3.17/1.48  tff(c_650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_640])).
% 3.17/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.48  
% 3.17/1.48  Inference rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Ref     : 0
% 3.17/1.48  #Sup     : 123
% 3.17/1.48  #Fact    : 0
% 3.17/1.48  #Define  : 0
% 3.17/1.48  #Split   : 3
% 3.17/1.48  #Chain   : 0
% 3.17/1.48  #Close   : 0
% 3.17/1.48  
% 3.17/1.48  Ordering : KBO
% 3.17/1.48  
% 3.17/1.48  Simplification rules
% 3.17/1.48  ----------------------
% 3.17/1.48  #Subsume      : 21
% 3.17/1.48  #Demod        : 161
% 3.17/1.48  #Tautology    : 33
% 3.17/1.48  #SimpNegUnit  : 7
% 3.17/1.48  #BackRed      : 0
% 3.17/1.48  
% 3.17/1.48  #Partial instantiations: 0
% 3.17/1.48  #Strategies tried      : 1
% 3.17/1.48  
% 3.17/1.48  Timing (in seconds)
% 3.17/1.48  ----------------------
% 3.17/1.49  Preprocessing        : 0.35
% 3.17/1.49  Parsing              : 0.18
% 3.17/1.49  CNF conversion       : 0.03
% 3.17/1.49  Main loop            : 0.34
% 3.17/1.49  Inferencing          : 0.12
% 3.17/1.49  Reduction            : 0.11
% 3.17/1.49  Demodulation         : 0.08
% 3.17/1.49  BG Simplification    : 0.02
% 3.17/1.49  Subsumption          : 0.06
% 3.17/1.49  Abstraction          : 0.02
% 3.17/1.49  MUC search           : 0.00
% 3.17/1.49  Cooper               : 0.00
% 3.17/1.49  Total                : 0.73
% 3.17/1.49  Index Insertion      : 0.00
% 3.17/1.49  Index Deletion       : 0.00
% 3.17/1.49  Index Matching       : 0.00
% 3.17/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
