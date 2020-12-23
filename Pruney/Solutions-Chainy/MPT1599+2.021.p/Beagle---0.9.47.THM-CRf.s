%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:25 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 450 expanded)
%              Number of leaves         :   38 ( 187 expanded)
%              Depth                    :   14
%              Number of atoms          :  370 (1349 expanded)
%              Number of equality atoms :   15 ( 214 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_126,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_153,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_102,axiom,(
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

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_139,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_44,plain,(
    ! [A_64] : u1_struct_0(k2_yellow_1(A_64)) = A_64 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_61,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_62,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54])).

tff(c_58,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_38,plain,(
    ! [A_62] : v5_orders_2(k2_yellow_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_30,plain,(
    ! [A_61] : l1_orders_2(k2_yellow_1(A_61)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_631,plain,(
    ! [A_171,B_172,C_173] :
      ( k12_lattice3(A_171,B_172,C_173) = k11_lattice3(A_171,B_172,C_173)
      | ~ m1_subset_1(C_173,u1_struct_0(A_171))
      | ~ m1_subset_1(B_172,u1_struct_0(A_171))
      | ~ l1_orders_2(A_171)
      | ~ v2_lattice3(A_171)
      | ~ v5_orders_2(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_638,plain,(
    ! [A_64,B_172,C_173] :
      ( k12_lattice3(k2_yellow_1(A_64),B_172,C_173) = k11_lattice3(k2_yellow_1(A_64),B_172,C_173)
      | ~ m1_subset_1(C_173,A_64)
      | ~ m1_subset_1(B_172,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v2_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_631])).

tff(c_644,plain,(
    ! [A_177,B_178,C_179] :
      ( k12_lattice3(k2_yellow_1(A_177),B_178,C_179) = k11_lattice3(k2_yellow_1(A_177),B_178,C_179)
      | ~ m1_subset_1(C_179,A_177)
      | ~ m1_subset_1(B_178,A_177)
      | ~ v2_lattice3(k2_yellow_1(A_177)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_638])).

tff(c_648,plain,(
    ! [B_180,C_181] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_180,C_181) = k11_lattice3(k2_yellow_1('#skF_2'),B_180,C_181)
      | ~ m1_subset_1(C_181,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_644])).

tff(c_522,plain,(
    ! [A_155,B_156,C_157] :
      ( m1_subset_1(k12_lattice3(A_155,B_156,C_157),u1_struct_0(A_155))
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v2_lattice3(A_155)
      | ~ v5_orders_2(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_525,plain,(
    ! [A_64,B_156,C_157] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_64),B_156,C_157),A_64)
      | ~ m1_subset_1(C_157,u1_struct_0(k2_yellow_1(A_64)))
      | ~ m1_subset_1(B_156,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v2_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_522])).

tff(c_527,plain,(
    ! [A_64,B_156,C_157] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_64),B_156,C_157),A_64)
      | ~ m1_subset_1(C_157,A_64)
      | ~ m1_subset_1(B_156,A_64)
      | ~ v2_lattice3(k2_yellow_1(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_525])).

tff(c_654,plain,(
    ! [B_180,C_181] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_180,C_181),'#skF_2')
      | ~ m1_subset_1(C_181,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_181,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_527])).

tff(c_663,plain,(
    ! [B_180,C_181] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_180,C_181),'#skF_2')
      | ~ m1_subset_1(C_181,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_654])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_647,plain,(
    ! [B_178,C_179] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_178,C_179) = k11_lattice3(k2_yellow_1('#skF_2'),B_178,C_179)
      | ~ m1_subset_1(C_179,'#skF_2')
      | ~ m1_subset_1(B_178,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_644])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k12_lattice3(A_9,B_10,C_11),u1_struct_0(A_9))
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9)
      | ~ v2_lattice3(A_9)
      | ~ v5_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_808,plain,(
    ! [A_205,B_206,C_207] :
      ( r1_orders_2(A_205,k12_lattice3(A_205,B_206,C_207),B_206)
      | ~ m1_subset_1(k12_lattice3(A_205,B_206,C_207),u1_struct_0(A_205))
      | ~ m1_subset_1(C_207,u1_struct_0(A_205))
      | ~ m1_subset_1(B_206,u1_struct_0(A_205))
      | ~ l1_orders_2(A_205)
      | ~ v2_lattice3(A_205)
      | ~ v5_orders_2(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_820,plain,(
    ! [A_208,B_209,C_210] :
      ( r1_orders_2(A_208,k12_lattice3(A_208,B_209,C_210),B_209)
      | ~ m1_subset_1(C_210,u1_struct_0(A_208))
      | ~ m1_subset_1(B_209,u1_struct_0(A_208))
      | ~ l1_orders_2(A_208)
      | ~ v2_lattice3(A_208)
      | ~ v5_orders_2(A_208) ) ),
    inference(resolution,[status(thm)],[c_10,c_808])).

tff(c_827,plain,(
    ! [B_178,C_179] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_178,C_179),B_178)
      | ~ m1_subset_1(C_179,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_178,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_179,'#skF_2')
      | ~ m1_subset_1(B_178,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_820])).

tff(c_833,plain,(
    ! [B_211,C_212] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_211,C_212),B_211)
      | ~ m1_subset_1(C_212,'#skF_2')
      | ~ m1_subset_1(B_211,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_827])).

tff(c_34,plain,(
    ! [A_62] : v3_orders_2(k2_yellow_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_668,plain,(
    ! [A_184,B_185,C_186] :
      ( r3_orders_2(A_184,B_185,C_186)
      | ~ r1_orders_2(A_184,B_185,C_186)
      | ~ m1_subset_1(C_186,u1_struct_0(A_184))
      | ~ m1_subset_1(B_185,u1_struct_0(A_184))
      | ~ l1_orders_2(A_184)
      | ~ v3_orders_2(A_184)
      | v2_struct_0(A_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_675,plain,(
    ! [A_64,B_185,C_186] :
      ( r3_orders_2(k2_yellow_1(A_64),B_185,C_186)
      | ~ r1_orders_2(k2_yellow_1(A_64),B_185,C_186)
      | ~ m1_subset_1(C_186,A_64)
      | ~ m1_subset_1(B_185,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v3_orders_2(k2_yellow_1(A_64))
      | v2_struct_0(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_668])).

tff(c_680,plain,(
    ! [A_187,B_188,C_189] :
      ( r3_orders_2(k2_yellow_1(A_187),B_188,C_189)
      | ~ r1_orders_2(k2_yellow_1(A_187),B_188,C_189)
      | ~ m1_subset_1(C_189,A_187)
      | ~ m1_subset_1(B_188,A_187)
      | v2_struct_0(k2_yellow_1(A_187)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_675])).

tff(c_50,plain,(
    ! [B_69,C_71,A_65] :
      ( r1_tarski(B_69,C_71)
      | ~ r3_orders_2(k2_yellow_1(A_65),B_69,C_71)
      | ~ m1_subset_1(C_71,u1_struct_0(k2_yellow_1(A_65)))
      | ~ m1_subset_1(B_69,u1_struct_0(k2_yellow_1(A_65)))
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_63,plain,(
    ! [B_69,C_71,A_65] :
      ( r1_tarski(B_69,C_71)
      | ~ r3_orders_2(k2_yellow_1(A_65),B_69,C_71)
      | ~ m1_subset_1(C_71,A_65)
      | ~ m1_subset_1(B_69,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_50])).

tff(c_689,plain,(
    ! [B_188,C_189,A_187] :
      ( r1_tarski(B_188,C_189)
      | v1_xboole_0(A_187)
      | ~ r1_orders_2(k2_yellow_1(A_187),B_188,C_189)
      | ~ m1_subset_1(C_189,A_187)
      | ~ m1_subset_1(B_188,A_187)
      | v2_struct_0(k2_yellow_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_680,c_63])).

tff(c_836,plain,(
    ! [B_211,C_212] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_211,C_212),B_211)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_211,C_212),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_212,'#skF_2')
      | ~ m1_subset_1(B_211,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_833,c_689])).

tff(c_839,plain,(
    ! [B_211,C_212] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_211,C_212),B_211)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_211,C_212),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_212,'#skF_2')
      | ~ m1_subset_1(B_211,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_836])).

tff(c_850,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_839])).

tff(c_42,plain,(
    ! [A_63] :
      ( ~ v2_struct_0(k2_yellow_1(A_63))
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_853,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_850,c_42])).

tff(c_857,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_853])).

tff(c_859,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_839])).

tff(c_764,plain,(
    ! [A_195,B_196,C_197] :
      ( r1_orders_2(A_195,k12_lattice3(A_195,B_196,C_197),C_197)
      | ~ m1_subset_1(k12_lattice3(A_195,B_196,C_197),u1_struct_0(A_195))
      | ~ m1_subset_1(C_197,u1_struct_0(A_195))
      | ~ m1_subset_1(B_196,u1_struct_0(A_195))
      | ~ l1_orders_2(A_195)
      | ~ v2_lattice3(A_195)
      | ~ v5_orders_2(A_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_778,plain,(
    ! [A_198,B_199,C_200] :
      ( r1_orders_2(A_198,k12_lattice3(A_198,B_199,C_200),C_200)
      | ~ m1_subset_1(C_200,u1_struct_0(A_198))
      | ~ m1_subset_1(B_199,u1_struct_0(A_198))
      | ~ l1_orders_2(A_198)
      | ~ v2_lattice3(A_198)
      | ~ v5_orders_2(A_198) ) ),
    inference(resolution,[status(thm)],[c_10,c_764])).

tff(c_785,plain,(
    ! [B_178,C_179] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_178,C_179),C_179)
      | ~ m1_subset_1(C_179,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_178,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_179,'#skF_2')
      | ~ m1_subset_1(B_178,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_778])).

tff(c_791,plain,(
    ! [B_201,C_202] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_201,C_202),C_202)
      | ~ m1_subset_1(C_202,'#skF_2')
      | ~ m1_subset_1(B_201,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_785])).

tff(c_794,plain,(
    ! [B_201,C_202] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_201,C_202),C_202)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_201,C_202),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_202,'#skF_2')
      | ~ m1_subset_1(B_201,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_791,c_689])).

tff(c_797,plain,(
    ! [B_201,C_202] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_201,C_202),C_202)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_201,C_202),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_202,'#skF_2')
      | ~ m1_subset_1(B_201,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_794])).

tff(c_925,plain,(
    ! [B_223,C_224] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_223,C_224),C_224)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_223,C_224),'#skF_2')
      | ~ m1_subset_1(C_224,'#skF_2')
      | ~ m1_subset_1(B_223,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_859,c_797])).

tff(c_391,plain,(
    ! [A_128,B_129,C_130] :
      ( k12_lattice3(A_128,B_129,C_130) = k11_lattice3(A_128,B_129,C_130)
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v2_lattice3(A_128)
      | ~ v5_orders_2(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_398,plain,(
    ! [A_64,B_129,C_130] :
      ( k12_lattice3(k2_yellow_1(A_64),B_129,C_130) = k11_lattice3(k2_yellow_1(A_64),B_129,C_130)
      | ~ m1_subset_1(C_130,A_64)
      | ~ m1_subset_1(B_129,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v2_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_391])).

tff(c_403,plain,(
    ! [A_131,B_132,C_133] :
      ( k12_lattice3(k2_yellow_1(A_131),B_132,C_133) = k11_lattice3(k2_yellow_1(A_131),B_132,C_133)
      | ~ m1_subset_1(C_133,A_131)
      | ~ m1_subset_1(B_132,A_131)
      | ~ v2_lattice3(k2_yellow_1(A_131)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_398])).

tff(c_407,plain,(
    ! [B_134,C_135] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_134,C_135) = k11_lattice3(k2_yellow_1('#skF_2'),B_134,C_135)
      | ~ m1_subset_1(C_135,'#skF_2')
      | ~ m1_subset_1(B_134,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_403])).

tff(c_240,plain,(
    ! [A_103,B_104,C_105] :
      ( m1_subset_1(k12_lattice3(A_103,B_104,C_105),u1_struct_0(A_103))
      | ~ m1_subset_1(C_105,u1_struct_0(A_103))
      | ~ m1_subset_1(B_104,u1_struct_0(A_103))
      | ~ l1_orders_2(A_103)
      | ~ v2_lattice3(A_103)
      | ~ v5_orders_2(A_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_243,plain,(
    ! [A_64,B_104,C_105] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_64),B_104,C_105),A_64)
      | ~ m1_subset_1(C_105,u1_struct_0(k2_yellow_1(A_64)))
      | ~ m1_subset_1(B_104,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v2_lattice3(k2_yellow_1(A_64))
      | ~ v5_orders_2(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_240])).

tff(c_245,plain,(
    ! [A_64,B_104,C_105] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_64),B_104,C_105),A_64)
      | ~ m1_subset_1(C_105,A_64)
      | ~ m1_subset_1(B_104,A_64)
      | ~ v2_lattice3(k2_yellow_1(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_243])).

tff(c_413,plain,(
    ! [B_134,C_135] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_134,C_135),'#skF_2')
      | ~ m1_subset_1(C_135,'#skF_2')
      | ~ m1_subset_1(B_134,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_135,'#skF_2')
      | ~ m1_subset_1(B_134,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_245])).

tff(c_422,plain,(
    ! [B_134,C_135] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_134,C_135),'#skF_2')
      | ~ m1_subset_1(C_135,'#skF_2')
      | ~ m1_subset_1(B_134,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_413])).

tff(c_406,plain,(
    ! [B_132,C_133] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_132,C_133) = k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_133)
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_403])).

tff(c_428,plain,(
    ! [A_138,B_139,C_140] :
      ( r1_orders_2(A_138,k12_lattice3(A_138,B_139,C_140),B_139)
      | ~ m1_subset_1(k12_lattice3(A_138,B_139,C_140),u1_struct_0(A_138))
      | ~ m1_subset_1(C_140,u1_struct_0(A_138))
      | ~ m1_subset_1(B_139,u1_struct_0(A_138))
      | ~ l1_orders_2(A_138)
      | ~ v2_lattice3(A_138)
      | ~ v5_orders_2(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_440,plain,(
    ! [A_141,B_142,C_143] :
      ( r1_orders_2(A_141,k12_lattice3(A_141,B_142,C_143),B_142)
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v2_lattice3(A_141)
      | ~ v5_orders_2(A_141) ) ),
    inference(resolution,[status(thm)],[c_10,c_428])).

tff(c_447,plain,(
    ! [B_132,C_133] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_132,C_133),B_132)
      | ~ m1_subset_1(C_133,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_132,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_133,'#skF_2')
      | ~ m1_subset_1(B_132,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_440])).

tff(c_453,plain,(
    ! [B_144,C_145] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),B_144)
      | ~ m1_subset_1(C_145,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_447])).

tff(c_363,plain,(
    ! [A_119,B_120,C_121] :
      ( r3_orders_2(A_119,B_120,C_121)
      | ~ r1_orders_2(A_119,B_120,C_121)
      | ~ m1_subset_1(C_121,u1_struct_0(A_119))
      | ~ m1_subset_1(B_120,u1_struct_0(A_119))
      | ~ l1_orders_2(A_119)
      | ~ v3_orders_2(A_119)
      | v2_struct_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_370,plain,(
    ! [A_64,B_120,C_121] :
      ( r3_orders_2(k2_yellow_1(A_64),B_120,C_121)
      | ~ r1_orders_2(k2_yellow_1(A_64),B_120,C_121)
      | ~ m1_subset_1(C_121,A_64)
      | ~ m1_subset_1(B_120,u1_struct_0(k2_yellow_1(A_64)))
      | ~ l1_orders_2(k2_yellow_1(A_64))
      | ~ v3_orders_2(k2_yellow_1(A_64))
      | v2_struct_0(k2_yellow_1(A_64)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_363])).

tff(c_375,plain,(
    ! [A_122,B_123,C_124] :
      ( r3_orders_2(k2_yellow_1(A_122),B_123,C_124)
      | ~ r1_orders_2(k2_yellow_1(A_122),B_123,C_124)
      | ~ m1_subset_1(C_124,A_122)
      | ~ m1_subset_1(B_123,A_122)
      | v2_struct_0(k2_yellow_1(A_122)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_370])).

tff(c_384,plain,(
    ! [B_123,C_124,A_122] :
      ( r1_tarski(B_123,C_124)
      | v1_xboole_0(A_122)
      | ~ r1_orders_2(k2_yellow_1(A_122),B_123,C_124)
      | ~ m1_subset_1(C_124,A_122)
      | ~ m1_subset_1(B_123,A_122)
      | v2_struct_0(k2_yellow_1(A_122)) ) ),
    inference(resolution,[status(thm)],[c_375,c_63])).

tff(c_456,plain,(
    ! [B_144,C_145] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),B_144)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_145,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_453,c_384])).

tff(c_459,plain,(
    ! [B_144,C_145] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),B_144)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_144,C_145),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_145,'#skF_2')
      | ~ m1_subset_1(B_144,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_456])).

tff(c_470,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_459])).

tff(c_473,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_470,c_42])).

tff(c_477,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_473])).

tff(c_480,plain,(
    ! [B_148,C_149] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_148,C_149),B_148)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_148,C_149),'#skF_2')
      | ~ m1_subset_1(C_149,'#skF_2')
      | ~ m1_subset_1(B_148,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_459])).

tff(c_118,plain,(
    ! [A_88,B_89,C_90] :
      ( r1_tarski(A_88,k3_xboole_0(B_89,C_90))
      | ~ r1_tarski(A_88,C_90)
      | ~ r1_tarski(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_122,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_52])).

tff(c_157,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_483,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_480,c_157])).

tff(c_486,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_483])).

tff(c_489,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_422,c_486])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_489])).

tff(c_494,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_928,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_925,c_494])).

tff(c_931,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_928])).

tff(c_939,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_663,c_931])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_939])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:53:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.64  
% 2.96/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.96/1.65  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.96/1.65  
% 2.96/1.65  %Foreground sorts:
% 2.96/1.65  
% 2.96/1.65  
% 2.96/1.65  %Background operators:
% 2.96/1.65  
% 2.96/1.65  
% 2.96/1.65  %Foreground operators:
% 2.96/1.65  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 2.96/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.96/1.65  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 2.96/1.65  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 2.96/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.65  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 2.96/1.65  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.96/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.65  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 2.96/1.65  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 2.96/1.65  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.65  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.65  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 2.96/1.65  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 2.96/1.65  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 2.96/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.65  tff('#skF_4', type, '#skF_4': $i).
% 2.96/1.65  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 2.96/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.65  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 2.96/1.65  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 2.96/1.65  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.96/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.96/1.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.96/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.65  
% 3.25/1.67  tff(f_126, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.25/1.67  tff(f_153, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.25/1.67  tff(f_114, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.25/1.67  tff(f_106, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.25/1.67  tff(f_72, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.25/1.67  tff(f_60, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 3.25/1.67  tff(f_102, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k12_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_0)).
% 3.25/1.67  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.25/1.67  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.25/1.67  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.25/1.67  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.25/1.67  tff(c_44, plain, (![A_64]: (u1_struct_0(k2_yellow_1(A_64))=A_64)), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.25/1.67  tff(c_56, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.25/1.67  tff(c_61, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 3.25/1.67  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.25/1.67  tff(c_62, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54])).
% 3.25/1.67  tff(c_58, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.25/1.67  tff(c_38, plain, (![A_62]: (v5_orders_2(k2_yellow_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.25/1.67  tff(c_30, plain, (![A_61]: (l1_orders_2(k2_yellow_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.25/1.67  tff(c_631, plain, (![A_171, B_172, C_173]: (k12_lattice3(A_171, B_172, C_173)=k11_lattice3(A_171, B_172, C_173) | ~m1_subset_1(C_173, u1_struct_0(A_171)) | ~m1_subset_1(B_172, u1_struct_0(A_171)) | ~l1_orders_2(A_171) | ~v2_lattice3(A_171) | ~v5_orders_2(A_171))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.25/1.67  tff(c_638, plain, (![A_64, B_172, C_173]: (k12_lattice3(k2_yellow_1(A_64), B_172, C_173)=k11_lattice3(k2_yellow_1(A_64), B_172, C_173) | ~m1_subset_1(C_173, A_64) | ~m1_subset_1(B_172, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v2_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_631])).
% 3.25/1.67  tff(c_644, plain, (![A_177, B_178, C_179]: (k12_lattice3(k2_yellow_1(A_177), B_178, C_179)=k11_lattice3(k2_yellow_1(A_177), B_178, C_179) | ~m1_subset_1(C_179, A_177) | ~m1_subset_1(B_178, A_177) | ~v2_lattice3(k2_yellow_1(A_177)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_638])).
% 3.25/1.67  tff(c_648, plain, (![B_180, C_181]: (k12_lattice3(k2_yellow_1('#skF_2'), B_180, C_181)=k11_lattice3(k2_yellow_1('#skF_2'), B_180, C_181) | ~m1_subset_1(C_181, '#skF_2') | ~m1_subset_1(B_180, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_644])).
% 3.25/1.67  tff(c_522, plain, (![A_155, B_156, C_157]: (m1_subset_1(k12_lattice3(A_155, B_156, C_157), u1_struct_0(A_155)) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v2_lattice3(A_155) | ~v5_orders_2(A_155))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.67  tff(c_525, plain, (![A_64, B_156, C_157]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_64), B_156, C_157), A_64) | ~m1_subset_1(C_157, u1_struct_0(k2_yellow_1(A_64))) | ~m1_subset_1(B_156, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v2_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_522])).
% 3.25/1.67  tff(c_527, plain, (![A_64, B_156, C_157]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_64), B_156, C_157), A_64) | ~m1_subset_1(C_157, A_64) | ~m1_subset_1(B_156, A_64) | ~v2_lattice3(k2_yellow_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_525])).
% 3.25/1.67  tff(c_654, plain, (![B_180, C_181]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_180, C_181), '#skF_2') | ~m1_subset_1(C_181, '#skF_2') | ~m1_subset_1(B_180, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_181, '#skF_2') | ~m1_subset_1(B_180, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_648, c_527])).
% 3.25/1.67  tff(c_663, plain, (![B_180, C_181]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_180, C_181), '#skF_2') | ~m1_subset_1(C_181, '#skF_2') | ~m1_subset_1(B_180, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_654])).
% 3.25/1.67  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.25/1.67  tff(c_647, plain, (![B_178, C_179]: (k12_lattice3(k2_yellow_1('#skF_2'), B_178, C_179)=k11_lattice3(k2_yellow_1('#skF_2'), B_178, C_179) | ~m1_subset_1(C_179, '#skF_2') | ~m1_subset_1(B_178, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_644])).
% 3.25/1.67  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k12_lattice3(A_9, B_10, C_11), u1_struct_0(A_9)) | ~m1_subset_1(C_11, u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_orders_2(A_9) | ~v2_lattice3(A_9) | ~v5_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.67  tff(c_808, plain, (![A_205, B_206, C_207]: (r1_orders_2(A_205, k12_lattice3(A_205, B_206, C_207), B_206) | ~m1_subset_1(k12_lattice3(A_205, B_206, C_207), u1_struct_0(A_205)) | ~m1_subset_1(C_207, u1_struct_0(A_205)) | ~m1_subset_1(B_206, u1_struct_0(A_205)) | ~l1_orders_2(A_205) | ~v2_lattice3(A_205) | ~v5_orders_2(A_205))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.25/1.67  tff(c_820, plain, (![A_208, B_209, C_210]: (r1_orders_2(A_208, k12_lattice3(A_208, B_209, C_210), B_209) | ~m1_subset_1(C_210, u1_struct_0(A_208)) | ~m1_subset_1(B_209, u1_struct_0(A_208)) | ~l1_orders_2(A_208) | ~v2_lattice3(A_208) | ~v5_orders_2(A_208))), inference(resolution, [status(thm)], [c_10, c_808])).
% 3.25/1.67  tff(c_827, plain, (![B_178, C_179]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_178, C_179), B_178) | ~m1_subset_1(C_179, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_178, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_179, '#skF_2') | ~m1_subset_1(B_178, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_647, c_820])).
% 3.25/1.67  tff(c_833, plain, (![B_211, C_212]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_211, C_212), B_211) | ~m1_subset_1(C_212, '#skF_2') | ~m1_subset_1(B_211, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_827])).
% 3.25/1.67  tff(c_34, plain, (![A_62]: (v3_orders_2(k2_yellow_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.25/1.67  tff(c_668, plain, (![A_184, B_185, C_186]: (r3_orders_2(A_184, B_185, C_186) | ~r1_orders_2(A_184, B_185, C_186) | ~m1_subset_1(C_186, u1_struct_0(A_184)) | ~m1_subset_1(B_185, u1_struct_0(A_184)) | ~l1_orders_2(A_184) | ~v3_orders_2(A_184) | v2_struct_0(A_184))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.67  tff(c_675, plain, (![A_64, B_185, C_186]: (r3_orders_2(k2_yellow_1(A_64), B_185, C_186) | ~r1_orders_2(k2_yellow_1(A_64), B_185, C_186) | ~m1_subset_1(C_186, A_64) | ~m1_subset_1(B_185, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v3_orders_2(k2_yellow_1(A_64)) | v2_struct_0(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_668])).
% 3.25/1.67  tff(c_680, plain, (![A_187, B_188, C_189]: (r3_orders_2(k2_yellow_1(A_187), B_188, C_189) | ~r1_orders_2(k2_yellow_1(A_187), B_188, C_189) | ~m1_subset_1(C_189, A_187) | ~m1_subset_1(B_188, A_187) | v2_struct_0(k2_yellow_1(A_187)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_675])).
% 3.25/1.67  tff(c_50, plain, (![B_69, C_71, A_65]: (r1_tarski(B_69, C_71) | ~r3_orders_2(k2_yellow_1(A_65), B_69, C_71) | ~m1_subset_1(C_71, u1_struct_0(k2_yellow_1(A_65))) | ~m1_subset_1(B_69, u1_struct_0(k2_yellow_1(A_65))) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.25/1.67  tff(c_63, plain, (![B_69, C_71, A_65]: (r1_tarski(B_69, C_71) | ~r3_orders_2(k2_yellow_1(A_65), B_69, C_71) | ~m1_subset_1(C_71, A_65) | ~m1_subset_1(B_69, A_65) | v1_xboole_0(A_65))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_50])).
% 3.25/1.67  tff(c_689, plain, (![B_188, C_189, A_187]: (r1_tarski(B_188, C_189) | v1_xboole_0(A_187) | ~r1_orders_2(k2_yellow_1(A_187), B_188, C_189) | ~m1_subset_1(C_189, A_187) | ~m1_subset_1(B_188, A_187) | v2_struct_0(k2_yellow_1(A_187)))), inference(resolution, [status(thm)], [c_680, c_63])).
% 3.25/1.67  tff(c_836, plain, (![B_211, C_212]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_211, C_212), B_211) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_211, C_212), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_212, '#skF_2') | ~m1_subset_1(B_211, '#skF_2'))), inference(resolution, [status(thm)], [c_833, c_689])).
% 3.25/1.67  tff(c_839, plain, (![B_211, C_212]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_211, C_212), B_211) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_211, C_212), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_212, '#skF_2') | ~m1_subset_1(B_211, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_836])).
% 3.25/1.67  tff(c_850, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_839])).
% 3.25/1.67  tff(c_42, plain, (![A_63]: (~v2_struct_0(k2_yellow_1(A_63)) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.25/1.67  tff(c_853, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_850, c_42])).
% 3.25/1.67  tff(c_857, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_853])).
% 3.25/1.67  tff(c_859, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_839])).
% 3.25/1.67  tff(c_764, plain, (![A_195, B_196, C_197]: (r1_orders_2(A_195, k12_lattice3(A_195, B_196, C_197), C_197) | ~m1_subset_1(k12_lattice3(A_195, B_196, C_197), u1_struct_0(A_195)) | ~m1_subset_1(C_197, u1_struct_0(A_195)) | ~m1_subset_1(B_196, u1_struct_0(A_195)) | ~l1_orders_2(A_195) | ~v2_lattice3(A_195) | ~v5_orders_2(A_195))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.25/1.67  tff(c_778, plain, (![A_198, B_199, C_200]: (r1_orders_2(A_198, k12_lattice3(A_198, B_199, C_200), C_200) | ~m1_subset_1(C_200, u1_struct_0(A_198)) | ~m1_subset_1(B_199, u1_struct_0(A_198)) | ~l1_orders_2(A_198) | ~v2_lattice3(A_198) | ~v5_orders_2(A_198))), inference(resolution, [status(thm)], [c_10, c_764])).
% 3.25/1.67  tff(c_785, plain, (![B_178, C_179]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_178, C_179), C_179) | ~m1_subset_1(C_179, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_178, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_179, '#skF_2') | ~m1_subset_1(B_178, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_647, c_778])).
% 3.25/1.67  tff(c_791, plain, (![B_201, C_202]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_201, C_202), C_202) | ~m1_subset_1(C_202, '#skF_2') | ~m1_subset_1(B_201, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_785])).
% 3.25/1.67  tff(c_794, plain, (![B_201, C_202]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_201, C_202), C_202) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_201, C_202), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_202, '#skF_2') | ~m1_subset_1(B_201, '#skF_2'))), inference(resolution, [status(thm)], [c_791, c_689])).
% 3.25/1.67  tff(c_797, plain, (![B_201, C_202]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_201, C_202), C_202) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_201, C_202), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_202, '#skF_2') | ~m1_subset_1(B_201, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_794])).
% 3.25/1.67  tff(c_925, plain, (![B_223, C_224]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_223, C_224), C_224) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_223, C_224), '#skF_2') | ~m1_subset_1(C_224, '#skF_2') | ~m1_subset_1(B_223, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_859, c_797])).
% 3.25/1.67  tff(c_391, plain, (![A_128, B_129, C_130]: (k12_lattice3(A_128, B_129, C_130)=k11_lattice3(A_128, B_129, C_130) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v2_lattice3(A_128) | ~v5_orders_2(A_128))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.25/1.67  tff(c_398, plain, (![A_64, B_129, C_130]: (k12_lattice3(k2_yellow_1(A_64), B_129, C_130)=k11_lattice3(k2_yellow_1(A_64), B_129, C_130) | ~m1_subset_1(C_130, A_64) | ~m1_subset_1(B_129, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v2_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_391])).
% 3.25/1.67  tff(c_403, plain, (![A_131, B_132, C_133]: (k12_lattice3(k2_yellow_1(A_131), B_132, C_133)=k11_lattice3(k2_yellow_1(A_131), B_132, C_133) | ~m1_subset_1(C_133, A_131) | ~m1_subset_1(B_132, A_131) | ~v2_lattice3(k2_yellow_1(A_131)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_398])).
% 3.25/1.67  tff(c_407, plain, (![B_134, C_135]: (k12_lattice3(k2_yellow_1('#skF_2'), B_134, C_135)=k11_lattice3(k2_yellow_1('#skF_2'), B_134, C_135) | ~m1_subset_1(C_135, '#skF_2') | ~m1_subset_1(B_134, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_403])).
% 3.25/1.67  tff(c_240, plain, (![A_103, B_104, C_105]: (m1_subset_1(k12_lattice3(A_103, B_104, C_105), u1_struct_0(A_103)) | ~m1_subset_1(C_105, u1_struct_0(A_103)) | ~m1_subset_1(B_104, u1_struct_0(A_103)) | ~l1_orders_2(A_103) | ~v2_lattice3(A_103) | ~v5_orders_2(A_103))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.25/1.67  tff(c_243, plain, (![A_64, B_104, C_105]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_64), B_104, C_105), A_64) | ~m1_subset_1(C_105, u1_struct_0(k2_yellow_1(A_64))) | ~m1_subset_1(B_104, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v2_lattice3(k2_yellow_1(A_64)) | ~v5_orders_2(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_240])).
% 3.25/1.67  tff(c_245, plain, (![A_64, B_104, C_105]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_64), B_104, C_105), A_64) | ~m1_subset_1(C_105, A_64) | ~m1_subset_1(B_104, A_64) | ~v2_lattice3(k2_yellow_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_243])).
% 3.25/1.67  tff(c_413, plain, (![B_134, C_135]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_134, C_135), '#skF_2') | ~m1_subset_1(C_135, '#skF_2') | ~m1_subset_1(B_134, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_135, '#skF_2') | ~m1_subset_1(B_134, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_407, c_245])).
% 3.25/1.67  tff(c_422, plain, (![B_134, C_135]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_134, C_135), '#skF_2') | ~m1_subset_1(C_135, '#skF_2') | ~m1_subset_1(B_134, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_413])).
% 3.25/1.67  tff(c_406, plain, (![B_132, C_133]: (k12_lattice3(k2_yellow_1('#skF_2'), B_132, C_133)=k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_133) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_403])).
% 3.25/1.67  tff(c_428, plain, (![A_138, B_139, C_140]: (r1_orders_2(A_138, k12_lattice3(A_138, B_139, C_140), B_139) | ~m1_subset_1(k12_lattice3(A_138, B_139, C_140), u1_struct_0(A_138)) | ~m1_subset_1(C_140, u1_struct_0(A_138)) | ~m1_subset_1(B_139, u1_struct_0(A_138)) | ~l1_orders_2(A_138) | ~v2_lattice3(A_138) | ~v5_orders_2(A_138))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.25/1.67  tff(c_440, plain, (![A_141, B_142, C_143]: (r1_orders_2(A_141, k12_lattice3(A_141, B_142, C_143), B_142) | ~m1_subset_1(C_143, u1_struct_0(A_141)) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v2_lattice3(A_141) | ~v5_orders_2(A_141))), inference(resolution, [status(thm)], [c_10, c_428])).
% 3.25/1.67  tff(c_447, plain, (![B_132, C_133]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_132, C_133), B_132) | ~m1_subset_1(C_133, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_132, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_133, '#skF_2') | ~m1_subset_1(B_132, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_406, c_440])).
% 3.25/1.67  tff(c_453, plain, (![B_144, C_145]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), B_144) | ~m1_subset_1(C_145, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_447])).
% 3.25/1.67  tff(c_363, plain, (![A_119, B_120, C_121]: (r3_orders_2(A_119, B_120, C_121) | ~r1_orders_2(A_119, B_120, C_121) | ~m1_subset_1(C_121, u1_struct_0(A_119)) | ~m1_subset_1(B_120, u1_struct_0(A_119)) | ~l1_orders_2(A_119) | ~v3_orders_2(A_119) | v2_struct_0(A_119))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.67  tff(c_370, plain, (![A_64, B_120, C_121]: (r3_orders_2(k2_yellow_1(A_64), B_120, C_121) | ~r1_orders_2(k2_yellow_1(A_64), B_120, C_121) | ~m1_subset_1(C_121, A_64) | ~m1_subset_1(B_120, u1_struct_0(k2_yellow_1(A_64))) | ~l1_orders_2(k2_yellow_1(A_64)) | ~v3_orders_2(k2_yellow_1(A_64)) | v2_struct_0(k2_yellow_1(A_64)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_363])).
% 3.25/1.67  tff(c_375, plain, (![A_122, B_123, C_124]: (r3_orders_2(k2_yellow_1(A_122), B_123, C_124) | ~r1_orders_2(k2_yellow_1(A_122), B_123, C_124) | ~m1_subset_1(C_124, A_122) | ~m1_subset_1(B_123, A_122) | v2_struct_0(k2_yellow_1(A_122)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_370])).
% 3.25/1.67  tff(c_384, plain, (![B_123, C_124, A_122]: (r1_tarski(B_123, C_124) | v1_xboole_0(A_122) | ~r1_orders_2(k2_yellow_1(A_122), B_123, C_124) | ~m1_subset_1(C_124, A_122) | ~m1_subset_1(B_123, A_122) | v2_struct_0(k2_yellow_1(A_122)))), inference(resolution, [status(thm)], [c_375, c_63])).
% 3.25/1.67  tff(c_456, plain, (![B_144, C_145]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), B_144) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_145, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(resolution, [status(thm)], [c_453, c_384])).
% 3.25/1.67  tff(c_459, plain, (![B_144, C_145]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), B_144) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_144, C_145), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_145, '#skF_2') | ~m1_subset_1(B_144, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_456])).
% 3.25/1.67  tff(c_470, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_459])).
% 3.25/1.67  tff(c_473, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_470, c_42])).
% 3.25/1.67  tff(c_477, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_473])).
% 3.25/1.67  tff(c_480, plain, (![B_148, C_149]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_148, C_149), B_148) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_148, C_149), '#skF_2') | ~m1_subset_1(C_149, '#skF_2') | ~m1_subset_1(B_148, '#skF_2'))), inference(splitRight, [status(thm)], [c_459])).
% 3.25/1.67  tff(c_118, plain, (![A_88, B_89, C_90]: (r1_tarski(A_88, k3_xboole_0(B_89, C_90)) | ~r1_tarski(A_88, C_90) | ~r1_tarski(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.67  tff(c_52, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.25/1.67  tff(c_122, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_118, c_52])).
% 3.25/1.67  tff(c_157, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_122])).
% 3.25/1.67  tff(c_483, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_480, c_157])).
% 3.25/1.67  tff(c_486, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_483])).
% 3.25/1.67  tff(c_489, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_422, c_486])).
% 3.25/1.67  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_489])).
% 3.25/1.67  tff(c_494, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_122])).
% 3.25/1.67  tff(c_928, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_925, c_494])).
% 3.25/1.67  tff(c_931, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_928])).
% 3.25/1.67  tff(c_939, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_663, c_931])).
% 3.25/1.67  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_939])).
% 3.25/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.67  
% 3.25/1.67  Inference rules
% 3.25/1.67  ----------------------
% 3.25/1.67  #Ref     : 0
% 3.25/1.67  #Sup     : 197
% 3.25/1.67  #Fact    : 0
% 3.25/1.67  #Define  : 0
% 3.25/1.67  #Split   : 3
% 3.25/1.67  #Chain   : 0
% 3.25/1.67  #Close   : 0
% 3.25/1.67  
% 3.25/1.67  Ordering : KBO
% 3.25/1.67  
% 3.25/1.67  Simplification rules
% 3.25/1.67  ----------------------
% 3.25/1.67  #Subsume      : 9
% 3.25/1.67  #Demod        : 200
% 3.25/1.67  #Tautology    : 98
% 3.25/1.67  #SimpNegUnit  : 10
% 3.25/1.67  #BackRed      : 0
% 3.25/1.67  
% 3.25/1.67  #Partial instantiations: 0
% 3.25/1.67  #Strategies tried      : 1
% 3.25/1.67  
% 3.25/1.67  Timing (in seconds)
% 3.25/1.67  ----------------------
% 3.31/1.67  Preprocessing        : 0.34
% 3.31/1.67  Parsing              : 0.16
% 3.31/1.67  CNF conversion       : 0.03
% 3.31/1.67  Main loop            : 0.40
% 3.31/1.67  Inferencing          : 0.15
% 3.31/1.67  Reduction            : 0.14
% 3.31/1.67  Demodulation         : 0.11
% 3.31/1.67  BG Simplification    : 0.03
% 3.31/1.67  Subsumption          : 0.06
% 3.31/1.67  Abstraction          : 0.03
% 3.31/1.67  MUC search           : 0.00
% 3.31/1.67  Cooper               : 0.00
% 3.31/1.67  Total                : 0.78
% 3.31/1.67  Index Insertion      : 0.00
% 3.31/1.67  Index Deletion       : 0.00
% 3.31/1.67  Index Matching       : 0.00
% 3.31/1.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
