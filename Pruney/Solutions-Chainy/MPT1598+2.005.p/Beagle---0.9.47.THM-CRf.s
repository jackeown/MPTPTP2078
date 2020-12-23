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

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 522 expanded)
%              Number of leaves         :   38 ( 214 expanded)
%              Depth                    :   14
%              Number of atoms          :  447 (1600 expanded)
%              Number of equality atoms :   26 ( 256 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k13_lattice3,type,(
    k13_lattice3: ( $i * $i * $i ) > $i )).

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

tff(f_136,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_163,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v1_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k2_xboole_0(B,C),k10_lattice3(k2_yellow_1(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_1)).

tff(f_124,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_116,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k13_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k13_lattice3)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k13_lattice3(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k13_lattice3)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k13_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,B,D)
                      & r1_orders_2(A,C,D)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,B,E)
                              & r1_orders_2(A,C,E) )
                           => r1_orders_2(A,D,E) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow_0)).

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

tff(f_149,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_44,plain,(
    ! [A_65] : u1_struct_0(k2_yellow_1(A_65)) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_61,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_62,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54])).

tff(c_58,plain,(
    v1_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_38,plain,(
    ! [A_63] : v5_orders_2(k2_yellow_1(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_30,plain,(
    ! [A_62] : l1_orders_2(k2_yellow_1(A_62)) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_581,plain,(
    ! [A_190,B_191,C_192] :
      ( k13_lattice3(A_190,B_191,C_192) = k10_lattice3(A_190,B_191,C_192)
      | ~ m1_subset_1(C_192,u1_struct_0(A_190))
      | ~ m1_subset_1(B_191,u1_struct_0(A_190))
      | ~ l1_orders_2(A_190)
      | ~ v1_lattice3(A_190)
      | ~ v5_orders_2(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_588,plain,(
    ! [A_65,B_191,C_192] :
      ( k13_lattice3(k2_yellow_1(A_65),B_191,C_192) = k10_lattice3(k2_yellow_1(A_65),B_191,C_192)
      | ~ m1_subset_1(C_192,A_65)
      | ~ m1_subset_1(B_191,u1_struct_0(k2_yellow_1(A_65)))
      | ~ l1_orders_2(k2_yellow_1(A_65))
      | ~ v1_lattice3(k2_yellow_1(A_65))
      | ~ v5_orders_2(k2_yellow_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_581])).

tff(c_594,plain,(
    ! [A_196,B_197,C_198] :
      ( k13_lattice3(k2_yellow_1(A_196),B_197,C_198) = k10_lattice3(k2_yellow_1(A_196),B_197,C_198)
      | ~ m1_subset_1(C_198,A_196)
      | ~ m1_subset_1(B_197,A_196)
      | ~ v1_lattice3(k2_yellow_1(A_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_588])).

tff(c_598,plain,(
    ! [B_199,C_200] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_199,C_200) = k10_lattice3(k2_yellow_1('#skF_2'),B_199,C_200)
      | ~ m1_subset_1(C_200,'#skF_2')
      | ~ m1_subset_1(B_199,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_594])).

tff(c_568,plain,(
    ! [A_181,B_182,C_183] :
      ( m1_subset_1(k13_lattice3(A_181,B_182,C_183),u1_struct_0(A_181))
      | ~ m1_subset_1(C_183,u1_struct_0(A_181))
      | ~ m1_subset_1(B_182,u1_struct_0(A_181))
      | ~ l1_orders_2(A_181)
      | ~ v1_lattice3(A_181)
      | ~ v5_orders_2(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_571,plain,(
    ! [A_65,B_182,C_183] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_65),B_182,C_183),A_65)
      | ~ m1_subset_1(C_183,u1_struct_0(k2_yellow_1(A_65)))
      | ~ m1_subset_1(B_182,u1_struct_0(k2_yellow_1(A_65)))
      | ~ l1_orders_2(k2_yellow_1(A_65))
      | ~ v1_lattice3(k2_yellow_1(A_65))
      | ~ v5_orders_2(k2_yellow_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_568])).

tff(c_573,plain,(
    ! [A_65,B_182,C_183] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_65),B_182,C_183),A_65)
      | ~ m1_subset_1(C_183,A_65)
      | ~ m1_subset_1(B_182,A_65)
      | ~ v1_lattice3(k2_yellow_1(A_65)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_571])).

tff(c_604,plain,(
    ! [B_199,C_200] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_199,C_200),'#skF_2')
      | ~ m1_subset_1(C_200,'#skF_2')
      | ~ m1_subset_1(B_199,'#skF_2')
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_200,'#skF_2')
      | ~ m1_subset_1(B_199,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_598,c_573])).

tff(c_613,plain,(
    ! [B_199,C_200] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_199,C_200),'#skF_2')
      | ~ m1_subset_1(C_200,'#skF_2')
      | ~ m1_subset_1(B_199,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_604])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_645,plain,(
    ! [A_212,C_213,B_214] :
      ( k13_lattice3(A_212,C_213,B_214) = k13_lattice3(A_212,B_214,C_213)
      | ~ m1_subset_1(C_213,u1_struct_0(A_212))
      | ~ m1_subset_1(B_214,u1_struct_0(A_212))
      | ~ l1_orders_2(A_212)
      | ~ v1_lattice3(A_212)
      | ~ v5_orders_2(A_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_652,plain,(
    ! [A_65,C_213,B_214] :
      ( k13_lattice3(k2_yellow_1(A_65),C_213,B_214) = k13_lattice3(k2_yellow_1(A_65),B_214,C_213)
      | ~ m1_subset_1(C_213,A_65)
      | ~ m1_subset_1(B_214,u1_struct_0(k2_yellow_1(A_65)))
      | ~ l1_orders_2(k2_yellow_1(A_65))
      | ~ v1_lattice3(k2_yellow_1(A_65))
      | ~ v5_orders_2(k2_yellow_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_645])).

tff(c_669,plain,(
    ! [A_218,C_219,B_220] :
      ( k13_lattice3(k2_yellow_1(A_218),C_219,B_220) = k13_lattice3(k2_yellow_1(A_218),B_220,C_219)
      | ~ m1_subset_1(C_219,A_218)
      | ~ m1_subset_1(B_220,A_218)
      | ~ v1_lattice3(k2_yellow_1(A_218)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_652])).

tff(c_672,plain,(
    ! [C_219,B_220] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),C_219,B_220) = k13_lattice3(k2_yellow_1('#skF_2'),B_220,C_219)
      | ~ m1_subset_1(C_219,'#skF_2')
      | ~ m1_subset_1(B_220,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_669])).

tff(c_10,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k13_lattice3(A_10,B_11,C_12),u1_struct_0(A_10))
      | ~ m1_subset_1(C_12,u1_struct_0(A_10))
      | ~ m1_subset_1(B_11,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10)
      | ~ v1_lattice3(A_10)
      | ~ v5_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_657,plain,(
    ! [A_215,C_216,B_217] :
      ( r1_orders_2(A_215,C_216,k13_lattice3(A_215,B_217,C_216))
      | ~ m1_subset_1(k13_lattice3(A_215,B_217,C_216),u1_struct_0(A_215))
      | ~ m1_subset_1(C_216,u1_struct_0(A_215))
      | ~ m1_subset_1(B_217,u1_struct_0(A_215))
      | ~ l1_orders_2(A_215)
      | ~ v1_lattice3(A_215)
      | ~ v5_orders_2(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_800,plain,(
    ! [A_227,C_228,B_229] :
      ( r1_orders_2(A_227,C_228,k13_lattice3(A_227,B_229,C_228))
      | ~ m1_subset_1(C_228,u1_struct_0(A_227))
      | ~ m1_subset_1(B_229,u1_struct_0(A_227))
      | ~ l1_orders_2(A_227)
      | ~ v1_lattice3(A_227)
      | ~ v5_orders_2(A_227) ) ),
    inference(resolution,[status(thm)],[c_10,c_657])).

tff(c_810,plain,(
    ! [C_219,B_220] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_219,k13_lattice3(k2_yellow_1('#skF_2'),C_219,B_220))
      | ~ m1_subset_1(C_219,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_220,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_219,'#skF_2')
      | ~ m1_subset_1(B_220,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_800])).

tff(c_828,plain,(
    ! [C_230,B_231] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_230,k13_lattice3(k2_yellow_1('#skF_2'),C_230,B_231))
      | ~ m1_subset_1(C_230,'#skF_2')
      | ~ m1_subset_1(B_231,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_810])).

tff(c_34,plain,(
    ! [A_63] : v3_orders_2(k2_yellow_1(A_63)) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_618,plain,(
    ! [A_203,B_204,C_205] :
      ( r3_orders_2(A_203,B_204,C_205)
      | ~ r1_orders_2(A_203,B_204,C_205)
      | ~ m1_subset_1(C_205,u1_struct_0(A_203))
      | ~ m1_subset_1(B_204,u1_struct_0(A_203))
      | ~ l1_orders_2(A_203)
      | ~ v3_orders_2(A_203)
      | v2_struct_0(A_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_625,plain,(
    ! [A_65,B_204,C_205] :
      ( r3_orders_2(k2_yellow_1(A_65),B_204,C_205)
      | ~ r1_orders_2(k2_yellow_1(A_65),B_204,C_205)
      | ~ m1_subset_1(C_205,A_65)
      | ~ m1_subset_1(B_204,u1_struct_0(k2_yellow_1(A_65)))
      | ~ l1_orders_2(k2_yellow_1(A_65))
      | ~ v3_orders_2(k2_yellow_1(A_65))
      | v2_struct_0(k2_yellow_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_618])).

tff(c_630,plain,(
    ! [A_206,B_207,C_208] :
      ( r3_orders_2(k2_yellow_1(A_206),B_207,C_208)
      | ~ r1_orders_2(k2_yellow_1(A_206),B_207,C_208)
      | ~ m1_subset_1(C_208,A_206)
      | ~ m1_subset_1(B_207,A_206)
      | v2_struct_0(k2_yellow_1(A_206)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_625])).

tff(c_50,plain,(
    ! [B_70,C_72,A_66] :
      ( r1_tarski(B_70,C_72)
      | ~ r3_orders_2(k2_yellow_1(A_66),B_70,C_72)
      | ~ m1_subset_1(C_72,u1_struct_0(k2_yellow_1(A_66)))
      | ~ m1_subset_1(B_70,u1_struct_0(k2_yellow_1(A_66)))
      | v1_xboole_0(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_63,plain,(
    ! [B_70,C_72,A_66] :
      ( r1_tarski(B_70,C_72)
      | ~ r3_orders_2(k2_yellow_1(A_66),B_70,C_72)
      | ~ m1_subset_1(C_72,A_66)
      | ~ m1_subset_1(B_70,A_66)
      | v1_xboole_0(A_66) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_50])).

tff(c_639,plain,(
    ! [B_207,C_208,A_206] :
      ( r1_tarski(B_207,C_208)
      | v1_xboole_0(A_206)
      | ~ r1_orders_2(k2_yellow_1(A_206),B_207,C_208)
      | ~ m1_subset_1(C_208,A_206)
      | ~ m1_subset_1(B_207,A_206)
      | v2_struct_0(k2_yellow_1(A_206)) ) ),
    inference(resolution,[status(thm)],[c_630,c_63])).

tff(c_831,plain,(
    ! [C_230,B_231] :
      ( r1_tarski(C_230,k13_lattice3(k2_yellow_1('#skF_2'),C_230,B_231))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1('#skF_2'),C_230,B_231),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_230,'#skF_2')
      | ~ m1_subset_1(B_231,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_828,c_639])).

tff(c_846,plain,(
    ! [C_230,B_231] :
      ( r1_tarski(C_230,k13_lattice3(k2_yellow_1('#skF_2'),C_230,B_231))
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1('#skF_2'),C_230,B_231),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_230,'#skF_2')
      | ~ m1_subset_1(B_231,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_831])).

tff(c_885,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_846])).

tff(c_42,plain,(
    ! [A_64] :
      ( ~ v2_struct_0(k2_yellow_1(A_64))
      | v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_888,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_885,c_42])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_888])).

tff(c_894,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_846])).

tff(c_597,plain,(
    ! [B_197,C_198] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_197,C_198) = k10_lattice3(k2_yellow_1('#skF_2'),B_197,C_198)
      | ~ m1_subset_1(C_198,'#skF_2')
      | ~ m1_subset_1(B_197,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_594])).

tff(c_816,plain,(
    ! [C_198,B_197] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_198,k10_lattice3(k2_yellow_1('#skF_2'),B_197,C_198))
      | ~ m1_subset_1(C_198,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_197,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_198,'#skF_2')
      | ~ m1_subset_1(B_197,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_597,c_800])).

tff(c_871,plain,(
    ! [C_235,B_236] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),C_235,k10_lattice3(k2_yellow_1('#skF_2'),B_236,C_235))
      | ~ m1_subset_1(C_235,'#skF_2')
      | ~ m1_subset_1(B_236,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_816])).

tff(c_874,plain,(
    ! [C_235,B_236] :
      ( r1_tarski(C_235,k10_lattice3(k2_yellow_1('#skF_2'),B_236,C_235))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_236,C_235),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_235,'#skF_2')
      | ~ m1_subset_1(B_236,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_871,c_639])).

tff(c_877,plain,(
    ! [C_235,B_236] :
      ( r1_tarski(C_235,k10_lattice3(k2_yellow_1('#skF_2'),B_236,C_235))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_236,C_235),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_235,'#skF_2')
      | ~ m1_subset_1(B_236,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_874])).

tff(c_977,plain,(
    ! [C_252,B_253] :
      ( r1_tarski(C_252,k10_lattice3(k2_yellow_1('#skF_2'),B_253,C_252))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_253,C_252),'#skF_2')
      | ~ m1_subset_1(C_252,'#skF_2')
      | ~ m1_subset_1(B_253,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_894,c_877])).

tff(c_117,plain,(
    ! [A_106,B_107,C_108] :
      ( k13_lattice3(A_106,B_107,C_108) = k10_lattice3(A_106,B_107,C_108)
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v1_lattice3(A_106)
      | ~ v5_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_124,plain,(
    ! [A_65,B_107,C_108] :
      ( k13_lattice3(k2_yellow_1(A_65),B_107,C_108) = k10_lattice3(k2_yellow_1(A_65),B_107,C_108)
      | ~ m1_subset_1(C_108,A_65)
      | ~ m1_subset_1(B_107,u1_struct_0(k2_yellow_1(A_65)))
      | ~ l1_orders_2(k2_yellow_1(A_65))
      | ~ v1_lattice3(k2_yellow_1(A_65))
      | ~ v5_orders_2(k2_yellow_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_117])).

tff(c_129,plain,(
    ! [A_109,B_110,C_111] :
      ( k13_lattice3(k2_yellow_1(A_109),B_110,C_111) = k10_lattice3(k2_yellow_1(A_109),B_110,C_111)
      | ~ m1_subset_1(C_111,A_109)
      | ~ m1_subset_1(B_110,A_109)
      | ~ v1_lattice3(k2_yellow_1(A_109)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_124])).

tff(c_133,plain,(
    ! [B_112,C_113] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_112,C_113) = k10_lattice3(k2_yellow_1('#skF_2'),B_112,C_113)
      | ~ m1_subset_1(C_113,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_129])).

tff(c_103,plain,(
    ! [A_94,B_95,C_96] :
      ( m1_subset_1(k13_lattice3(A_94,B_95,C_96),u1_struct_0(A_94))
      | ~ m1_subset_1(C_96,u1_struct_0(A_94))
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_orders_2(A_94)
      | ~ v1_lattice3(A_94)
      | ~ v5_orders_2(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_106,plain,(
    ! [A_65,B_95,C_96] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_65),B_95,C_96),A_65)
      | ~ m1_subset_1(C_96,u1_struct_0(k2_yellow_1(A_65)))
      | ~ m1_subset_1(B_95,u1_struct_0(k2_yellow_1(A_65)))
      | ~ l1_orders_2(k2_yellow_1(A_65))
      | ~ v1_lattice3(k2_yellow_1(A_65))
      | ~ v5_orders_2(k2_yellow_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_103])).

tff(c_108,plain,(
    ! [A_65,B_95,C_96] :
      ( m1_subset_1(k13_lattice3(k2_yellow_1(A_65),B_95,C_96),A_65)
      | ~ m1_subset_1(C_96,A_65)
      | ~ m1_subset_1(B_95,A_65)
      | ~ v1_lattice3(k2_yellow_1(A_65)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_44,c_106])).

tff(c_139,plain,(
    ! [B_112,C_113] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_112,C_113),'#skF_2')
      | ~ m1_subset_1(C_113,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_2')
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_113,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_108])).

tff(c_148,plain,(
    ! [B_112,C_113] :
      ( m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_112,C_113),'#skF_2')
      | ~ m1_subset_1(C_113,'#skF_2')
      | ~ m1_subset_1(B_112,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_139])).

tff(c_175,plain,(
    ! [A_122,C_123,B_124] :
      ( k13_lattice3(A_122,C_123,B_124) = k13_lattice3(A_122,B_124,C_123)
      | ~ m1_subset_1(C_123,u1_struct_0(A_122))
      | ~ m1_subset_1(B_124,u1_struct_0(A_122))
      | ~ l1_orders_2(A_122)
      | ~ v1_lattice3(A_122)
      | ~ v5_orders_2(A_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_182,plain,(
    ! [A_65,C_123,B_124] :
      ( k13_lattice3(k2_yellow_1(A_65),C_123,B_124) = k13_lattice3(k2_yellow_1(A_65),B_124,C_123)
      | ~ m1_subset_1(C_123,A_65)
      | ~ m1_subset_1(B_124,u1_struct_0(k2_yellow_1(A_65)))
      | ~ l1_orders_2(k2_yellow_1(A_65))
      | ~ v1_lattice3(k2_yellow_1(A_65))
      | ~ v5_orders_2(k2_yellow_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_175])).

tff(c_187,plain,(
    ! [A_125,C_126,B_127] :
      ( k13_lattice3(k2_yellow_1(A_125),C_126,B_127) = k13_lattice3(k2_yellow_1(A_125),B_127,C_126)
      | ~ m1_subset_1(C_126,A_125)
      | ~ m1_subset_1(B_127,A_125)
      | ~ v1_lattice3(k2_yellow_1(A_125)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_182])).

tff(c_190,plain,(
    ! [C_126,B_127] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),C_126,B_127) = k13_lattice3(k2_yellow_1('#skF_2'),B_127,C_126)
      | ~ m1_subset_1(C_126,'#skF_2')
      | ~ m1_subset_1(B_127,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_411,plain,(
    ! [A_151,B_152,C_153] :
      ( r1_orders_2(A_151,B_152,k13_lattice3(A_151,B_152,C_153))
      | ~ m1_subset_1(k13_lattice3(A_151,B_152,C_153),u1_struct_0(A_151))
      | ~ m1_subset_1(C_153,u1_struct_0(A_151))
      | ~ m1_subset_1(B_152,u1_struct_0(A_151))
      | ~ l1_orders_2(A_151)
      | ~ v1_lattice3(A_151)
      | ~ v5_orders_2(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_435,plain,(
    ! [A_154,B_155,C_156] :
      ( r1_orders_2(A_154,B_155,k13_lattice3(A_154,B_155,C_156))
      | ~ m1_subset_1(C_156,u1_struct_0(A_154))
      | ~ m1_subset_1(B_155,u1_struct_0(A_154))
      | ~ l1_orders_2(A_154)
      | ~ v1_lattice3(A_154)
      | ~ v5_orders_2(A_154) ) ),
    inference(resolution,[status(thm)],[c_10,c_411])).

tff(c_445,plain,(
    ! [B_127,C_126] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_127,k13_lattice3(k2_yellow_1('#skF_2'),C_126,B_127))
      | ~ m1_subset_1(C_126,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_127,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_126,'#skF_2')
      | ~ m1_subset_1(B_127,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_435])).

tff(c_463,plain,(
    ! [B_157,C_158] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_157,k13_lattice3(k2_yellow_1('#skF_2'),C_158,B_157))
      | ~ m1_subset_1(C_158,'#skF_2')
      | ~ m1_subset_1(B_157,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_445])).

tff(c_152,plain,(
    ! [A_114,B_115,C_116] :
      ( r3_orders_2(A_114,B_115,C_116)
      | ~ r1_orders_2(A_114,B_115,C_116)
      | ~ m1_subset_1(C_116,u1_struct_0(A_114))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_159,plain,(
    ! [A_65,B_115,C_116] :
      ( r3_orders_2(k2_yellow_1(A_65),B_115,C_116)
      | ~ r1_orders_2(k2_yellow_1(A_65),B_115,C_116)
      | ~ m1_subset_1(C_116,A_65)
      | ~ m1_subset_1(B_115,u1_struct_0(k2_yellow_1(A_65)))
      | ~ l1_orders_2(k2_yellow_1(A_65))
      | ~ v3_orders_2(k2_yellow_1(A_65))
      | v2_struct_0(k2_yellow_1(A_65)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_152])).

tff(c_165,plain,(
    ! [A_119,B_120,C_121] :
      ( r3_orders_2(k2_yellow_1(A_119),B_120,C_121)
      | ~ r1_orders_2(k2_yellow_1(A_119),B_120,C_121)
      | ~ m1_subset_1(C_121,A_119)
      | ~ m1_subset_1(B_120,A_119)
      | v2_struct_0(k2_yellow_1(A_119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_159])).

tff(c_174,plain,(
    ! [B_120,C_121,A_119] :
      ( r1_tarski(B_120,C_121)
      | v1_xboole_0(A_119)
      | ~ r1_orders_2(k2_yellow_1(A_119),B_120,C_121)
      | ~ m1_subset_1(C_121,A_119)
      | ~ m1_subset_1(B_120,A_119)
      | v2_struct_0(k2_yellow_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_165,c_63])).

tff(c_466,plain,(
    ! [B_157,C_158] :
      ( r1_tarski(B_157,k13_lattice3(k2_yellow_1('#skF_2'),C_158,B_157))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1('#skF_2'),C_158,B_157),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_158,'#skF_2')
      | ~ m1_subset_1(B_157,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_463,c_174])).

tff(c_481,plain,(
    ! [B_157,C_158] :
      ( r1_tarski(B_157,k13_lattice3(k2_yellow_1('#skF_2'),C_158,B_157))
      | ~ m1_subset_1(k13_lattice3(k2_yellow_1('#skF_2'),C_158,B_157),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_158,'#skF_2')
      | ~ m1_subset_1(B_157,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_466])).

tff(c_482,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_481])).

tff(c_485,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_482,c_42])).

tff(c_489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_485])).

tff(c_491,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_481])).

tff(c_132,plain,(
    ! [B_110,C_111] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_110,C_111) = k10_lattice3(k2_yellow_1('#skF_2'),B_110,C_111)
      | ~ m1_subset_1(C_111,'#skF_2')
      | ~ m1_subset_1(B_110,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_129])).

tff(c_191,plain,(
    ! [C_128,B_129] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),C_128,B_129) = k13_lattice3(k2_yellow_1('#skF_2'),B_129,C_128)
      | ~ m1_subset_1(C_128,'#skF_2')
      | ~ m1_subset_1(B_129,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_314,plain,(
    ! [C_141,B_142] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),C_141,B_142) = k10_lattice3(k2_yellow_1('#skF_2'),B_142,C_141)
      | ~ m1_subset_1(B_142,'#skF_2')
      | ~ m1_subset_1(C_141,'#skF_2')
      | ~ m1_subset_1(C_141,'#skF_2')
      | ~ m1_subset_1(B_142,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_191])).

tff(c_266,plain,(
    ! [A_132,C_133,B_134] :
      ( r1_orders_2(A_132,C_133,k13_lattice3(A_132,B_134,C_133))
      | ~ m1_subset_1(k13_lattice3(A_132,B_134,C_133),u1_struct_0(A_132))
      | ~ m1_subset_1(C_133,u1_struct_0(A_132))
      | ~ m1_subset_1(B_134,u1_struct_0(A_132))
      | ~ l1_orders_2(A_132)
      | ~ v1_lattice3(A_132)
      | ~ v5_orders_2(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_283,plain,(
    ! [A_10,C_12,B_11] :
      ( r1_orders_2(A_10,C_12,k13_lattice3(A_10,B_11,C_12))
      | ~ m1_subset_1(C_12,u1_struct_0(A_10))
      | ~ m1_subset_1(B_11,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10)
      | ~ v1_lattice3(A_10)
      | ~ v5_orders_2(A_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_266])).

tff(c_320,plain,(
    ! [B_142,C_141] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_142,k10_lattice3(k2_yellow_1('#skF_2'),B_142,C_141))
      | ~ m1_subset_1(B_142,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_141,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_142,'#skF_2')
      | ~ m1_subset_1(C_141,'#skF_2')
      | ~ m1_subset_1(C_141,'#skF_2')
      | ~ m1_subset_1(B_142,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_283])).

tff(c_385,plain,(
    ! [B_147,C_148] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),B_147,k10_lattice3(k2_yellow_1('#skF_2'),B_147,C_148))
      | ~ m1_subset_1(C_148,'#skF_2')
      | ~ m1_subset_1(B_147,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_58,c_30,c_44,c_44,c_320])).

tff(c_388,plain,(
    ! [B_147,C_148] :
      ( r1_tarski(B_147,k10_lattice3(k2_yellow_1('#skF_2'),B_147,C_148))
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_147,C_148),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_148,'#skF_2')
      | ~ m1_subset_1(B_147,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_385,c_174])).

tff(c_391,plain,(
    ! [B_147,C_148] :
      ( r1_tarski(B_147,k10_lattice3(k2_yellow_1('#skF_2'),B_147,C_148))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_147,C_148),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_148,'#skF_2')
      | ~ m1_subset_1(B_147,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_388])).

tff(c_546,plain,(
    ! [B_173,C_174] :
      ( r1_tarski(B_173,k10_lattice3(k2_yellow_1('#skF_2'),B_173,C_174))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),B_173,C_174),'#skF_2')
      | ~ m1_subset_1(C_174,'#skF_2')
      | ~ m1_subset_1(B_173,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_491,c_391])).

tff(c_91,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(k2_xboole_0(A_85,C_86),B_87)
      | ~ r1_tarski(C_86,B_87)
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_4'),k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_95,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_91,c_52])).

tff(c_96,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_95])).

tff(c_549,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_546,c_96])).

tff(c_552,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_549])).

tff(c_555,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_148,c_552])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_555])).

tff(c_560,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_95])).

tff(c_980,plain,
    ( ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_977,c_560])).

tff(c_983,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_980])).

tff(c_986,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_613,c_983])).

tff(c_990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:04:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.62  
% 3.39/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.62  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.73/1.62  
% 3.73/1.62  %Foreground sorts:
% 3.73/1.62  
% 3.73/1.62  
% 3.73/1.62  %Background operators:
% 3.73/1.62  
% 3.73/1.62  
% 3.73/1.62  %Foreground operators:
% 3.73/1.62  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.73/1.62  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.73/1.62  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.73/1.62  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.73/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.73/1.62  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 3.73/1.62  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.73/1.62  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 3.73/1.62  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.73/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.73/1.62  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 3.73/1.62  tff('#skF_2', type, '#skF_2': $i).
% 3.73/1.62  tff('#skF_3', type, '#skF_3': $i).
% 3.73/1.62  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.73/1.62  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.73/1.62  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.73/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.73/1.62  tff('#skF_4', type, '#skF_4': $i).
% 3.73/1.62  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.73/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.73/1.62  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.73/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.73/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.73/1.62  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.73/1.62  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.73/1.62  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.73/1.62  
% 3.73/1.64  tff(f_136, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.73/1.64  tff(f_163, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v1_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k2_xboole_0(B, C), k10_lattice3(k2_yellow_1(A), B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_1)).
% 3.73/1.64  tff(f_124, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.73/1.64  tff(f_116, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.73/1.64  tff(f_82, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 3.73/1.64  tff(f_70, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k13_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k13_lattice3)).
% 3.73/1.64  tff(f_58, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k13_lattice3(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k13_lattice3)).
% 3.73/1.64  tff(f_112, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k13_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_yellow_0)).
% 3.73/1.64  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.73/1.64  tff(f_149, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.73/1.64  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.73/1.64  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.73/1.64  tff(c_44, plain, (![A_65]: (u1_struct_0(k2_yellow_1(A_65))=A_65)), inference(cnfTransformation, [status(thm)], [f_136])).
% 3.73/1.64  tff(c_56, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.73/1.64  tff(c_61, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 3.73/1.64  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.73/1.64  tff(c_62, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54])).
% 3.73/1.64  tff(c_58, plain, (v1_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.73/1.64  tff(c_38, plain, (![A_63]: (v5_orders_2(k2_yellow_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.73/1.64  tff(c_30, plain, (![A_62]: (l1_orders_2(k2_yellow_1(A_62)))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.73/1.64  tff(c_581, plain, (![A_190, B_191, C_192]: (k13_lattice3(A_190, B_191, C_192)=k10_lattice3(A_190, B_191, C_192) | ~m1_subset_1(C_192, u1_struct_0(A_190)) | ~m1_subset_1(B_191, u1_struct_0(A_190)) | ~l1_orders_2(A_190) | ~v1_lattice3(A_190) | ~v5_orders_2(A_190))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.73/1.64  tff(c_588, plain, (![A_65, B_191, C_192]: (k13_lattice3(k2_yellow_1(A_65), B_191, C_192)=k10_lattice3(k2_yellow_1(A_65), B_191, C_192) | ~m1_subset_1(C_192, A_65) | ~m1_subset_1(B_191, u1_struct_0(k2_yellow_1(A_65))) | ~l1_orders_2(k2_yellow_1(A_65)) | ~v1_lattice3(k2_yellow_1(A_65)) | ~v5_orders_2(k2_yellow_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_581])).
% 3.73/1.64  tff(c_594, plain, (![A_196, B_197, C_198]: (k13_lattice3(k2_yellow_1(A_196), B_197, C_198)=k10_lattice3(k2_yellow_1(A_196), B_197, C_198) | ~m1_subset_1(C_198, A_196) | ~m1_subset_1(B_197, A_196) | ~v1_lattice3(k2_yellow_1(A_196)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_588])).
% 3.73/1.64  tff(c_598, plain, (![B_199, C_200]: (k13_lattice3(k2_yellow_1('#skF_2'), B_199, C_200)=k10_lattice3(k2_yellow_1('#skF_2'), B_199, C_200) | ~m1_subset_1(C_200, '#skF_2') | ~m1_subset_1(B_199, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_594])).
% 3.73/1.64  tff(c_568, plain, (![A_181, B_182, C_183]: (m1_subset_1(k13_lattice3(A_181, B_182, C_183), u1_struct_0(A_181)) | ~m1_subset_1(C_183, u1_struct_0(A_181)) | ~m1_subset_1(B_182, u1_struct_0(A_181)) | ~l1_orders_2(A_181) | ~v1_lattice3(A_181) | ~v5_orders_2(A_181))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.73/1.64  tff(c_571, plain, (![A_65, B_182, C_183]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_65), B_182, C_183), A_65) | ~m1_subset_1(C_183, u1_struct_0(k2_yellow_1(A_65))) | ~m1_subset_1(B_182, u1_struct_0(k2_yellow_1(A_65))) | ~l1_orders_2(k2_yellow_1(A_65)) | ~v1_lattice3(k2_yellow_1(A_65)) | ~v5_orders_2(k2_yellow_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_568])).
% 3.73/1.64  tff(c_573, plain, (![A_65, B_182, C_183]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_65), B_182, C_183), A_65) | ~m1_subset_1(C_183, A_65) | ~m1_subset_1(B_182, A_65) | ~v1_lattice3(k2_yellow_1(A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_571])).
% 3.73/1.64  tff(c_604, plain, (![B_199, C_200]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_199, C_200), '#skF_2') | ~m1_subset_1(C_200, '#skF_2') | ~m1_subset_1(B_199, '#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_200, '#skF_2') | ~m1_subset_1(B_199, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_598, c_573])).
% 3.73/1.64  tff(c_613, plain, (![B_199, C_200]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_199, C_200), '#skF_2') | ~m1_subset_1(C_200, '#skF_2') | ~m1_subset_1(B_199, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_604])).
% 3.73/1.64  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.73/1.64  tff(c_645, plain, (![A_212, C_213, B_214]: (k13_lattice3(A_212, C_213, B_214)=k13_lattice3(A_212, B_214, C_213) | ~m1_subset_1(C_213, u1_struct_0(A_212)) | ~m1_subset_1(B_214, u1_struct_0(A_212)) | ~l1_orders_2(A_212) | ~v1_lattice3(A_212) | ~v5_orders_2(A_212))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.73/1.64  tff(c_652, plain, (![A_65, C_213, B_214]: (k13_lattice3(k2_yellow_1(A_65), C_213, B_214)=k13_lattice3(k2_yellow_1(A_65), B_214, C_213) | ~m1_subset_1(C_213, A_65) | ~m1_subset_1(B_214, u1_struct_0(k2_yellow_1(A_65))) | ~l1_orders_2(k2_yellow_1(A_65)) | ~v1_lattice3(k2_yellow_1(A_65)) | ~v5_orders_2(k2_yellow_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_645])).
% 3.73/1.64  tff(c_669, plain, (![A_218, C_219, B_220]: (k13_lattice3(k2_yellow_1(A_218), C_219, B_220)=k13_lattice3(k2_yellow_1(A_218), B_220, C_219) | ~m1_subset_1(C_219, A_218) | ~m1_subset_1(B_220, A_218) | ~v1_lattice3(k2_yellow_1(A_218)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_652])).
% 3.73/1.64  tff(c_672, plain, (![C_219, B_220]: (k13_lattice3(k2_yellow_1('#skF_2'), C_219, B_220)=k13_lattice3(k2_yellow_1('#skF_2'), B_220, C_219) | ~m1_subset_1(C_219, '#skF_2') | ~m1_subset_1(B_220, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_669])).
% 3.73/1.64  tff(c_10, plain, (![A_10, B_11, C_12]: (m1_subset_1(k13_lattice3(A_10, B_11, C_12), u1_struct_0(A_10)) | ~m1_subset_1(C_12, u1_struct_0(A_10)) | ~m1_subset_1(B_11, u1_struct_0(A_10)) | ~l1_orders_2(A_10) | ~v1_lattice3(A_10) | ~v5_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.73/1.64  tff(c_657, plain, (![A_215, C_216, B_217]: (r1_orders_2(A_215, C_216, k13_lattice3(A_215, B_217, C_216)) | ~m1_subset_1(k13_lattice3(A_215, B_217, C_216), u1_struct_0(A_215)) | ~m1_subset_1(C_216, u1_struct_0(A_215)) | ~m1_subset_1(B_217, u1_struct_0(A_215)) | ~l1_orders_2(A_215) | ~v1_lattice3(A_215) | ~v5_orders_2(A_215))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.73/1.64  tff(c_800, plain, (![A_227, C_228, B_229]: (r1_orders_2(A_227, C_228, k13_lattice3(A_227, B_229, C_228)) | ~m1_subset_1(C_228, u1_struct_0(A_227)) | ~m1_subset_1(B_229, u1_struct_0(A_227)) | ~l1_orders_2(A_227) | ~v1_lattice3(A_227) | ~v5_orders_2(A_227))), inference(resolution, [status(thm)], [c_10, c_657])).
% 3.73/1.64  tff(c_810, plain, (![C_219, B_220]: (r1_orders_2(k2_yellow_1('#skF_2'), C_219, k13_lattice3(k2_yellow_1('#skF_2'), C_219, B_220)) | ~m1_subset_1(C_219, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_220, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_219, '#skF_2') | ~m1_subset_1(B_220, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_672, c_800])).
% 3.73/1.64  tff(c_828, plain, (![C_230, B_231]: (r1_orders_2(k2_yellow_1('#skF_2'), C_230, k13_lattice3(k2_yellow_1('#skF_2'), C_230, B_231)) | ~m1_subset_1(C_230, '#skF_2') | ~m1_subset_1(B_231, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_810])).
% 3.73/1.64  tff(c_34, plain, (![A_63]: (v3_orders_2(k2_yellow_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.73/1.64  tff(c_618, plain, (![A_203, B_204, C_205]: (r3_orders_2(A_203, B_204, C_205) | ~r1_orders_2(A_203, B_204, C_205) | ~m1_subset_1(C_205, u1_struct_0(A_203)) | ~m1_subset_1(B_204, u1_struct_0(A_203)) | ~l1_orders_2(A_203) | ~v3_orders_2(A_203) | v2_struct_0(A_203))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.73/1.64  tff(c_625, plain, (![A_65, B_204, C_205]: (r3_orders_2(k2_yellow_1(A_65), B_204, C_205) | ~r1_orders_2(k2_yellow_1(A_65), B_204, C_205) | ~m1_subset_1(C_205, A_65) | ~m1_subset_1(B_204, u1_struct_0(k2_yellow_1(A_65))) | ~l1_orders_2(k2_yellow_1(A_65)) | ~v3_orders_2(k2_yellow_1(A_65)) | v2_struct_0(k2_yellow_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_618])).
% 3.73/1.64  tff(c_630, plain, (![A_206, B_207, C_208]: (r3_orders_2(k2_yellow_1(A_206), B_207, C_208) | ~r1_orders_2(k2_yellow_1(A_206), B_207, C_208) | ~m1_subset_1(C_208, A_206) | ~m1_subset_1(B_207, A_206) | v2_struct_0(k2_yellow_1(A_206)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_625])).
% 3.73/1.64  tff(c_50, plain, (![B_70, C_72, A_66]: (r1_tarski(B_70, C_72) | ~r3_orders_2(k2_yellow_1(A_66), B_70, C_72) | ~m1_subset_1(C_72, u1_struct_0(k2_yellow_1(A_66))) | ~m1_subset_1(B_70, u1_struct_0(k2_yellow_1(A_66))) | v1_xboole_0(A_66))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.73/1.64  tff(c_63, plain, (![B_70, C_72, A_66]: (r1_tarski(B_70, C_72) | ~r3_orders_2(k2_yellow_1(A_66), B_70, C_72) | ~m1_subset_1(C_72, A_66) | ~m1_subset_1(B_70, A_66) | v1_xboole_0(A_66))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_50])).
% 3.73/1.64  tff(c_639, plain, (![B_207, C_208, A_206]: (r1_tarski(B_207, C_208) | v1_xboole_0(A_206) | ~r1_orders_2(k2_yellow_1(A_206), B_207, C_208) | ~m1_subset_1(C_208, A_206) | ~m1_subset_1(B_207, A_206) | v2_struct_0(k2_yellow_1(A_206)))), inference(resolution, [status(thm)], [c_630, c_63])).
% 3.73/1.64  tff(c_831, plain, (![C_230, B_231]: (r1_tarski(C_230, k13_lattice3(k2_yellow_1('#skF_2'), C_230, B_231)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k13_lattice3(k2_yellow_1('#skF_2'), C_230, B_231), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_230, '#skF_2') | ~m1_subset_1(B_231, '#skF_2'))), inference(resolution, [status(thm)], [c_828, c_639])).
% 3.73/1.64  tff(c_846, plain, (![C_230, B_231]: (r1_tarski(C_230, k13_lattice3(k2_yellow_1('#skF_2'), C_230, B_231)) | ~m1_subset_1(k13_lattice3(k2_yellow_1('#skF_2'), C_230, B_231), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_230, '#skF_2') | ~m1_subset_1(B_231, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_831])).
% 3.73/1.64  tff(c_885, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_846])).
% 3.73/1.64  tff(c_42, plain, (![A_64]: (~v2_struct_0(k2_yellow_1(A_64)) | v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_132])).
% 3.73/1.64  tff(c_888, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_885, c_42])).
% 3.73/1.64  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_888])).
% 3.73/1.64  tff(c_894, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_846])).
% 3.73/1.64  tff(c_597, plain, (![B_197, C_198]: (k13_lattice3(k2_yellow_1('#skF_2'), B_197, C_198)=k10_lattice3(k2_yellow_1('#skF_2'), B_197, C_198) | ~m1_subset_1(C_198, '#skF_2') | ~m1_subset_1(B_197, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_594])).
% 3.73/1.64  tff(c_816, plain, (![C_198, B_197]: (r1_orders_2(k2_yellow_1('#skF_2'), C_198, k10_lattice3(k2_yellow_1('#skF_2'), B_197, C_198)) | ~m1_subset_1(C_198, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_197, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_198, '#skF_2') | ~m1_subset_1(B_197, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_597, c_800])).
% 3.73/1.64  tff(c_871, plain, (![C_235, B_236]: (r1_orders_2(k2_yellow_1('#skF_2'), C_235, k10_lattice3(k2_yellow_1('#skF_2'), B_236, C_235)) | ~m1_subset_1(C_235, '#skF_2') | ~m1_subset_1(B_236, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_816])).
% 3.73/1.64  tff(c_874, plain, (![C_235, B_236]: (r1_tarski(C_235, k10_lattice3(k2_yellow_1('#skF_2'), B_236, C_235)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_236, C_235), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_235, '#skF_2') | ~m1_subset_1(B_236, '#skF_2'))), inference(resolution, [status(thm)], [c_871, c_639])).
% 3.73/1.64  tff(c_877, plain, (![C_235, B_236]: (r1_tarski(C_235, k10_lattice3(k2_yellow_1('#skF_2'), B_236, C_235)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_236, C_235), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_235, '#skF_2') | ~m1_subset_1(B_236, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_874])).
% 3.73/1.64  tff(c_977, plain, (![C_252, B_253]: (r1_tarski(C_252, k10_lattice3(k2_yellow_1('#skF_2'), B_253, C_252)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_253, C_252), '#skF_2') | ~m1_subset_1(C_252, '#skF_2') | ~m1_subset_1(B_253, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_894, c_877])).
% 3.73/1.64  tff(c_117, plain, (![A_106, B_107, C_108]: (k13_lattice3(A_106, B_107, C_108)=k10_lattice3(A_106, B_107, C_108) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v1_lattice3(A_106) | ~v5_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.73/1.64  tff(c_124, plain, (![A_65, B_107, C_108]: (k13_lattice3(k2_yellow_1(A_65), B_107, C_108)=k10_lattice3(k2_yellow_1(A_65), B_107, C_108) | ~m1_subset_1(C_108, A_65) | ~m1_subset_1(B_107, u1_struct_0(k2_yellow_1(A_65))) | ~l1_orders_2(k2_yellow_1(A_65)) | ~v1_lattice3(k2_yellow_1(A_65)) | ~v5_orders_2(k2_yellow_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_117])).
% 3.73/1.65  tff(c_129, plain, (![A_109, B_110, C_111]: (k13_lattice3(k2_yellow_1(A_109), B_110, C_111)=k10_lattice3(k2_yellow_1(A_109), B_110, C_111) | ~m1_subset_1(C_111, A_109) | ~m1_subset_1(B_110, A_109) | ~v1_lattice3(k2_yellow_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_124])).
% 3.73/1.65  tff(c_133, plain, (![B_112, C_113]: (k13_lattice3(k2_yellow_1('#skF_2'), B_112, C_113)=k10_lattice3(k2_yellow_1('#skF_2'), B_112, C_113) | ~m1_subset_1(C_113, '#skF_2') | ~m1_subset_1(B_112, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_129])).
% 3.73/1.65  tff(c_103, plain, (![A_94, B_95, C_96]: (m1_subset_1(k13_lattice3(A_94, B_95, C_96), u1_struct_0(A_94)) | ~m1_subset_1(C_96, u1_struct_0(A_94)) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l1_orders_2(A_94) | ~v1_lattice3(A_94) | ~v5_orders_2(A_94))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.73/1.65  tff(c_106, plain, (![A_65, B_95, C_96]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_65), B_95, C_96), A_65) | ~m1_subset_1(C_96, u1_struct_0(k2_yellow_1(A_65))) | ~m1_subset_1(B_95, u1_struct_0(k2_yellow_1(A_65))) | ~l1_orders_2(k2_yellow_1(A_65)) | ~v1_lattice3(k2_yellow_1(A_65)) | ~v5_orders_2(k2_yellow_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_103])).
% 3.73/1.65  tff(c_108, plain, (![A_65, B_95, C_96]: (m1_subset_1(k13_lattice3(k2_yellow_1(A_65), B_95, C_96), A_65) | ~m1_subset_1(C_96, A_65) | ~m1_subset_1(B_95, A_65) | ~v1_lattice3(k2_yellow_1(A_65)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_44, c_106])).
% 3.73/1.65  tff(c_139, plain, (![B_112, C_113]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_112, C_113), '#skF_2') | ~m1_subset_1(C_113, '#skF_2') | ~m1_subset_1(B_112, '#skF_2') | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_113, '#skF_2') | ~m1_subset_1(B_112, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_108])).
% 3.73/1.65  tff(c_148, plain, (![B_112, C_113]: (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_112, C_113), '#skF_2') | ~m1_subset_1(C_113, '#skF_2') | ~m1_subset_1(B_112, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_139])).
% 3.73/1.65  tff(c_175, plain, (![A_122, C_123, B_124]: (k13_lattice3(A_122, C_123, B_124)=k13_lattice3(A_122, B_124, C_123) | ~m1_subset_1(C_123, u1_struct_0(A_122)) | ~m1_subset_1(B_124, u1_struct_0(A_122)) | ~l1_orders_2(A_122) | ~v1_lattice3(A_122) | ~v5_orders_2(A_122))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.73/1.65  tff(c_182, plain, (![A_65, C_123, B_124]: (k13_lattice3(k2_yellow_1(A_65), C_123, B_124)=k13_lattice3(k2_yellow_1(A_65), B_124, C_123) | ~m1_subset_1(C_123, A_65) | ~m1_subset_1(B_124, u1_struct_0(k2_yellow_1(A_65))) | ~l1_orders_2(k2_yellow_1(A_65)) | ~v1_lattice3(k2_yellow_1(A_65)) | ~v5_orders_2(k2_yellow_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_175])).
% 3.73/1.65  tff(c_187, plain, (![A_125, C_126, B_127]: (k13_lattice3(k2_yellow_1(A_125), C_126, B_127)=k13_lattice3(k2_yellow_1(A_125), B_127, C_126) | ~m1_subset_1(C_126, A_125) | ~m1_subset_1(B_127, A_125) | ~v1_lattice3(k2_yellow_1(A_125)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_182])).
% 3.73/1.65  tff(c_190, plain, (![C_126, B_127]: (k13_lattice3(k2_yellow_1('#skF_2'), C_126, B_127)=k13_lattice3(k2_yellow_1('#skF_2'), B_127, C_126) | ~m1_subset_1(C_126, '#skF_2') | ~m1_subset_1(B_127, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_187])).
% 3.73/1.65  tff(c_411, plain, (![A_151, B_152, C_153]: (r1_orders_2(A_151, B_152, k13_lattice3(A_151, B_152, C_153)) | ~m1_subset_1(k13_lattice3(A_151, B_152, C_153), u1_struct_0(A_151)) | ~m1_subset_1(C_153, u1_struct_0(A_151)) | ~m1_subset_1(B_152, u1_struct_0(A_151)) | ~l1_orders_2(A_151) | ~v1_lattice3(A_151) | ~v5_orders_2(A_151))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.73/1.65  tff(c_435, plain, (![A_154, B_155, C_156]: (r1_orders_2(A_154, B_155, k13_lattice3(A_154, B_155, C_156)) | ~m1_subset_1(C_156, u1_struct_0(A_154)) | ~m1_subset_1(B_155, u1_struct_0(A_154)) | ~l1_orders_2(A_154) | ~v1_lattice3(A_154) | ~v5_orders_2(A_154))), inference(resolution, [status(thm)], [c_10, c_411])).
% 3.73/1.65  tff(c_445, plain, (![B_127, C_126]: (r1_orders_2(k2_yellow_1('#skF_2'), B_127, k13_lattice3(k2_yellow_1('#skF_2'), C_126, B_127)) | ~m1_subset_1(C_126, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_127, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_126, '#skF_2') | ~m1_subset_1(B_127, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_435])).
% 3.73/1.65  tff(c_463, plain, (![B_157, C_158]: (r1_orders_2(k2_yellow_1('#skF_2'), B_157, k13_lattice3(k2_yellow_1('#skF_2'), C_158, B_157)) | ~m1_subset_1(C_158, '#skF_2') | ~m1_subset_1(B_157, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_445])).
% 3.73/1.65  tff(c_152, plain, (![A_114, B_115, C_116]: (r3_orders_2(A_114, B_115, C_116) | ~r1_orders_2(A_114, B_115, C_116) | ~m1_subset_1(C_116, u1_struct_0(A_114)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.73/1.65  tff(c_159, plain, (![A_65, B_115, C_116]: (r3_orders_2(k2_yellow_1(A_65), B_115, C_116) | ~r1_orders_2(k2_yellow_1(A_65), B_115, C_116) | ~m1_subset_1(C_116, A_65) | ~m1_subset_1(B_115, u1_struct_0(k2_yellow_1(A_65))) | ~l1_orders_2(k2_yellow_1(A_65)) | ~v3_orders_2(k2_yellow_1(A_65)) | v2_struct_0(k2_yellow_1(A_65)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_152])).
% 3.73/1.65  tff(c_165, plain, (![A_119, B_120, C_121]: (r3_orders_2(k2_yellow_1(A_119), B_120, C_121) | ~r1_orders_2(k2_yellow_1(A_119), B_120, C_121) | ~m1_subset_1(C_121, A_119) | ~m1_subset_1(B_120, A_119) | v2_struct_0(k2_yellow_1(A_119)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_159])).
% 3.73/1.65  tff(c_174, plain, (![B_120, C_121, A_119]: (r1_tarski(B_120, C_121) | v1_xboole_0(A_119) | ~r1_orders_2(k2_yellow_1(A_119), B_120, C_121) | ~m1_subset_1(C_121, A_119) | ~m1_subset_1(B_120, A_119) | v2_struct_0(k2_yellow_1(A_119)))), inference(resolution, [status(thm)], [c_165, c_63])).
% 3.73/1.65  tff(c_466, plain, (![B_157, C_158]: (r1_tarski(B_157, k13_lattice3(k2_yellow_1('#skF_2'), C_158, B_157)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k13_lattice3(k2_yellow_1('#skF_2'), C_158, B_157), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_158, '#skF_2') | ~m1_subset_1(B_157, '#skF_2'))), inference(resolution, [status(thm)], [c_463, c_174])).
% 3.73/1.65  tff(c_481, plain, (![B_157, C_158]: (r1_tarski(B_157, k13_lattice3(k2_yellow_1('#skF_2'), C_158, B_157)) | ~m1_subset_1(k13_lattice3(k2_yellow_1('#skF_2'), C_158, B_157), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_158, '#skF_2') | ~m1_subset_1(B_157, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_466])).
% 3.73/1.65  tff(c_482, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_481])).
% 3.73/1.65  tff(c_485, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_482, c_42])).
% 3.73/1.65  tff(c_489, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_485])).
% 3.73/1.65  tff(c_491, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_481])).
% 3.73/1.65  tff(c_132, plain, (![B_110, C_111]: (k13_lattice3(k2_yellow_1('#skF_2'), B_110, C_111)=k10_lattice3(k2_yellow_1('#skF_2'), B_110, C_111) | ~m1_subset_1(C_111, '#skF_2') | ~m1_subset_1(B_110, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_129])).
% 3.73/1.65  tff(c_191, plain, (![C_128, B_129]: (k13_lattice3(k2_yellow_1('#skF_2'), C_128, B_129)=k13_lattice3(k2_yellow_1('#skF_2'), B_129, C_128) | ~m1_subset_1(C_128, '#skF_2') | ~m1_subset_1(B_129, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_187])).
% 3.73/1.65  tff(c_314, plain, (![C_141, B_142]: (k13_lattice3(k2_yellow_1('#skF_2'), C_141, B_142)=k10_lattice3(k2_yellow_1('#skF_2'), B_142, C_141) | ~m1_subset_1(B_142, '#skF_2') | ~m1_subset_1(C_141, '#skF_2') | ~m1_subset_1(C_141, '#skF_2') | ~m1_subset_1(B_142, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_191])).
% 3.73/1.65  tff(c_266, plain, (![A_132, C_133, B_134]: (r1_orders_2(A_132, C_133, k13_lattice3(A_132, B_134, C_133)) | ~m1_subset_1(k13_lattice3(A_132, B_134, C_133), u1_struct_0(A_132)) | ~m1_subset_1(C_133, u1_struct_0(A_132)) | ~m1_subset_1(B_134, u1_struct_0(A_132)) | ~l1_orders_2(A_132) | ~v1_lattice3(A_132) | ~v5_orders_2(A_132))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.73/1.65  tff(c_283, plain, (![A_10, C_12, B_11]: (r1_orders_2(A_10, C_12, k13_lattice3(A_10, B_11, C_12)) | ~m1_subset_1(C_12, u1_struct_0(A_10)) | ~m1_subset_1(B_11, u1_struct_0(A_10)) | ~l1_orders_2(A_10) | ~v1_lattice3(A_10) | ~v5_orders_2(A_10))), inference(resolution, [status(thm)], [c_10, c_266])).
% 3.73/1.65  tff(c_320, plain, (![B_142, C_141]: (r1_orders_2(k2_yellow_1('#skF_2'), B_142, k10_lattice3(k2_yellow_1('#skF_2'), B_142, C_141)) | ~m1_subset_1(B_142, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_141, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(B_142, '#skF_2') | ~m1_subset_1(C_141, '#skF_2') | ~m1_subset_1(C_141, '#skF_2') | ~m1_subset_1(B_142, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_314, c_283])).
% 3.73/1.65  tff(c_385, plain, (![B_147, C_148]: (r1_orders_2(k2_yellow_1('#skF_2'), B_147, k10_lattice3(k2_yellow_1('#skF_2'), B_147, C_148)) | ~m1_subset_1(C_148, '#skF_2') | ~m1_subset_1(B_147, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_58, c_30, c_44, c_44, c_320])).
% 3.73/1.65  tff(c_388, plain, (![B_147, C_148]: (r1_tarski(B_147, k10_lattice3(k2_yellow_1('#skF_2'), B_147, C_148)) | v1_xboole_0('#skF_2') | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_147, C_148), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_148, '#skF_2') | ~m1_subset_1(B_147, '#skF_2'))), inference(resolution, [status(thm)], [c_385, c_174])).
% 3.73/1.65  tff(c_391, plain, (![B_147, C_148]: (r1_tarski(B_147, k10_lattice3(k2_yellow_1('#skF_2'), B_147, C_148)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_147, C_148), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_148, '#skF_2') | ~m1_subset_1(B_147, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_60, c_388])).
% 3.73/1.65  tff(c_546, plain, (![B_173, C_174]: (r1_tarski(B_173, k10_lattice3(k2_yellow_1('#skF_2'), B_173, C_174)) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), B_173, C_174), '#skF_2') | ~m1_subset_1(C_174, '#skF_2') | ~m1_subset_1(B_173, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_491, c_391])).
% 3.73/1.65  tff(c_91, plain, (![A_85, C_86, B_87]: (r1_tarski(k2_xboole_0(A_85, C_86), B_87) | ~r1_tarski(C_86, B_87) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.73/1.65  tff(c_52, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_4'), k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_163])).
% 3.73/1.65  tff(c_95, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_91, c_52])).
% 3.73/1.65  tff(c_96, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_95])).
% 3.73/1.65  tff(c_549, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_546, c_96])).
% 3.73/1.65  tff(c_552, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_549])).
% 3.73/1.65  tff(c_555, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_148, c_552])).
% 3.73/1.65  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_555])).
% 3.73/1.65  tff(c_560, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_95])).
% 3.73/1.65  tff(c_980, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_977, c_560])).
% 3.73/1.65  tff(c_983, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_980])).
% 3.73/1.65  tff(c_986, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_613, c_983])).
% 3.73/1.65  tff(c_990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_986])).
% 3.73/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/1.65  
% 3.73/1.65  Inference rules
% 3.73/1.65  ----------------------
% 3.73/1.65  #Ref     : 0
% 3.73/1.65  #Sup     : 207
% 3.73/1.65  #Fact    : 0
% 3.73/1.65  #Define  : 0
% 3.73/1.65  #Split   : 3
% 3.73/1.65  #Chain   : 0
% 3.73/1.65  #Close   : 0
% 3.73/1.65  
% 3.73/1.65  Ordering : KBO
% 3.73/1.65  
% 3.73/1.65  Simplification rules
% 3.73/1.65  ----------------------
% 3.73/1.65  #Subsume      : 71
% 3.73/1.65  #Demod        : 331
% 3.73/1.65  #Tautology    : 36
% 3.73/1.65  #SimpNegUnit  : 16
% 3.73/1.65  #BackRed      : 0
% 3.73/1.65  
% 3.73/1.65  #Partial instantiations: 0
% 3.73/1.65  #Strategies tried      : 1
% 3.73/1.65  
% 3.73/1.65  Timing (in seconds)
% 3.73/1.65  ----------------------
% 3.73/1.65  Preprocessing        : 0.36
% 3.73/1.65  Parsing              : 0.19
% 3.73/1.65  CNF conversion       : 0.03
% 3.73/1.65  Main loop            : 0.44
% 3.73/1.65  Inferencing          : 0.17
% 3.73/1.65  Reduction            : 0.14
% 3.73/1.65  Demodulation         : 0.10
% 3.73/1.65  BG Simplification    : 0.03
% 3.73/1.65  Subsumption          : 0.07
% 3.73/1.65  Abstraction          : 0.03
% 3.73/1.65  MUC search           : 0.00
% 3.73/1.65  Cooper               : 0.00
% 3.73/1.65  Total                : 0.85
% 3.73/1.65  Index Insertion      : 0.00
% 3.73/1.65  Index Deletion       : 0.00
% 3.73/1.65  Index Matching       : 0.00
% 3.73/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
