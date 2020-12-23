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
% DateTime   : Thu Dec  3 10:25:26 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 122 expanded)
%              Number of leaves         :   45 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  201 ( 274 expanded)
%              Number of equality atoms :   22 (  51 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_yellow_0,type,(
    k1_yellow_0: ( $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(r1_yellow_0,type,(
    r1_yellow_0: ( $i * $i ) > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_53,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_152,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_131,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_115,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_127,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) )
               => ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) ) )
              & ( ( r2_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r2_lattice3(A,C,D)
                       => r1_orders_2(A,B,D) ) ) )
               => ( B = k1_yellow_0(A,C)
                  & r1_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_144,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_49,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

tff(c_48,plain,(
    ! [A_43] : l1_orders_2(k2_yellow_1(A_43)) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_18,plain,(
    ! [A_13] :
      ( l1_struct_0(A_13)
      | ~ l1_orders_2(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_66,plain,(
    k3_yellow_0(k2_yellow_1('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_108,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(A_64,B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_116,plain,(
    m1_subset_1(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_108])).

tff(c_117,plain,(
    ! [A_66] :
      ( k1_yellow_0(A_66,k1_xboole_0) = k3_yellow_0(A_66)
      | ~ l1_orders_2(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_121,plain,(
    ! [A_43] : k1_yellow_0(k2_yellow_1(A_43),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_43)) ),
    inference(resolution,[status(thm)],[c_48,c_117])).

tff(c_58,plain,(
    ! [A_45] : u1_struct_0(k2_yellow_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_229,plain,(
    ! [A_94,B_95] :
      ( r2_lattice3(A_94,k1_xboole_0,B_95)
      | ~ m1_subset_1(B_95,u1_struct_0(A_94))
      | ~ l1_orders_2(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_244,plain,(
    ! [A_45,B_95] :
      ( r2_lattice3(k2_yellow_1(A_45),k1_xboole_0,B_95)
      | ~ m1_subset_1(B_95,A_45)
      | ~ l1_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_229])).

tff(c_249,plain,(
    ! [A_45,B_95] :
      ( r2_lattice3(k2_yellow_1(A_45),k1_xboole_0,B_95)
      | ~ m1_subset_1(B_95,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_244])).

tff(c_56,plain,(
    ! [A_44] : v5_orders_2(k2_yellow_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_469,plain,(
    ! [A_189,B_190,C_191] :
      ( m1_subset_1('#skF_3'(A_189,B_190,C_191),u1_struct_0(A_189))
      | k1_yellow_0(A_189,C_191) = B_190
      | ~ r2_lattice3(A_189,C_191,B_190)
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | ~ v5_orders_2(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_480,plain,(
    ! [A_45,B_190,C_191] :
      ( m1_subset_1('#skF_3'(k2_yellow_1(A_45),B_190,C_191),A_45)
      | k1_yellow_0(k2_yellow_1(A_45),C_191) = B_190
      | ~ r2_lattice3(k2_yellow_1(A_45),C_191,B_190)
      | ~ m1_subset_1(B_190,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_469])).

tff(c_485,plain,(
    ! [A_45,B_190,C_191] :
      ( m1_subset_1('#skF_3'(k2_yellow_1(A_45),B_190,C_191),A_45)
      | k1_yellow_0(k2_yellow_1(A_45),C_191) = B_190
      | ~ r2_lattice3(k2_yellow_1(A_45),C_191,B_190)
      | ~ m1_subset_1(B_190,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_58,c_480])).

tff(c_127,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69,B_70),A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    ! [A_69,B_70] :
      ( ~ v1_xboole_0(A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_127,c_2])).

tff(c_52,plain,(
    ! [A_44] : v3_orders_2(k2_yellow_1(A_44)) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    ! [A_46,B_50,C_52] :
      ( r3_orders_2(k2_yellow_1(A_46),B_50,C_52)
      | ~ r1_tarski(B_50,C_52)
      | ~ m1_subset_1(C_52,u1_struct_0(k2_yellow_1(A_46)))
      | ~ m1_subset_1(B_50,u1_struct_0(k2_yellow_1(A_46)))
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_356,plain,(
    ! [A_138,B_139,C_140] :
      ( r3_orders_2(k2_yellow_1(A_138),B_139,C_140)
      | ~ r1_tarski(B_139,C_140)
      | ~ m1_subset_1(C_140,A_138)
      | ~ m1_subset_1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_62])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_orders_2(A_14,B_15,C_16)
      | ~ r3_orders_2(A_14,B_15,C_16)
      | ~ m1_subset_1(C_16,u1_struct_0(A_14))
      | ~ m1_subset_1(B_15,u1_struct_0(A_14))
      | ~ l1_orders_2(A_14)
      | ~ v3_orders_2(A_14)
      | v2_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_358,plain,(
    ! [A_138,B_139,C_140] :
      ( r1_orders_2(k2_yellow_1(A_138),B_139,C_140)
      | ~ m1_subset_1(C_140,u1_struct_0(k2_yellow_1(A_138)))
      | ~ m1_subset_1(B_139,u1_struct_0(k2_yellow_1(A_138)))
      | ~ l1_orders_2(k2_yellow_1(A_138))
      | ~ v3_orders_2(k2_yellow_1(A_138))
      | v2_struct_0(k2_yellow_1(A_138))
      | ~ r1_tarski(B_139,C_140)
      | ~ m1_subset_1(C_140,A_138)
      | ~ m1_subset_1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_356,c_22])).

tff(c_364,plain,(
    ! [A_138,B_139,C_140] :
      ( r1_orders_2(k2_yellow_1(A_138),B_139,C_140)
      | v2_struct_0(k2_yellow_1(A_138))
      | ~ r1_tarski(B_139,C_140)
      | ~ m1_subset_1(C_140,A_138)
      | ~ m1_subset_1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_58,c_58,c_358])).

tff(c_461,plain,(
    ! [A_186,B_187,C_188] :
      ( ~ r1_orders_2(A_186,B_187,'#skF_3'(A_186,B_187,C_188))
      | k1_yellow_0(A_186,C_188) = B_187
      | ~ r2_lattice3(A_186,C_188,B_187)
      | ~ m1_subset_1(B_187,u1_struct_0(A_186))
      | ~ l1_orders_2(A_186)
      | ~ v5_orders_2(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_465,plain,(
    ! [A_138,C_188,B_139] :
      ( k1_yellow_0(k2_yellow_1(A_138),C_188) = B_139
      | ~ r2_lattice3(k2_yellow_1(A_138),C_188,B_139)
      | ~ m1_subset_1(B_139,u1_struct_0(k2_yellow_1(A_138)))
      | ~ l1_orders_2(k2_yellow_1(A_138))
      | ~ v5_orders_2(k2_yellow_1(A_138))
      | v2_struct_0(k2_yellow_1(A_138))
      | ~ r1_tarski(B_139,'#skF_3'(k2_yellow_1(A_138),B_139,C_188))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_138),B_139,C_188),A_138)
      | ~ m1_subset_1(B_139,A_138)
      | v1_xboole_0(A_138) ) ),
    inference(resolution,[status(thm)],[c_364,c_461])).

tff(c_841,plain,(
    ! [A_279,C_280,B_281] :
      ( k1_yellow_0(k2_yellow_1(A_279),C_280) = B_281
      | ~ r2_lattice3(k2_yellow_1(A_279),C_280,B_281)
      | v2_struct_0(k2_yellow_1(A_279))
      | ~ r1_tarski(B_281,'#skF_3'(k2_yellow_1(A_279),B_281,C_280))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_279),B_281,C_280),A_279)
      | ~ m1_subset_1(B_281,A_279)
      | v1_xboole_0(A_279) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_48,c_58,c_465])).

tff(c_866,plain,(
    ! [A_296,C_297,A_298] :
      ( k1_yellow_0(k2_yellow_1(A_296),C_297) = A_298
      | ~ r2_lattice3(k2_yellow_1(A_296),C_297,A_298)
      | v2_struct_0(k2_yellow_1(A_296))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_296),A_298,C_297),A_296)
      | ~ m1_subset_1(A_298,A_296)
      | v1_xboole_0(A_296)
      | ~ v1_xboole_0(A_298) ) ),
    inference(resolution,[status(thm)],[c_135,c_841])).

tff(c_876,plain,(
    ! [A_302,B_303,C_304] :
      ( v2_struct_0(k2_yellow_1(A_302))
      | v1_xboole_0(A_302)
      | ~ v1_xboole_0(B_303)
      | k1_yellow_0(k2_yellow_1(A_302),C_304) = B_303
      | ~ r2_lattice3(k2_yellow_1(A_302),C_304,B_303)
      | ~ m1_subset_1(B_303,A_302) ) ),
    inference(resolution,[status(thm)],[c_485,c_866])).

tff(c_934,plain,(
    ! [A_45,B_95] :
      ( v2_struct_0(k2_yellow_1(A_45))
      | v1_xboole_0(A_45)
      | ~ v1_xboole_0(B_95)
      | k1_yellow_0(k2_yellow_1(A_45),k1_xboole_0) = B_95
      | ~ m1_subset_1(B_95,A_45) ) ),
    inference(resolution,[status(thm)],[c_249,c_876])).

tff(c_977,plain,(
    ! [A_305,B_306] :
      ( v2_struct_0(k2_yellow_1(A_305))
      | v1_xboole_0(A_305)
      | ~ v1_xboole_0(B_306)
      | k3_yellow_0(k2_yellow_1(A_305)) = B_306
      | ~ m1_subset_1(B_306,A_305) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_121,c_934])).

tff(c_995,plain,
    ( v2_struct_0(k2_yellow_1('#skF_4'))
    | v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0)
    | k3_yellow_0(k2_yellow_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_116,c_977])).

tff(c_1006,plain,
    ( v2_struct_0(k2_yellow_1('#skF_4'))
    | v1_xboole_0('#skF_4')
    | k3_yellow_0(k2_yellow_1('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_995])).

tff(c_1007,plain,(
    v2_struct_0(k2_yellow_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_70,c_1006])).

tff(c_123,plain,(
    ! [A_68] :
      ( v1_xboole_0(u1_struct_0(A_68))
      | ~ l1_struct_0(A_68)
      | ~ v2_struct_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [A_45] :
      ( v1_xboole_0(A_45)
      | ~ l1_struct_0(k2_yellow_1(A_45))
      | ~ v2_struct_0(k2_yellow_1(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_123])).

tff(c_1010,plain,
    ( v1_xboole_0('#skF_4')
    | ~ l1_struct_0(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1007,c_126])).

tff(c_1013,plain,(
    ~ l1_struct_0(k2_yellow_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1010])).

tff(c_1016,plain,(
    ~ l1_orders_2(k2_yellow_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_18,c_1013])).

tff(c_1020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1016])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.55/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.61  
% 3.55/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.61  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 3.55/1.61  
% 3.55/1.61  %Foreground sorts:
% 3.55/1.61  
% 3.55/1.61  
% 3.55/1.61  %Background operators:
% 3.55/1.61  
% 3.55/1.61  
% 3.55/1.61  %Foreground operators:
% 3.55/1.61  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.55/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.55/1.61  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.55/1.61  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.55/1.61  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.55/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.55/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.55/1.61  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.55/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.55/1.61  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.55/1.61  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.55/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.55/1.61  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.55/1.61  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.55/1.61  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.55/1.61  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.55/1.61  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.55/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.55/1.61  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.55/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.55/1.61  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.55/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.55/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.55/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.55/1.61  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.55/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.55/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.55/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.55/1.61  
% 3.95/1.63  tff(f_119, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.95/1.63  tff(f_53, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 3.95/1.63  tff(f_152, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.95/1.63  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.95/1.63  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.95/1.63  tff(f_72, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.95/1.63  tff(f_131, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.95/1.63  tff(f_115, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.95/1.63  tff(f_127, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.95/1.63  tff(f_106, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 3.95/1.63  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.95/1.63  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.95/1.63  tff(f_144, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.95/1.63  tff(f_68, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.95/1.63  tff(f_49, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_struct_0)).
% 3.95/1.63  tff(c_48, plain, (![A_43]: (l1_orders_2(k2_yellow_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.95/1.63  tff(c_18, plain, (![A_13]: (l1_struct_0(A_13) | ~l1_orders_2(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.95/1.63  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.95/1.63  tff(c_66, plain, (k3_yellow_0(k2_yellow_1('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.95/1.63  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.95/1.63  tff(c_68, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.95/1.63  tff(c_108, plain, (![A_64, B_65]: (m1_subset_1(A_64, B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.95/1.63  tff(c_116, plain, (m1_subset_1(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_68, c_108])).
% 3.95/1.63  tff(c_117, plain, (![A_66]: (k1_yellow_0(A_66, k1_xboole_0)=k3_yellow_0(A_66) | ~l1_orders_2(A_66))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.95/1.63  tff(c_121, plain, (![A_43]: (k1_yellow_0(k2_yellow_1(A_43), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_43)))), inference(resolution, [status(thm)], [c_48, c_117])).
% 3.95/1.63  tff(c_58, plain, (![A_45]: (u1_struct_0(k2_yellow_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.95/1.63  tff(c_229, plain, (![A_94, B_95]: (r2_lattice3(A_94, k1_xboole_0, B_95) | ~m1_subset_1(B_95, u1_struct_0(A_94)) | ~l1_orders_2(A_94))), inference(cnfTransformation, [status(thm)], [f_115])).
% 3.95/1.63  tff(c_244, plain, (![A_45, B_95]: (r2_lattice3(k2_yellow_1(A_45), k1_xboole_0, B_95) | ~m1_subset_1(B_95, A_45) | ~l1_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_229])).
% 3.95/1.63  tff(c_249, plain, (![A_45, B_95]: (r2_lattice3(k2_yellow_1(A_45), k1_xboole_0, B_95) | ~m1_subset_1(B_95, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_244])).
% 3.95/1.63  tff(c_56, plain, (![A_44]: (v5_orders_2(k2_yellow_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.95/1.63  tff(c_469, plain, (![A_189, B_190, C_191]: (m1_subset_1('#skF_3'(A_189, B_190, C_191), u1_struct_0(A_189)) | k1_yellow_0(A_189, C_191)=B_190 | ~r2_lattice3(A_189, C_191, B_190) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l1_orders_2(A_189) | ~v5_orders_2(A_189))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.95/1.63  tff(c_480, plain, (![A_45, B_190, C_191]: (m1_subset_1('#skF_3'(k2_yellow_1(A_45), B_190, C_191), A_45) | k1_yellow_0(k2_yellow_1(A_45), C_191)=B_190 | ~r2_lattice3(k2_yellow_1(A_45), C_191, B_190) | ~m1_subset_1(B_190, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_469])).
% 3.95/1.63  tff(c_485, plain, (![A_45, B_190, C_191]: (m1_subset_1('#skF_3'(k2_yellow_1(A_45), B_190, C_191), A_45) | k1_yellow_0(k2_yellow_1(A_45), C_191)=B_190 | ~r2_lattice3(k2_yellow_1(A_45), C_191, B_190) | ~m1_subset_1(B_190, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_58, c_480])).
% 3.95/1.63  tff(c_127, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69, B_70), A_69) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.95/1.63  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.63  tff(c_135, plain, (![A_69, B_70]: (~v1_xboole_0(A_69) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_127, c_2])).
% 3.95/1.63  tff(c_52, plain, (![A_44]: (v3_orders_2(k2_yellow_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.95/1.63  tff(c_62, plain, (![A_46, B_50, C_52]: (r3_orders_2(k2_yellow_1(A_46), B_50, C_52) | ~r1_tarski(B_50, C_52) | ~m1_subset_1(C_52, u1_struct_0(k2_yellow_1(A_46))) | ~m1_subset_1(B_50, u1_struct_0(k2_yellow_1(A_46))) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_144])).
% 3.95/1.63  tff(c_356, plain, (![A_138, B_139, C_140]: (r3_orders_2(k2_yellow_1(A_138), B_139, C_140) | ~r1_tarski(B_139, C_140) | ~m1_subset_1(C_140, A_138) | ~m1_subset_1(B_139, A_138) | v1_xboole_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_62])).
% 3.95/1.63  tff(c_22, plain, (![A_14, B_15, C_16]: (r1_orders_2(A_14, B_15, C_16) | ~r3_orders_2(A_14, B_15, C_16) | ~m1_subset_1(C_16, u1_struct_0(A_14)) | ~m1_subset_1(B_15, u1_struct_0(A_14)) | ~l1_orders_2(A_14) | ~v3_orders_2(A_14) | v2_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.95/1.63  tff(c_358, plain, (![A_138, B_139, C_140]: (r1_orders_2(k2_yellow_1(A_138), B_139, C_140) | ~m1_subset_1(C_140, u1_struct_0(k2_yellow_1(A_138))) | ~m1_subset_1(B_139, u1_struct_0(k2_yellow_1(A_138))) | ~l1_orders_2(k2_yellow_1(A_138)) | ~v3_orders_2(k2_yellow_1(A_138)) | v2_struct_0(k2_yellow_1(A_138)) | ~r1_tarski(B_139, C_140) | ~m1_subset_1(C_140, A_138) | ~m1_subset_1(B_139, A_138) | v1_xboole_0(A_138))), inference(resolution, [status(thm)], [c_356, c_22])).
% 3.95/1.63  tff(c_364, plain, (![A_138, B_139, C_140]: (r1_orders_2(k2_yellow_1(A_138), B_139, C_140) | v2_struct_0(k2_yellow_1(A_138)) | ~r1_tarski(B_139, C_140) | ~m1_subset_1(C_140, A_138) | ~m1_subset_1(B_139, A_138) | v1_xboole_0(A_138))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_58, c_58, c_358])).
% 3.95/1.63  tff(c_461, plain, (![A_186, B_187, C_188]: (~r1_orders_2(A_186, B_187, '#skF_3'(A_186, B_187, C_188)) | k1_yellow_0(A_186, C_188)=B_187 | ~r2_lattice3(A_186, C_188, B_187) | ~m1_subset_1(B_187, u1_struct_0(A_186)) | ~l1_orders_2(A_186) | ~v5_orders_2(A_186))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.95/1.63  tff(c_465, plain, (![A_138, C_188, B_139]: (k1_yellow_0(k2_yellow_1(A_138), C_188)=B_139 | ~r2_lattice3(k2_yellow_1(A_138), C_188, B_139) | ~m1_subset_1(B_139, u1_struct_0(k2_yellow_1(A_138))) | ~l1_orders_2(k2_yellow_1(A_138)) | ~v5_orders_2(k2_yellow_1(A_138)) | v2_struct_0(k2_yellow_1(A_138)) | ~r1_tarski(B_139, '#skF_3'(k2_yellow_1(A_138), B_139, C_188)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_138), B_139, C_188), A_138) | ~m1_subset_1(B_139, A_138) | v1_xboole_0(A_138))), inference(resolution, [status(thm)], [c_364, c_461])).
% 3.95/1.63  tff(c_841, plain, (![A_279, C_280, B_281]: (k1_yellow_0(k2_yellow_1(A_279), C_280)=B_281 | ~r2_lattice3(k2_yellow_1(A_279), C_280, B_281) | v2_struct_0(k2_yellow_1(A_279)) | ~r1_tarski(B_281, '#skF_3'(k2_yellow_1(A_279), B_281, C_280)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_279), B_281, C_280), A_279) | ~m1_subset_1(B_281, A_279) | v1_xboole_0(A_279))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_48, c_58, c_465])).
% 3.95/1.63  tff(c_866, plain, (![A_296, C_297, A_298]: (k1_yellow_0(k2_yellow_1(A_296), C_297)=A_298 | ~r2_lattice3(k2_yellow_1(A_296), C_297, A_298) | v2_struct_0(k2_yellow_1(A_296)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_296), A_298, C_297), A_296) | ~m1_subset_1(A_298, A_296) | v1_xboole_0(A_296) | ~v1_xboole_0(A_298))), inference(resolution, [status(thm)], [c_135, c_841])).
% 3.95/1.63  tff(c_876, plain, (![A_302, B_303, C_304]: (v2_struct_0(k2_yellow_1(A_302)) | v1_xboole_0(A_302) | ~v1_xboole_0(B_303) | k1_yellow_0(k2_yellow_1(A_302), C_304)=B_303 | ~r2_lattice3(k2_yellow_1(A_302), C_304, B_303) | ~m1_subset_1(B_303, A_302))), inference(resolution, [status(thm)], [c_485, c_866])).
% 3.95/1.63  tff(c_934, plain, (![A_45, B_95]: (v2_struct_0(k2_yellow_1(A_45)) | v1_xboole_0(A_45) | ~v1_xboole_0(B_95) | k1_yellow_0(k2_yellow_1(A_45), k1_xboole_0)=B_95 | ~m1_subset_1(B_95, A_45))), inference(resolution, [status(thm)], [c_249, c_876])).
% 3.95/1.63  tff(c_977, plain, (![A_305, B_306]: (v2_struct_0(k2_yellow_1(A_305)) | v1_xboole_0(A_305) | ~v1_xboole_0(B_306) | k3_yellow_0(k2_yellow_1(A_305))=B_306 | ~m1_subset_1(B_306, A_305))), inference(demodulation, [status(thm), theory('equality')], [c_121, c_934])).
% 3.95/1.63  tff(c_995, plain, (v2_struct_0(k2_yellow_1('#skF_4')) | v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0) | k3_yellow_0(k2_yellow_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_116, c_977])).
% 3.95/1.63  tff(c_1006, plain, (v2_struct_0(k2_yellow_1('#skF_4')) | v1_xboole_0('#skF_4') | k3_yellow_0(k2_yellow_1('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_995])).
% 3.95/1.63  tff(c_1007, plain, (v2_struct_0(k2_yellow_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_70, c_1006])).
% 3.95/1.63  tff(c_123, plain, (![A_68]: (v1_xboole_0(u1_struct_0(A_68)) | ~l1_struct_0(A_68) | ~v2_struct_0(A_68))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.95/1.63  tff(c_126, plain, (![A_45]: (v1_xboole_0(A_45) | ~l1_struct_0(k2_yellow_1(A_45)) | ~v2_struct_0(k2_yellow_1(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_123])).
% 3.95/1.63  tff(c_1010, plain, (v1_xboole_0('#skF_4') | ~l1_struct_0(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_1007, c_126])).
% 3.95/1.63  tff(c_1013, plain, (~l1_struct_0(k2_yellow_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_70, c_1010])).
% 3.95/1.63  tff(c_1016, plain, (~l1_orders_2(k2_yellow_1('#skF_4'))), inference(resolution, [status(thm)], [c_18, c_1013])).
% 3.95/1.63  tff(c_1020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1016])).
% 3.95/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.63  
% 3.95/1.63  Inference rules
% 3.95/1.63  ----------------------
% 3.95/1.63  #Ref     : 0
% 3.95/1.63  #Sup     : 181
% 3.95/1.63  #Fact    : 0
% 3.95/1.63  #Define  : 0
% 3.95/1.63  #Split   : 1
% 3.95/1.63  #Chain   : 0
% 3.95/1.63  #Close   : 0
% 3.95/1.63  
% 3.95/1.63  Ordering : KBO
% 3.95/1.63  
% 3.95/1.63  Simplification rules
% 3.95/1.63  ----------------------
% 3.95/1.63  #Subsume      : 36
% 3.95/1.63  #Demod        : 258
% 3.95/1.63  #Tautology    : 27
% 3.95/1.63  #SimpNegUnit  : 3
% 3.95/1.63  #BackRed      : 0
% 3.95/1.63  
% 3.95/1.63  #Partial instantiations: 0
% 3.95/1.63  #Strategies tried      : 1
% 3.95/1.63  
% 3.95/1.63  Timing (in seconds)
% 3.95/1.63  ----------------------
% 3.95/1.63  Preprocessing        : 0.34
% 3.95/1.63  Parsing              : 0.18
% 3.95/1.63  CNF conversion       : 0.03
% 3.95/1.63  Main loop            : 0.53
% 3.95/1.63  Inferencing          : 0.22
% 3.95/1.63  Reduction            : 0.15
% 3.95/1.63  Demodulation         : 0.10
% 3.95/1.63  BG Simplification    : 0.03
% 3.95/1.63  Subsumption          : 0.10
% 3.95/1.63  Abstraction          : 0.02
% 3.95/1.63  MUC search           : 0.00
% 3.95/1.63  Cooper               : 0.00
% 3.95/1.63  Total                : 0.90
% 3.95/1.63  Index Insertion      : 0.00
% 3.95/1.63  Index Deletion       : 0.00
% 3.95/1.63  Index Matching       : 0.00
% 3.95/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
