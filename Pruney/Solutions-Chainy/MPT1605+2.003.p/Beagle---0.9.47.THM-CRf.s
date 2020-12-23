%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:26 EST 2020

% Result     : Theorem 3.52s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 112 expanded)
%              Number of leaves         :   43 (  60 expanded)
%              Depth                    :   15
%              Number of atoms          :  190 ( 257 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

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

tff(f_150,negated_conjecture,(
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

tff(f_109,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_62,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_129,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_105,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_117,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_96,axiom,(
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

tff(f_142,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_125,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(c_70,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_66,plain,(
    k3_yellow_0(k2_yellow_1('#skF_4')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    r2_hidden(k1_xboole_0,'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_109,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(A_63,B_64)
      | ~ r2_hidden(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_117,plain,(
    m1_subset_1(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_68,c_109])).

tff(c_44,plain,(
    ! [A_41] : l1_orders_2(k2_yellow_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_118,plain,(
    ! [A_65] :
      ( k1_yellow_0(A_65,k1_xboole_0) = k3_yellow_0(A_65)
      | ~ l1_orders_2(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_122,plain,(
    ! [A_41] : k1_yellow_0(k2_yellow_1(A_41),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_41)) ),
    inference(resolution,[status(thm)],[c_44,c_118])).

tff(c_58,plain,(
    ! [A_44] : u1_struct_0(k2_yellow_1(A_44)) = A_44 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_247,plain,(
    ! [A_95,B_96] :
      ( r2_lattice3(A_95,k1_xboole_0,B_96)
      | ~ m1_subset_1(B_96,u1_struct_0(A_95))
      | ~ l1_orders_2(A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_262,plain,(
    ! [A_44,B_96] :
      ( r2_lattice3(k2_yellow_1(A_44),k1_xboole_0,B_96)
      | ~ m1_subset_1(B_96,A_44)
      | ~ l1_orders_2(k2_yellow_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_247])).

tff(c_267,plain,(
    ! [A_44,B_96] :
      ( r2_lattice3(k2_yellow_1(A_44),k1_xboole_0,B_96)
      | ~ m1_subset_1(B_96,A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_262])).

tff(c_52,plain,(
    ! [A_42] : v5_orders_2(k2_yellow_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_457,plain,(
    ! [A_183,B_184,C_185] :
      ( m1_subset_1('#skF_3'(A_183,B_184,C_185),u1_struct_0(A_183))
      | k1_yellow_0(A_183,C_185) = B_184
      | ~ r2_lattice3(A_183,C_185,B_184)
      | ~ m1_subset_1(B_184,u1_struct_0(A_183))
      | ~ l1_orders_2(A_183)
      | ~ v5_orders_2(A_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_468,plain,(
    ! [A_44,B_184,C_185] :
      ( m1_subset_1('#skF_3'(k2_yellow_1(A_44),B_184,C_185),A_44)
      | k1_yellow_0(k2_yellow_1(A_44),C_185) = B_184
      | ~ r2_lattice3(k2_yellow_1(A_44),C_185,B_184)
      | ~ m1_subset_1(B_184,u1_struct_0(k2_yellow_1(A_44)))
      | ~ l1_orders_2(k2_yellow_1(A_44))
      | ~ v5_orders_2(k2_yellow_1(A_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_457])).

tff(c_473,plain,(
    ! [A_44,B_184,C_185] :
      ( m1_subset_1('#skF_3'(k2_yellow_1(A_44),B_184,C_185),A_44)
      | k1_yellow_0(k2_yellow_1(A_44),C_185) = B_184
      | ~ r2_lattice3(k2_yellow_1(A_44),C_185,B_184)
      | ~ m1_subset_1(B_184,A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_58,c_468])).

tff(c_134,plain,(
    ! [A_70,B_71] :
      ( r2_hidden('#skF_2'(A_70,B_71),A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    ! [A_70,B_71] :
      ( ~ v1_xboole_0(A_70)
      | r1_tarski(A_70,B_71) ) ),
    inference(resolution,[status(thm)],[c_134,c_2])).

tff(c_48,plain,(
    ! [A_42] : v3_orders_2(k2_yellow_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_62,plain,(
    ! [A_45,B_49,C_51] :
      ( r3_orders_2(k2_yellow_1(A_45),B_49,C_51)
      | ~ r1_tarski(B_49,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(k2_yellow_1(A_45)))
      | ~ m1_subset_1(B_49,u1_struct_0(k2_yellow_1(A_45)))
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_72,plain,(
    ! [A_45,B_49,C_51] :
      ( r3_orders_2(k2_yellow_1(A_45),B_49,C_51)
      | ~ r1_tarski(B_49,C_51)
      | ~ m1_subset_1(C_51,A_45)
      | ~ m1_subset_1(B_49,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_62])).

tff(c_431,plain,(
    ! [A_168,B_169,C_170] :
      ( r1_orders_2(A_168,B_169,C_170)
      | ~ r3_orders_2(A_168,B_169,C_170)
      | ~ m1_subset_1(C_170,u1_struct_0(A_168))
      | ~ m1_subset_1(B_169,u1_struct_0(A_168))
      | ~ l1_orders_2(A_168)
      | ~ v3_orders_2(A_168)
      | v2_struct_0(A_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_435,plain,(
    ! [A_45,B_49,C_51] :
      ( r1_orders_2(k2_yellow_1(A_45),B_49,C_51)
      | ~ m1_subset_1(C_51,u1_struct_0(k2_yellow_1(A_45)))
      | ~ m1_subset_1(B_49,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v3_orders_2(k2_yellow_1(A_45))
      | v2_struct_0(k2_yellow_1(A_45))
      | ~ r1_tarski(B_49,C_51)
      | ~ m1_subset_1(C_51,A_45)
      | ~ m1_subset_1(B_49,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_72,c_431])).

tff(c_441,plain,(
    ! [A_45,B_49,C_51] :
      ( r1_orders_2(k2_yellow_1(A_45),B_49,C_51)
      | v2_struct_0(k2_yellow_1(A_45))
      | ~ r1_tarski(B_49,C_51)
      | ~ m1_subset_1(C_51,A_45)
      | ~ m1_subset_1(B_49,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_58,c_58,c_435])).

tff(c_489,plain,(
    ! [A_189,B_190,C_191] :
      ( ~ r1_orders_2(A_189,B_190,'#skF_3'(A_189,B_190,C_191))
      | k1_yellow_0(A_189,C_191) = B_190
      | ~ r2_lattice3(A_189,C_191,B_190)
      | ~ m1_subset_1(B_190,u1_struct_0(A_189))
      | ~ l1_orders_2(A_189)
      | ~ v5_orders_2(A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_493,plain,(
    ! [A_45,C_191,B_49] :
      ( k1_yellow_0(k2_yellow_1(A_45),C_191) = B_49
      | ~ r2_lattice3(k2_yellow_1(A_45),C_191,B_49)
      | ~ m1_subset_1(B_49,u1_struct_0(k2_yellow_1(A_45)))
      | ~ l1_orders_2(k2_yellow_1(A_45))
      | ~ v5_orders_2(k2_yellow_1(A_45))
      | v2_struct_0(k2_yellow_1(A_45))
      | ~ r1_tarski(B_49,'#skF_3'(k2_yellow_1(A_45),B_49,C_191))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_45),B_49,C_191),A_45)
      | ~ m1_subset_1(B_49,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_441,c_489])).

tff(c_822,plain,(
    ! [A_274,C_275,B_276] :
      ( k1_yellow_0(k2_yellow_1(A_274),C_275) = B_276
      | ~ r2_lattice3(k2_yellow_1(A_274),C_275,B_276)
      | v2_struct_0(k2_yellow_1(A_274))
      | ~ r1_tarski(B_276,'#skF_3'(k2_yellow_1(A_274),B_276,C_275))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_274),B_276,C_275),A_274)
      | ~ m1_subset_1(B_276,A_274)
      | v1_xboole_0(A_274) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_58,c_493])).

tff(c_830,plain,(
    ! [A_285,C_286,A_287] :
      ( k1_yellow_0(k2_yellow_1(A_285),C_286) = A_287
      | ~ r2_lattice3(k2_yellow_1(A_285),C_286,A_287)
      | v2_struct_0(k2_yellow_1(A_285))
      | ~ m1_subset_1('#skF_3'(k2_yellow_1(A_285),A_287,C_286),A_285)
      | ~ m1_subset_1(A_287,A_285)
      | v1_xboole_0(A_285)
      | ~ v1_xboole_0(A_287) ) ),
    inference(resolution,[status(thm)],[c_147,c_822])).

tff(c_855,plain,(
    ! [A_292,B_293,C_294] :
      ( v2_struct_0(k2_yellow_1(A_292))
      | v1_xboole_0(A_292)
      | ~ v1_xboole_0(B_293)
      | k1_yellow_0(k2_yellow_1(A_292),C_294) = B_293
      | ~ r2_lattice3(k2_yellow_1(A_292),C_294,B_293)
      | ~ m1_subset_1(B_293,A_292) ) ),
    inference(resolution,[status(thm)],[c_473,c_830])).

tff(c_913,plain,(
    ! [A_44,B_96] :
      ( v2_struct_0(k2_yellow_1(A_44))
      | v1_xboole_0(A_44)
      | ~ v1_xboole_0(B_96)
      | k1_yellow_0(k2_yellow_1(A_44),k1_xboole_0) = B_96
      | ~ m1_subset_1(B_96,A_44) ) ),
    inference(resolution,[status(thm)],[c_267,c_855])).

tff(c_956,plain,(
    ! [A_295,B_296] :
      ( v2_struct_0(k2_yellow_1(A_295))
      | v1_xboole_0(A_295)
      | ~ v1_xboole_0(B_296)
      | k3_yellow_0(k2_yellow_1(A_295)) = B_296
      | ~ m1_subset_1(B_296,A_295) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_913])).

tff(c_974,plain,
    ( v2_struct_0(k2_yellow_1('#skF_4'))
    | v1_xboole_0('#skF_4')
    | ~ v1_xboole_0(k1_xboole_0)
    | k3_yellow_0(k2_yellow_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_117,c_956])).

tff(c_985,plain,
    ( v2_struct_0(k2_yellow_1('#skF_4'))
    | v1_xboole_0('#skF_4')
    | k3_yellow_0(k2_yellow_1('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_974])).

tff(c_986,plain,(
    v2_struct_0(k2_yellow_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_70,c_985])).

tff(c_56,plain,(
    ! [A_43] :
      ( ~ v2_struct_0(k2_yellow_1(A_43))
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_989,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_986,c_56])).

tff(c_993,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_989])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.52/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.60  
% 3.52/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.52/1.61  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 3.52/1.61  
% 3.52/1.61  %Foreground sorts:
% 3.52/1.61  
% 3.52/1.61  
% 3.52/1.61  %Background operators:
% 3.52/1.61  
% 3.52/1.61  
% 3.52/1.61  %Foreground operators:
% 3.52/1.61  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.52/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.52/1.61  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.52/1.61  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.52/1.61  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.52/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.52/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.52/1.61  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.52/1.61  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.52/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.52/1.61  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.52/1.61  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.52/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.52/1.61  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.52/1.61  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.52/1.61  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.52/1.61  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.52/1.61  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.52/1.61  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.52/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.52/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.52/1.61  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.52/1.61  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.52/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.52/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.52/1.61  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.52/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.52/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.52/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.52/1.61  
% 3.82/1.62  tff(f_150, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.82/1.62  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.82/1.62  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.82/1.62  tff(f_109, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.82/1.62  tff(f_62, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.82/1.62  tff(f_129, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.82/1.62  tff(f_105, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.82/1.62  tff(f_117, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.82/1.62  tff(f_96, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 3.82/1.62  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.82/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.82/1.62  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.82/1.62  tff(f_58, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.82/1.62  tff(f_125, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.82/1.62  tff(c_70, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.82/1.62  tff(c_66, plain, (k3_yellow_0(k2_yellow_1('#skF_4'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.82/1.62  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.62  tff(c_68, plain, (r2_hidden(k1_xboole_0, '#skF_4')), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.82/1.62  tff(c_109, plain, (![A_63, B_64]: (m1_subset_1(A_63, B_64) | ~r2_hidden(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/1.62  tff(c_117, plain, (m1_subset_1(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_68, c_109])).
% 3.82/1.62  tff(c_44, plain, (![A_41]: (l1_orders_2(k2_yellow_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 3.82/1.62  tff(c_118, plain, (![A_65]: (k1_yellow_0(A_65, k1_xboole_0)=k3_yellow_0(A_65) | ~l1_orders_2(A_65))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.82/1.62  tff(c_122, plain, (![A_41]: (k1_yellow_0(k2_yellow_1(A_41), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_41)))), inference(resolution, [status(thm)], [c_44, c_118])).
% 3.82/1.62  tff(c_58, plain, (![A_44]: (u1_struct_0(k2_yellow_1(A_44))=A_44)), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.82/1.62  tff(c_247, plain, (![A_95, B_96]: (r2_lattice3(A_95, k1_xboole_0, B_96) | ~m1_subset_1(B_96, u1_struct_0(A_95)) | ~l1_orders_2(A_95))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.82/1.62  tff(c_262, plain, (![A_44, B_96]: (r2_lattice3(k2_yellow_1(A_44), k1_xboole_0, B_96) | ~m1_subset_1(B_96, A_44) | ~l1_orders_2(k2_yellow_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_247])).
% 3.82/1.62  tff(c_267, plain, (![A_44, B_96]: (r2_lattice3(k2_yellow_1(A_44), k1_xboole_0, B_96) | ~m1_subset_1(B_96, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_262])).
% 3.82/1.62  tff(c_52, plain, (![A_42]: (v5_orders_2(k2_yellow_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.82/1.62  tff(c_457, plain, (![A_183, B_184, C_185]: (m1_subset_1('#skF_3'(A_183, B_184, C_185), u1_struct_0(A_183)) | k1_yellow_0(A_183, C_185)=B_184 | ~r2_lattice3(A_183, C_185, B_184) | ~m1_subset_1(B_184, u1_struct_0(A_183)) | ~l1_orders_2(A_183) | ~v5_orders_2(A_183))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.82/1.62  tff(c_468, plain, (![A_44, B_184, C_185]: (m1_subset_1('#skF_3'(k2_yellow_1(A_44), B_184, C_185), A_44) | k1_yellow_0(k2_yellow_1(A_44), C_185)=B_184 | ~r2_lattice3(k2_yellow_1(A_44), C_185, B_184) | ~m1_subset_1(B_184, u1_struct_0(k2_yellow_1(A_44))) | ~l1_orders_2(k2_yellow_1(A_44)) | ~v5_orders_2(k2_yellow_1(A_44)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_457])).
% 3.82/1.62  tff(c_473, plain, (![A_44, B_184, C_185]: (m1_subset_1('#skF_3'(k2_yellow_1(A_44), B_184, C_185), A_44) | k1_yellow_0(k2_yellow_1(A_44), C_185)=B_184 | ~r2_lattice3(k2_yellow_1(A_44), C_185, B_184) | ~m1_subset_1(B_184, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_58, c_468])).
% 3.82/1.62  tff(c_134, plain, (![A_70, B_71]: (r2_hidden('#skF_2'(A_70, B_71), A_70) | r1_tarski(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.82/1.62  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.82/1.62  tff(c_147, plain, (![A_70, B_71]: (~v1_xboole_0(A_70) | r1_tarski(A_70, B_71))), inference(resolution, [status(thm)], [c_134, c_2])).
% 3.82/1.62  tff(c_48, plain, (![A_42]: (v3_orders_2(k2_yellow_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.82/1.62  tff(c_62, plain, (![A_45, B_49, C_51]: (r3_orders_2(k2_yellow_1(A_45), B_49, C_51) | ~r1_tarski(B_49, C_51) | ~m1_subset_1(C_51, u1_struct_0(k2_yellow_1(A_45))) | ~m1_subset_1(B_49, u1_struct_0(k2_yellow_1(A_45))) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_142])).
% 3.82/1.62  tff(c_72, plain, (![A_45, B_49, C_51]: (r3_orders_2(k2_yellow_1(A_45), B_49, C_51) | ~r1_tarski(B_49, C_51) | ~m1_subset_1(C_51, A_45) | ~m1_subset_1(B_49, A_45) | v1_xboole_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_62])).
% 3.82/1.62  tff(c_431, plain, (![A_168, B_169, C_170]: (r1_orders_2(A_168, B_169, C_170) | ~r3_orders_2(A_168, B_169, C_170) | ~m1_subset_1(C_170, u1_struct_0(A_168)) | ~m1_subset_1(B_169, u1_struct_0(A_168)) | ~l1_orders_2(A_168) | ~v3_orders_2(A_168) | v2_struct_0(A_168))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.82/1.62  tff(c_435, plain, (![A_45, B_49, C_51]: (r1_orders_2(k2_yellow_1(A_45), B_49, C_51) | ~m1_subset_1(C_51, u1_struct_0(k2_yellow_1(A_45))) | ~m1_subset_1(B_49, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v3_orders_2(k2_yellow_1(A_45)) | v2_struct_0(k2_yellow_1(A_45)) | ~r1_tarski(B_49, C_51) | ~m1_subset_1(C_51, A_45) | ~m1_subset_1(B_49, A_45) | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_72, c_431])).
% 3.82/1.62  tff(c_441, plain, (![A_45, B_49, C_51]: (r1_orders_2(k2_yellow_1(A_45), B_49, C_51) | v2_struct_0(k2_yellow_1(A_45)) | ~r1_tarski(B_49, C_51) | ~m1_subset_1(C_51, A_45) | ~m1_subset_1(B_49, A_45) | v1_xboole_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_58, c_58, c_435])).
% 3.82/1.62  tff(c_489, plain, (![A_189, B_190, C_191]: (~r1_orders_2(A_189, B_190, '#skF_3'(A_189, B_190, C_191)) | k1_yellow_0(A_189, C_191)=B_190 | ~r2_lattice3(A_189, C_191, B_190) | ~m1_subset_1(B_190, u1_struct_0(A_189)) | ~l1_orders_2(A_189) | ~v5_orders_2(A_189))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.82/1.62  tff(c_493, plain, (![A_45, C_191, B_49]: (k1_yellow_0(k2_yellow_1(A_45), C_191)=B_49 | ~r2_lattice3(k2_yellow_1(A_45), C_191, B_49) | ~m1_subset_1(B_49, u1_struct_0(k2_yellow_1(A_45))) | ~l1_orders_2(k2_yellow_1(A_45)) | ~v5_orders_2(k2_yellow_1(A_45)) | v2_struct_0(k2_yellow_1(A_45)) | ~r1_tarski(B_49, '#skF_3'(k2_yellow_1(A_45), B_49, C_191)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_45), B_49, C_191), A_45) | ~m1_subset_1(B_49, A_45) | v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_441, c_489])).
% 3.82/1.62  tff(c_822, plain, (![A_274, C_275, B_276]: (k1_yellow_0(k2_yellow_1(A_274), C_275)=B_276 | ~r2_lattice3(k2_yellow_1(A_274), C_275, B_276) | v2_struct_0(k2_yellow_1(A_274)) | ~r1_tarski(B_276, '#skF_3'(k2_yellow_1(A_274), B_276, C_275)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_274), B_276, C_275), A_274) | ~m1_subset_1(B_276, A_274) | v1_xboole_0(A_274))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_58, c_493])).
% 3.82/1.62  tff(c_830, plain, (![A_285, C_286, A_287]: (k1_yellow_0(k2_yellow_1(A_285), C_286)=A_287 | ~r2_lattice3(k2_yellow_1(A_285), C_286, A_287) | v2_struct_0(k2_yellow_1(A_285)) | ~m1_subset_1('#skF_3'(k2_yellow_1(A_285), A_287, C_286), A_285) | ~m1_subset_1(A_287, A_285) | v1_xboole_0(A_285) | ~v1_xboole_0(A_287))), inference(resolution, [status(thm)], [c_147, c_822])).
% 3.82/1.62  tff(c_855, plain, (![A_292, B_293, C_294]: (v2_struct_0(k2_yellow_1(A_292)) | v1_xboole_0(A_292) | ~v1_xboole_0(B_293) | k1_yellow_0(k2_yellow_1(A_292), C_294)=B_293 | ~r2_lattice3(k2_yellow_1(A_292), C_294, B_293) | ~m1_subset_1(B_293, A_292))), inference(resolution, [status(thm)], [c_473, c_830])).
% 3.82/1.62  tff(c_913, plain, (![A_44, B_96]: (v2_struct_0(k2_yellow_1(A_44)) | v1_xboole_0(A_44) | ~v1_xboole_0(B_96) | k1_yellow_0(k2_yellow_1(A_44), k1_xboole_0)=B_96 | ~m1_subset_1(B_96, A_44))), inference(resolution, [status(thm)], [c_267, c_855])).
% 3.82/1.62  tff(c_956, plain, (![A_295, B_296]: (v2_struct_0(k2_yellow_1(A_295)) | v1_xboole_0(A_295) | ~v1_xboole_0(B_296) | k3_yellow_0(k2_yellow_1(A_295))=B_296 | ~m1_subset_1(B_296, A_295))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_913])).
% 3.82/1.62  tff(c_974, plain, (v2_struct_0(k2_yellow_1('#skF_4')) | v1_xboole_0('#skF_4') | ~v1_xboole_0(k1_xboole_0) | k3_yellow_0(k2_yellow_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_117, c_956])).
% 3.82/1.62  tff(c_985, plain, (v2_struct_0(k2_yellow_1('#skF_4')) | v1_xboole_0('#skF_4') | k3_yellow_0(k2_yellow_1('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_974])).
% 3.82/1.62  tff(c_986, plain, (v2_struct_0(k2_yellow_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_66, c_70, c_985])).
% 3.82/1.62  tff(c_56, plain, (![A_43]: (~v2_struct_0(k2_yellow_1(A_43)) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.82/1.62  tff(c_989, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_986, c_56])).
% 3.82/1.62  tff(c_993, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_989])).
% 3.82/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.62  
% 3.82/1.62  Inference rules
% 3.82/1.62  ----------------------
% 3.82/1.62  #Ref     : 0
% 3.82/1.62  #Sup     : 176
% 3.82/1.62  #Fact    : 0
% 3.82/1.62  #Define  : 0
% 3.82/1.62  #Split   : 1
% 3.82/1.62  #Chain   : 0
% 3.82/1.62  #Close   : 0
% 3.82/1.62  
% 3.82/1.62  Ordering : KBO
% 3.82/1.62  
% 3.82/1.62  Simplification rules
% 3.82/1.62  ----------------------
% 3.82/1.62  #Subsume      : 35
% 3.82/1.62  #Demod        : 242
% 3.82/1.62  #Tautology    : 27
% 3.82/1.62  #SimpNegUnit  : 3
% 3.82/1.62  #BackRed      : 0
% 3.82/1.62  
% 3.82/1.62  #Partial instantiations: 0
% 3.82/1.62  #Strategies tried      : 1
% 3.82/1.62  
% 3.82/1.62  Timing (in seconds)
% 3.82/1.62  ----------------------
% 3.82/1.63  Preprocessing        : 0.33
% 3.82/1.63  Parsing              : 0.17
% 3.82/1.63  CNF conversion       : 0.03
% 3.82/1.63  Main loop            : 0.49
% 3.82/1.63  Inferencing          : 0.20
% 3.82/1.63  Reduction            : 0.14
% 3.82/1.63  Demodulation         : 0.09
% 3.82/1.63  BG Simplification    : 0.02
% 3.82/1.63  Subsumption          : 0.09
% 3.82/1.63  Abstraction          : 0.02
% 3.82/1.63  MUC search           : 0.00
% 3.82/1.63  Cooper               : 0.00
% 3.82/1.63  Total                : 0.85
% 3.82/1.63  Index Insertion      : 0.00
% 3.82/1.63  Index Deletion       : 0.00
% 3.82/1.63  Index Matching       : 0.00
% 3.82/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
