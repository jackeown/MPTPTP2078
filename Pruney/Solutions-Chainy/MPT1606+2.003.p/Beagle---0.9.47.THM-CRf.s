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
% DateTime   : Thu Dec  3 10:25:28 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 121 expanded)
%              Number of leaves         :   41 (  63 expanded)
%              Depth                    :   16
%              Number of atoms          :  193 ( 305 expanded)
%              Number of equality atoms :   23 (  60 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_orders_2,type,(
    v1_orders_2: $i > $o )).

tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(r3_orders_2,type,(
    r3_orders_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v3_orders_2,type,(
    v3_orders_2: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_orders_2,type,(
    r1_orders_2: ( $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(r2_yellow_0,type,(
    r2_yellow_0: ( $i * $i ) > $o )).

tff(k2_yellow_0,type,(
    k2_yellow_0: ( $i * $i ) > $i )).

tff(r1_lattice3,type,(
    r1_lattice3: ( $i * $i * $i ) > $o )).

tff(v4_orders_2,type,(
    v4_orders_2: $i > $o )).

tff(v5_orders_2,type,(
    v5_orders_2: $i > $o )).

tff(l1_orders_2,type,(
    l1_orders_2: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff(k1_yellow_1,type,(
    k1_yellow_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(u1_orders_2,type,(
    u1_orders_2: $i > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k3_tarski(A),A)
         => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k4_yellow_0(A) = k2_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_yellow_0)).

tff(f_125,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_101,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_113,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v5_orders_2(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( ( ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) )
               => ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) ) )
              & ( ( r1_lattice3(A,C,B)
                  & ! [D] :
                      ( m1_subset_1(D,u1_struct_0(A))
                     => ( r1_lattice3(A,C,D)
                       => r1_orders_2(A,D,B) ) ) )
               => ( B = k2_yellow_0(A,C)
                  & r2_yellow_0(A,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_yellow_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

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

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_121,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_58,plain,(
    k4_yellow_0(k2_yellow_1('#skF_2')) != k3_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_60,plain,(
    r2_hidden(k3_tarski('#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_91,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(A_55,B_56)
      | ~ r2_hidden(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_95,plain,(
    m1_subset_1(k3_tarski('#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_36,plain,(
    ! [A_36] : l1_orders_2(k2_yellow_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_96,plain,(
    ! [A_57] :
      ( k2_yellow_0(A_57,k1_xboole_0) = k4_yellow_0(A_57)
      | ~ l1_orders_2(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_100,plain,(
    ! [A_36] : k2_yellow_0(k2_yellow_1(A_36),k1_xboole_0) = k4_yellow_0(k2_yellow_1(A_36)) ),
    inference(resolution,[status(thm)],[c_36,c_96])).

tff(c_50,plain,(
    ! [A_39] : u1_struct_0(k2_yellow_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_116,plain,(
    ! [A_63,B_64] :
      ( r1_lattice3(A_63,k1_xboole_0,B_64)
      | ~ m1_subset_1(B_64,u1_struct_0(A_63))
      | ~ l1_orders_2(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_119,plain,(
    ! [A_39,B_64] :
      ( r1_lattice3(k2_yellow_1(A_39),k1_xboole_0,B_64)
      | ~ m1_subset_1(B_64,A_39)
      | ~ l1_orders_2(k2_yellow_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_116])).

tff(c_121,plain,(
    ! [A_39,B_64] :
      ( r1_lattice3(k2_yellow_1(A_39),k1_xboole_0,B_64)
      | ~ m1_subset_1(B_64,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_119])).

tff(c_44,plain,(
    ! [A_37] : v5_orders_2(k2_yellow_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_219,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1('#skF_1'(A_111,B_112,C_113),u1_struct_0(A_111))
      | k2_yellow_0(A_111,C_113) = B_112
      | ~ r1_lattice3(A_111,C_113,B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_230,plain,(
    ! [A_39,B_112,C_113] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_39),B_112,C_113),A_39)
      | k2_yellow_0(k2_yellow_1(A_39),C_113) = B_112
      | ~ r1_lattice3(k2_yellow_1(A_39),C_113,B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(k2_yellow_1(A_39)))
      | ~ l1_orders_2(k2_yellow_1(A_39))
      | ~ v5_orders_2(k2_yellow_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_219])).

tff(c_235,plain,(
    ! [A_39,B_112,C_113] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_39),B_112,C_113),A_39)
      | k2_yellow_0(k2_yellow_1(A_39),C_113) = B_112
      | ~ r1_lattice3(k2_yellow_1(A_39),C_113,B_112)
      | ~ m1_subset_1(B_112,A_39) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_50,c_230])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,k3_tarski(B_2))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_40,plain,(
    ! [A_37] : v3_orders_2(k2_yellow_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_54,plain,(
    ! [A_40,B_44,C_46] :
      ( r3_orders_2(k2_yellow_1(A_40),B_44,C_46)
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(k2_yellow_1(A_40)))
      | ~ m1_subset_1(B_44,u1_struct_0(k2_yellow_1(A_40)))
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_64,plain,(
    ! [A_40,B_44,C_46] :
      ( r3_orders_2(k2_yellow_1(A_40),B_44,C_46)
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,A_40)
      | ~ m1_subset_1(B_44,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_54])).

tff(c_163,plain,(
    ! [A_96,B_97,C_98] :
      ( r1_orders_2(A_96,B_97,C_98)
      | ~ r3_orders_2(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v3_orders_2(A_96)
      | v2_struct_0(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_167,plain,(
    ! [A_40,B_44,C_46] :
      ( r1_orders_2(k2_yellow_1(A_40),B_44,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(k2_yellow_1(A_40)))
      | ~ m1_subset_1(B_44,u1_struct_0(k2_yellow_1(A_40)))
      | ~ l1_orders_2(k2_yellow_1(A_40))
      | ~ v3_orders_2(k2_yellow_1(A_40))
      | v2_struct_0(k2_yellow_1(A_40))
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,A_40)
      | ~ m1_subset_1(B_44,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_64,c_163])).

tff(c_173,plain,(
    ! [A_40,B_44,C_46] :
      ( r1_orders_2(k2_yellow_1(A_40),B_44,C_46)
      | v2_struct_0(k2_yellow_1(A_40))
      | ~ r1_tarski(B_44,C_46)
      | ~ m1_subset_1(C_46,A_40)
      | ~ m1_subset_1(B_44,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36,c_50,c_50,c_167])).

tff(c_252,plain,(
    ! [A_120,B_121,C_122] :
      ( ~ r1_orders_2(A_120,'#skF_1'(A_120,B_121,C_122),B_121)
      | k2_yellow_0(A_120,C_122) = B_121
      | ~ r1_lattice3(A_120,C_122,B_121)
      | ~ m1_subset_1(B_121,u1_struct_0(A_120))
      | ~ l1_orders_2(A_120)
      | ~ v5_orders_2(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_256,plain,(
    ! [A_40,C_122,C_46] :
      ( k2_yellow_0(k2_yellow_1(A_40),C_122) = C_46
      | ~ r1_lattice3(k2_yellow_1(A_40),C_122,C_46)
      | ~ m1_subset_1(C_46,u1_struct_0(k2_yellow_1(A_40)))
      | ~ l1_orders_2(k2_yellow_1(A_40))
      | ~ v5_orders_2(k2_yellow_1(A_40))
      | v2_struct_0(k2_yellow_1(A_40))
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_40),C_46,C_122),C_46)
      | ~ m1_subset_1(C_46,A_40)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_40),C_46,C_122),A_40)
      | v1_xboole_0(A_40) ) ),
    inference(resolution,[status(thm)],[c_173,c_252])).

tff(c_363,plain,(
    ! [A_176,C_177,C_178] :
      ( k2_yellow_0(k2_yellow_1(A_176),C_177) = C_178
      | ~ r1_lattice3(k2_yellow_1(A_176),C_177,C_178)
      | v2_struct_0(k2_yellow_1(A_176))
      | ~ r1_tarski('#skF_1'(k2_yellow_1(A_176),C_178,C_177),C_178)
      | ~ m1_subset_1(C_178,A_176)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_176),C_178,C_177),A_176)
      | v1_xboole_0(A_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_36,c_50,c_256])).

tff(c_377,plain,(
    ! [B_182,A_183,C_184] :
      ( k3_tarski(B_182) = k2_yellow_0(k2_yellow_1(A_183),C_184)
      | ~ r1_lattice3(k2_yellow_1(A_183),C_184,k3_tarski(B_182))
      | v2_struct_0(k2_yellow_1(A_183))
      | ~ m1_subset_1(k3_tarski(B_182),A_183)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_183),k3_tarski(B_182),C_184),A_183)
      | v1_xboole_0(A_183)
      | ~ r2_hidden('#skF_1'(k2_yellow_1(A_183),k3_tarski(B_182),C_184),B_182) ) ),
    inference(resolution,[status(thm)],[c_2,c_363])).

tff(c_392,plain,(
    ! [A_188,B_189,C_190] :
      ( v2_struct_0(k2_yellow_1(A_188))
      | v1_xboole_0(A_188)
      | ~ r2_hidden('#skF_1'(k2_yellow_1(A_188),k3_tarski(B_189),C_190),B_189)
      | k3_tarski(B_189) = k2_yellow_0(k2_yellow_1(A_188),C_190)
      | ~ r1_lattice3(k2_yellow_1(A_188),C_190,k3_tarski(B_189))
      | ~ m1_subset_1(k3_tarski(B_189),A_188) ) ),
    inference(resolution,[status(thm)],[c_235,c_377])).

tff(c_447,plain,(
    ! [A_201,B_202,C_203] :
      ( v2_struct_0(k2_yellow_1(A_201))
      | v1_xboole_0(A_201)
      | k3_tarski(B_202) = k2_yellow_0(k2_yellow_1(A_201),C_203)
      | ~ r1_lattice3(k2_yellow_1(A_201),C_203,k3_tarski(B_202))
      | ~ m1_subset_1(k3_tarski(B_202),A_201)
      | v1_xboole_0(B_202)
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_201),k3_tarski(B_202),C_203),B_202) ) ),
    inference(resolution,[status(thm)],[c_6,c_392])).

tff(c_472,plain,(
    ! [A_204,C_205] :
      ( v2_struct_0(k2_yellow_1(A_204))
      | v1_xboole_0(A_204)
      | k2_yellow_0(k2_yellow_1(A_204),C_205) = k3_tarski(A_204)
      | ~ r1_lattice3(k2_yellow_1(A_204),C_205,k3_tarski(A_204))
      | ~ m1_subset_1(k3_tarski(A_204),A_204) ) ),
    inference(resolution,[status(thm)],[c_235,c_447])).

tff(c_476,plain,(
    ! [A_39] :
      ( v2_struct_0(k2_yellow_1(A_39))
      | v1_xboole_0(A_39)
      | k2_yellow_0(k2_yellow_1(A_39),k1_xboole_0) = k3_tarski(A_39)
      | ~ m1_subset_1(k3_tarski(A_39),A_39) ) ),
    inference(resolution,[status(thm)],[c_121,c_472])).

tff(c_479,plain,(
    ! [A_206] :
      ( v2_struct_0(k2_yellow_1(A_206))
      | v1_xboole_0(A_206)
      | k4_yellow_0(k2_yellow_1(A_206)) = k3_tarski(A_206)
      | ~ m1_subset_1(k3_tarski(A_206),A_206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_476])).

tff(c_482,plain,
    ( v2_struct_0(k2_yellow_1('#skF_2'))
    | v1_xboole_0('#skF_2')
    | k4_yellow_0(k2_yellow_1('#skF_2')) = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_95,c_479])).

tff(c_485,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_62,c_482])).

tff(c_48,plain,(
    ! [A_38] :
      ( ~ v2_struct_0(k2_yellow_1(A_38))
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_488,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_485,c_48])).

tff(c_492,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:31:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.46  
% 3.09/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.46  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_yellow_0 > r2_hidden > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k2_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k4_yellow_0 > k3_tarski > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.09/1.46  
% 3.09/1.46  %Foreground sorts:
% 3.09/1.46  
% 3.09/1.46  
% 3.09/1.46  %Background operators:
% 3.09/1.46  
% 3.09/1.46  
% 3.09/1.46  %Foreground operators:
% 3.09/1.46  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.09/1.46  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.09/1.46  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.09/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.09/1.46  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.09/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.46  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.09/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.46  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.09/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.46  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.09/1.46  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.46  tff(r2_yellow_0, type, r2_yellow_0: ($i * $i) > $o).
% 3.09/1.46  tff(k2_yellow_0, type, k2_yellow_0: ($i * $i) > $i).
% 3.09/1.46  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.09/1.46  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.09/1.46  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.09/1.46  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.09/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.46  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.09/1.46  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 3.09/1.46  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.09/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.46  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.09/1.46  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.09/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.46  
% 3.26/1.48  tff(f_146, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 3.26/1.48  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.26/1.48  tff(f_105, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.26/1.48  tff(f_58, axiom, (![A]: (l1_orders_2(A) => (k4_yellow_0(A) = k2_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_yellow_0)).
% 3.26/1.48  tff(f_125, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.26/1.48  tff(f_101, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.26/1.48  tff(f_113, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.26/1.48  tff(f_92, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C)) => (r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B)))))) & ((r1_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r1_lattice3(A, C, D) => r1_orders_2(A, D, B))))) => ((B = k2_yellow_0(A, C)) & r2_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_yellow_0)).
% 3.26/1.48  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.26/1.48  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.26/1.48  tff(f_138, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.26/1.48  tff(f_54, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.26/1.48  tff(f_121, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.26/1.48  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.26/1.48  tff(c_58, plain, (k4_yellow_0(k2_yellow_1('#skF_2'))!=k3_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.26/1.48  tff(c_60, plain, (r2_hidden(k3_tarski('#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 3.26/1.48  tff(c_91, plain, (![A_55, B_56]: (m1_subset_1(A_55, B_56) | ~r2_hidden(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.26/1.48  tff(c_95, plain, (m1_subset_1(k3_tarski('#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_60, c_91])).
% 3.26/1.48  tff(c_36, plain, (![A_36]: (l1_orders_2(k2_yellow_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.26/1.48  tff(c_96, plain, (![A_57]: (k2_yellow_0(A_57, k1_xboole_0)=k4_yellow_0(A_57) | ~l1_orders_2(A_57))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.26/1.48  tff(c_100, plain, (![A_36]: (k2_yellow_0(k2_yellow_1(A_36), k1_xboole_0)=k4_yellow_0(k2_yellow_1(A_36)))), inference(resolution, [status(thm)], [c_36, c_96])).
% 3.26/1.48  tff(c_50, plain, (![A_39]: (u1_struct_0(k2_yellow_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.26/1.48  tff(c_116, plain, (![A_63, B_64]: (r1_lattice3(A_63, k1_xboole_0, B_64) | ~m1_subset_1(B_64, u1_struct_0(A_63)) | ~l1_orders_2(A_63))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.26/1.48  tff(c_119, plain, (![A_39, B_64]: (r1_lattice3(k2_yellow_1(A_39), k1_xboole_0, B_64) | ~m1_subset_1(B_64, A_39) | ~l1_orders_2(k2_yellow_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_116])).
% 3.26/1.48  tff(c_121, plain, (![A_39, B_64]: (r1_lattice3(k2_yellow_1(A_39), k1_xboole_0, B_64) | ~m1_subset_1(B_64, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_119])).
% 3.26/1.48  tff(c_44, plain, (![A_37]: (v5_orders_2(k2_yellow_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.26/1.48  tff(c_219, plain, (![A_111, B_112, C_113]: (m1_subset_1('#skF_1'(A_111, B_112, C_113), u1_struct_0(A_111)) | k2_yellow_0(A_111, C_113)=B_112 | ~r1_lattice3(A_111, C_113, B_112) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.26/1.48  tff(c_230, plain, (![A_39, B_112, C_113]: (m1_subset_1('#skF_1'(k2_yellow_1(A_39), B_112, C_113), A_39) | k2_yellow_0(k2_yellow_1(A_39), C_113)=B_112 | ~r1_lattice3(k2_yellow_1(A_39), C_113, B_112) | ~m1_subset_1(B_112, u1_struct_0(k2_yellow_1(A_39))) | ~l1_orders_2(k2_yellow_1(A_39)) | ~v5_orders_2(k2_yellow_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_219])).
% 3.26/1.48  tff(c_235, plain, (![A_39, B_112, C_113]: (m1_subset_1('#skF_1'(k2_yellow_1(A_39), B_112, C_113), A_39) | k2_yellow_0(k2_yellow_1(A_39), C_113)=B_112 | ~r1_lattice3(k2_yellow_1(A_39), C_113, B_112) | ~m1_subset_1(B_112, A_39))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_50, c_230])).
% 3.26/1.48  tff(c_6, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.26/1.48  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k3_tarski(B_2)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.26/1.48  tff(c_40, plain, (![A_37]: (v3_orders_2(k2_yellow_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.26/1.48  tff(c_54, plain, (![A_40, B_44, C_46]: (r3_orders_2(k2_yellow_1(A_40), B_44, C_46) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, u1_struct_0(k2_yellow_1(A_40))) | ~m1_subset_1(B_44, u1_struct_0(k2_yellow_1(A_40))) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.26/1.48  tff(c_64, plain, (![A_40, B_44, C_46]: (r3_orders_2(k2_yellow_1(A_40), B_44, C_46) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, A_40) | ~m1_subset_1(B_44, A_40) | v1_xboole_0(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_54])).
% 3.26/1.48  tff(c_163, plain, (![A_96, B_97, C_98]: (r1_orders_2(A_96, B_97, C_98) | ~r3_orders_2(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v3_orders_2(A_96) | v2_struct_0(A_96))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.26/1.48  tff(c_167, plain, (![A_40, B_44, C_46]: (r1_orders_2(k2_yellow_1(A_40), B_44, C_46) | ~m1_subset_1(C_46, u1_struct_0(k2_yellow_1(A_40))) | ~m1_subset_1(B_44, u1_struct_0(k2_yellow_1(A_40))) | ~l1_orders_2(k2_yellow_1(A_40)) | ~v3_orders_2(k2_yellow_1(A_40)) | v2_struct_0(k2_yellow_1(A_40)) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, A_40) | ~m1_subset_1(B_44, A_40) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_64, c_163])).
% 3.26/1.48  tff(c_173, plain, (![A_40, B_44, C_46]: (r1_orders_2(k2_yellow_1(A_40), B_44, C_46) | v2_struct_0(k2_yellow_1(A_40)) | ~r1_tarski(B_44, C_46) | ~m1_subset_1(C_46, A_40) | ~m1_subset_1(B_44, A_40) | v1_xboole_0(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36, c_50, c_50, c_167])).
% 3.26/1.48  tff(c_252, plain, (![A_120, B_121, C_122]: (~r1_orders_2(A_120, '#skF_1'(A_120, B_121, C_122), B_121) | k2_yellow_0(A_120, C_122)=B_121 | ~r1_lattice3(A_120, C_122, B_121) | ~m1_subset_1(B_121, u1_struct_0(A_120)) | ~l1_orders_2(A_120) | ~v5_orders_2(A_120))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.26/1.48  tff(c_256, plain, (![A_40, C_122, C_46]: (k2_yellow_0(k2_yellow_1(A_40), C_122)=C_46 | ~r1_lattice3(k2_yellow_1(A_40), C_122, C_46) | ~m1_subset_1(C_46, u1_struct_0(k2_yellow_1(A_40))) | ~l1_orders_2(k2_yellow_1(A_40)) | ~v5_orders_2(k2_yellow_1(A_40)) | v2_struct_0(k2_yellow_1(A_40)) | ~r1_tarski('#skF_1'(k2_yellow_1(A_40), C_46, C_122), C_46) | ~m1_subset_1(C_46, A_40) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_40), C_46, C_122), A_40) | v1_xboole_0(A_40))), inference(resolution, [status(thm)], [c_173, c_252])).
% 3.26/1.48  tff(c_363, plain, (![A_176, C_177, C_178]: (k2_yellow_0(k2_yellow_1(A_176), C_177)=C_178 | ~r1_lattice3(k2_yellow_1(A_176), C_177, C_178) | v2_struct_0(k2_yellow_1(A_176)) | ~r1_tarski('#skF_1'(k2_yellow_1(A_176), C_178, C_177), C_178) | ~m1_subset_1(C_178, A_176) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_176), C_178, C_177), A_176) | v1_xboole_0(A_176))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_36, c_50, c_256])).
% 3.26/1.48  tff(c_377, plain, (![B_182, A_183, C_184]: (k3_tarski(B_182)=k2_yellow_0(k2_yellow_1(A_183), C_184) | ~r1_lattice3(k2_yellow_1(A_183), C_184, k3_tarski(B_182)) | v2_struct_0(k2_yellow_1(A_183)) | ~m1_subset_1(k3_tarski(B_182), A_183) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_183), k3_tarski(B_182), C_184), A_183) | v1_xboole_0(A_183) | ~r2_hidden('#skF_1'(k2_yellow_1(A_183), k3_tarski(B_182), C_184), B_182))), inference(resolution, [status(thm)], [c_2, c_363])).
% 3.26/1.48  tff(c_392, plain, (![A_188, B_189, C_190]: (v2_struct_0(k2_yellow_1(A_188)) | v1_xboole_0(A_188) | ~r2_hidden('#skF_1'(k2_yellow_1(A_188), k3_tarski(B_189), C_190), B_189) | k3_tarski(B_189)=k2_yellow_0(k2_yellow_1(A_188), C_190) | ~r1_lattice3(k2_yellow_1(A_188), C_190, k3_tarski(B_189)) | ~m1_subset_1(k3_tarski(B_189), A_188))), inference(resolution, [status(thm)], [c_235, c_377])).
% 3.26/1.48  tff(c_447, plain, (![A_201, B_202, C_203]: (v2_struct_0(k2_yellow_1(A_201)) | v1_xboole_0(A_201) | k3_tarski(B_202)=k2_yellow_0(k2_yellow_1(A_201), C_203) | ~r1_lattice3(k2_yellow_1(A_201), C_203, k3_tarski(B_202)) | ~m1_subset_1(k3_tarski(B_202), A_201) | v1_xboole_0(B_202) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_201), k3_tarski(B_202), C_203), B_202))), inference(resolution, [status(thm)], [c_6, c_392])).
% 3.26/1.48  tff(c_472, plain, (![A_204, C_205]: (v2_struct_0(k2_yellow_1(A_204)) | v1_xboole_0(A_204) | k2_yellow_0(k2_yellow_1(A_204), C_205)=k3_tarski(A_204) | ~r1_lattice3(k2_yellow_1(A_204), C_205, k3_tarski(A_204)) | ~m1_subset_1(k3_tarski(A_204), A_204))), inference(resolution, [status(thm)], [c_235, c_447])).
% 3.26/1.48  tff(c_476, plain, (![A_39]: (v2_struct_0(k2_yellow_1(A_39)) | v1_xboole_0(A_39) | k2_yellow_0(k2_yellow_1(A_39), k1_xboole_0)=k3_tarski(A_39) | ~m1_subset_1(k3_tarski(A_39), A_39))), inference(resolution, [status(thm)], [c_121, c_472])).
% 3.26/1.48  tff(c_479, plain, (![A_206]: (v2_struct_0(k2_yellow_1(A_206)) | v1_xboole_0(A_206) | k4_yellow_0(k2_yellow_1(A_206))=k3_tarski(A_206) | ~m1_subset_1(k3_tarski(A_206), A_206))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_476])).
% 3.26/1.48  tff(c_482, plain, (v2_struct_0(k2_yellow_1('#skF_2')) | v1_xboole_0('#skF_2') | k4_yellow_0(k2_yellow_1('#skF_2'))=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_95, c_479])).
% 3.26/1.48  tff(c_485, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_58, c_62, c_482])).
% 3.26/1.48  tff(c_48, plain, (![A_38]: (~v2_struct_0(k2_yellow_1(A_38)) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.26/1.48  tff(c_488, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_485, c_48])).
% 3.26/1.48  tff(c_492, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_488])).
% 3.26/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  Inference rules
% 3.26/1.48  ----------------------
% 3.26/1.48  #Ref     : 0
% 3.26/1.48  #Sup     : 75
% 3.26/1.48  #Fact    : 0
% 3.26/1.48  #Define  : 0
% 3.26/1.48  #Split   : 1
% 3.26/1.48  #Chain   : 0
% 3.26/1.48  #Close   : 0
% 3.26/1.48  
% 3.26/1.48  Ordering : KBO
% 3.26/1.48  
% 3.26/1.48  Simplification rules
% 3.26/1.48  ----------------------
% 3.26/1.48  #Subsume      : 11
% 3.26/1.48  #Demod        : 118
% 3.26/1.48  #Tautology    : 14
% 3.26/1.48  #SimpNegUnit  : 3
% 3.26/1.48  #BackRed      : 0
% 3.26/1.48  
% 3.26/1.48  #Partial instantiations: 0
% 3.26/1.48  #Strategies tried      : 1
% 3.26/1.48  
% 3.26/1.48  Timing (in seconds)
% 3.26/1.48  ----------------------
% 3.26/1.48  Preprocessing        : 0.35
% 3.26/1.48  Parsing              : 0.18
% 3.26/1.48  CNF conversion       : 0.03
% 3.26/1.48  Main loop            : 0.35
% 3.26/1.48  Inferencing          : 0.15
% 3.26/1.48  Reduction            : 0.10
% 3.26/1.48  Demodulation         : 0.07
% 3.26/1.48  BG Simplification    : 0.02
% 3.26/1.48  Subsumption          : 0.06
% 3.26/1.48  Abstraction          : 0.02
% 3.26/1.48  MUC search           : 0.00
% 3.26/1.48  Cooper               : 0.00
% 3.26/1.48  Total                : 0.73
% 3.26/1.48  Index Insertion      : 0.00
% 3.26/1.48  Index Deletion       : 0.00
% 3.26/1.48  Index Matching       : 0.00
% 3.26/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
