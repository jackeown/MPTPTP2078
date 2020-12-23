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
% DateTime   : Thu Dec  3 10:25:25 EST 2020

% Result     : Theorem 3.79s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 711 expanded)
%              Number of leaves         :   39 ( 289 expanded)
%              Depth                    :   14
%              Number of atoms          :  383 (2094 expanded)
%              Number of equality atoms :   22 ( 386 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_143,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_170,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_131,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_123,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k12_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k12_lattice3)).

tff(f_119,axiom,(
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

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ! [D] :
                  ( m1_subset_1(D,u1_struct_0(A))
                 => ( D = k11_lattice3(A,B,C)
                  <=> ( r1_orders_2(A,D,B)
                      & r1_orders_2(A,D,C)
                      & ! [E] :
                          ( m1_subset_1(E,u1_struct_0(A))
                         => ( ( r1_orders_2(A,E,B)
                              & r1_orders_2(A,E,C) )
                           => r1_orders_2(A,E,D) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l28_lattice3)).

tff(f_139,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_156,axiom,(
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

tff(c_46,plain,(
    ! [A_71] : u1_struct_0(k2_yellow_1(A_71)) = A_71 ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_63,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_58])).

tff(c_56,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_64,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_56])).

tff(c_60,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_40,plain,(
    ! [A_69] : v5_orders_2(k2_yellow_1(A_69)) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    ! [A_68] : l1_orders_2(k2_yellow_1(A_68)) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_979,plain,(
    ! [A_201,B_202,C_203] :
      ( k12_lattice3(A_201,B_202,C_203) = k11_lattice3(A_201,B_202,C_203)
      | ~ m1_subset_1(C_203,u1_struct_0(A_201))
      | ~ m1_subset_1(B_202,u1_struct_0(A_201))
      | ~ l1_orders_2(A_201)
      | ~ v2_lattice3(A_201)
      | ~ v5_orders_2(A_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_986,plain,(
    ! [A_71,B_202,C_203] :
      ( k12_lattice3(k2_yellow_1(A_71),B_202,C_203) = k11_lattice3(k2_yellow_1(A_71),B_202,C_203)
      | ~ m1_subset_1(C_203,A_71)
      | ~ m1_subset_1(B_202,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_979])).

tff(c_997,plain,(
    ! [A_204,B_205,C_206] :
      ( k12_lattice3(k2_yellow_1(A_204),B_205,C_206) = k11_lattice3(k2_yellow_1(A_204),B_205,C_206)
      | ~ m1_subset_1(C_206,A_204)
      | ~ m1_subset_1(B_205,A_204)
      | ~ v2_lattice3(k2_yellow_1(A_204)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_986])).

tff(c_1001,plain,(
    ! [B_207,C_208] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_207,C_208) = k11_lattice3(k2_yellow_1('#skF_2'),B_207,C_208)
      | ~ m1_subset_1(C_208,'#skF_2')
      | ~ m1_subset_1(B_207,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_997])).

tff(c_779,plain,(
    ! [A_174,B_175,C_176] :
      ( m1_subset_1(k12_lattice3(A_174,B_175,C_176),u1_struct_0(A_174))
      | ~ m1_subset_1(C_176,u1_struct_0(A_174))
      | ~ m1_subset_1(B_175,u1_struct_0(A_174))
      | ~ l1_orders_2(A_174)
      | ~ v2_lattice3(A_174)
      | ~ v5_orders_2(A_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_782,plain,(
    ! [A_71,B_175,C_176] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_71),B_175,C_176),A_71)
      | ~ m1_subset_1(C_176,u1_struct_0(k2_yellow_1(A_71)))
      | ~ m1_subset_1(B_175,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_779])).

tff(c_784,plain,(
    ! [A_71,B_175,C_176] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_71),B_175,C_176),A_71)
      | ~ m1_subset_1(C_176,A_71)
      | ~ m1_subset_1(B_175,A_71)
      | ~ v2_lattice3(k2_yellow_1(A_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_46,c_782])).

tff(c_1007,plain,(
    ! [B_207,C_208] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_207,C_208),'#skF_2')
      | ~ m1_subset_1(C_208,'#skF_2')
      | ~ m1_subset_1(B_207,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_208,'#skF_2')
      | ~ m1_subset_1(B_207,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1001,c_784])).

tff(c_1016,plain,(
    ! [B_207,C_208] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_207,C_208),'#skF_2')
      | ~ m1_subset_1(C_208,'#skF_2')
      | ~ m1_subset_1(B_207,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1007])).

tff(c_62,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_894,plain,(
    ! [A_190,C_191,B_192] :
      ( k11_lattice3(A_190,C_191,B_192) = k11_lattice3(A_190,B_192,C_191)
      | ~ m1_subset_1(C_191,u1_struct_0(A_190))
      | ~ m1_subset_1(B_192,u1_struct_0(A_190))
      | ~ l1_orders_2(A_190)
      | ~ v2_lattice3(A_190)
      | ~ v5_orders_2(A_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_901,plain,(
    ! [A_71,C_191,B_192] :
      ( k11_lattice3(k2_yellow_1(A_71),C_191,B_192) = k11_lattice3(k2_yellow_1(A_71),B_192,C_191)
      | ~ m1_subset_1(C_191,A_71)
      | ~ m1_subset_1(B_192,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_894])).

tff(c_911,plain,(
    ! [A_196,C_197,B_198] :
      ( k11_lattice3(k2_yellow_1(A_196),C_197,B_198) = k11_lattice3(k2_yellow_1(A_196),B_198,C_197)
      | ~ m1_subset_1(C_197,A_196)
      | ~ m1_subset_1(B_198,A_196)
      | ~ v2_lattice3(k2_yellow_1(A_196)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_901])).

tff(c_914,plain,(
    ! [C_197,B_198] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_197,B_198) = k11_lattice3(k2_yellow_1('#skF_2'),B_198,C_197)
      | ~ m1_subset_1(C_197,'#skF_2')
      | ~ m1_subset_1(B_198,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_911])).

tff(c_1179,plain,(
    ! [A_227,B_228,C_229] :
      ( r1_orders_2(A_227,k11_lattice3(A_227,B_228,C_229),C_229)
      | ~ m1_subset_1(k11_lattice3(A_227,B_228,C_229),u1_struct_0(A_227))
      | ~ m1_subset_1(C_229,u1_struct_0(A_227))
      | ~ m1_subset_1(B_228,u1_struct_0(A_227))
      | ~ l1_orders_2(A_227)
      | ~ v2_lattice3(A_227)
      | ~ v5_orders_2(A_227)
      | v2_struct_0(A_227) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1181,plain,(
    ! [B_198,C_197] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_198,C_197),C_197)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_197,B_198),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_197,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_198,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_197,'#skF_2')
      | ~ m1_subset_1(B_198,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_914,c_1179])).

tff(c_1187,plain,(
    ! [B_198,C_197] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_198,C_197),C_197)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_197,B_198),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_197,'#skF_2')
      | ~ m1_subset_1(B_198,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60,c_32,c_46,c_46,c_46,c_1181])).

tff(c_1281,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1187])).

tff(c_44,plain,(
    ! [A_70] :
      ( ~ v2_struct_0(k2_yellow_1(A_70))
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1284,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1281,c_44])).

tff(c_1288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1284])).

tff(c_1290,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_1291,plain,(
    ! [B_232,C_233] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_232,C_233),C_233)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_233,B_232),'#skF_2')
      | ~ m1_subset_1(C_233,'#skF_2')
      | ~ m1_subset_1(B_232,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_1187])).

tff(c_36,plain,(
    ! [A_69] : v3_orders_2(k2_yellow_1(A_69)) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_879,plain,(
    ! [A_187,B_188,C_189] :
      ( r3_orders_2(A_187,B_188,C_189)
      | ~ r1_orders_2(A_187,B_188,C_189)
      | ~ m1_subset_1(C_189,u1_struct_0(A_187))
      | ~ m1_subset_1(B_188,u1_struct_0(A_187))
      | ~ l1_orders_2(A_187)
      | ~ v3_orders_2(A_187)
      | v2_struct_0(A_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_886,plain,(
    ! [A_71,B_188,C_189] :
      ( r3_orders_2(k2_yellow_1(A_71),B_188,C_189)
      | ~ r1_orders_2(k2_yellow_1(A_71),B_188,C_189)
      | ~ m1_subset_1(C_189,A_71)
      | ~ m1_subset_1(B_188,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v3_orders_2(k2_yellow_1(A_71))
      | v2_struct_0(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_879])).

tff(c_906,plain,(
    ! [A_193,B_194,C_195] :
      ( r3_orders_2(k2_yellow_1(A_193),B_194,C_195)
      | ~ r1_orders_2(k2_yellow_1(A_193),B_194,C_195)
      | ~ m1_subset_1(C_195,A_193)
      | ~ m1_subset_1(B_194,A_193)
      | v2_struct_0(k2_yellow_1(A_193)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_46,c_886])).

tff(c_52,plain,(
    ! [B_76,C_78,A_72] :
      ( r1_tarski(B_76,C_78)
      | ~ r3_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ m1_subset_1(C_78,u1_struct_0(k2_yellow_1(A_72)))
      | ~ m1_subset_1(B_76,u1_struct_0(k2_yellow_1(A_72)))
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_65,plain,(
    ! [B_76,C_78,A_72] :
      ( r1_tarski(B_76,C_78)
      | ~ r3_orders_2(k2_yellow_1(A_72),B_76,C_78)
      | ~ m1_subset_1(C_78,A_72)
      | ~ m1_subset_1(B_76,A_72)
      | v1_xboole_0(A_72) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_46,c_52])).

tff(c_910,plain,(
    ! [B_194,C_195,A_193] :
      ( r1_tarski(B_194,C_195)
      | v1_xboole_0(A_193)
      | ~ r1_orders_2(k2_yellow_1(A_193),B_194,C_195)
      | ~ m1_subset_1(C_195,A_193)
      | ~ m1_subset_1(B_194,A_193)
      | v2_struct_0(k2_yellow_1(A_193)) ) ),
    inference(resolution,[status(thm)],[c_906,c_65])).

tff(c_1294,plain,(
    ! [B_232,C_233] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_232,C_233),C_233)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_232,C_233),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_233,B_232),'#skF_2')
      | ~ m1_subset_1(C_233,'#skF_2')
      | ~ m1_subset_1(B_232,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1291,c_910])).

tff(c_1389,plain,(
    ! [B_242,C_243] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_242,C_243),C_243)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_242,C_243),'#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_243,B_242),'#skF_2')
      | ~ m1_subset_1(C_243,'#skF_2')
      | ~ m1_subset_1(B_242,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1290,c_62,c_1294])).

tff(c_452,plain,(
    ! [A_137,B_138,C_139] :
      ( k12_lattice3(A_137,B_138,C_139) = k11_lattice3(A_137,B_138,C_139)
      | ~ m1_subset_1(C_139,u1_struct_0(A_137))
      | ~ m1_subset_1(B_138,u1_struct_0(A_137))
      | ~ l1_orders_2(A_137)
      | ~ v2_lattice3(A_137)
      | ~ v5_orders_2(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_459,plain,(
    ! [A_71,B_138,C_139] :
      ( k12_lattice3(k2_yellow_1(A_71),B_138,C_139) = k11_lattice3(k2_yellow_1(A_71),B_138,C_139)
      | ~ m1_subset_1(C_139,A_71)
      | ~ m1_subset_1(B_138,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_452])).

tff(c_474,plain,(
    ! [A_143,B_144,C_145] :
      ( k12_lattice3(k2_yellow_1(A_143),B_144,C_145) = k11_lattice3(k2_yellow_1(A_143),B_144,C_145)
      | ~ m1_subset_1(C_145,A_143)
      | ~ m1_subset_1(B_144,A_143)
      | ~ v2_lattice3(k2_yellow_1(A_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_459])).

tff(c_478,plain,(
    ! [B_146,C_147] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_146,C_147) = k11_lattice3(k2_yellow_1('#skF_2'),B_146,C_147)
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_474])).

tff(c_242,plain,(
    ! [A_110,B_111,C_112] :
      ( m1_subset_1(k12_lattice3(A_110,B_111,C_112),u1_struct_0(A_110))
      | ~ m1_subset_1(C_112,u1_struct_0(A_110))
      | ~ m1_subset_1(B_111,u1_struct_0(A_110))
      | ~ l1_orders_2(A_110)
      | ~ v2_lattice3(A_110)
      | ~ v5_orders_2(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_245,plain,(
    ! [A_71,B_111,C_112] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_71),B_111,C_112),A_71)
      | ~ m1_subset_1(C_112,u1_struct_0(k2_yellow_1(A_71)))
      | ~ m1_subset_1(B_111,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_242])).

tff(c_247,plain,(
    ! [A_71,B_111,C_112] :
      ( m1_subset_1(k12_lattice3(k2_yellow_1(A_71),B_111,C_112),A_71)
      | ~ m1_subset_1(C_112,A_71)
      | ~ m1_subset_1(B_111,A_71)
      | ~ v2_lattice3(k2_yellow_1(A_71)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_46,c_245])).

tff(c_484,plain,(
    ! [B_146,C_147] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_146,C_147),'#skF_2')
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2')
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_247])).

tff(c_493,plain,(
    ! [B_146,C_147] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_146,C_147),'#skF_2')
      | ~ m1_subset_1(C_147,'#skF_2')
      | ~ m1_subset_1(B_146,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_484])).

tff(c_365,plain,(
    ! [A_126,C_127,B_128] :
      ( k11_lattice3(A_126,C_127,B_128) = k11_lattice3(A_126,B_128,C_127)
      | ~ m1_subset_1(C_127,u1_struct_0(A_126))
      | ~ m1_subset_1(B_128,u1_struct_0(A_126))
      | ~ l1_orders_2(A_126)
      | ~ v2_lattice3(A_126)
      | ~ v5_orders_2(A_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_372,plain,(
    ! [A_71,C_127,B_128] :
      ( k11_lattice3(k2_yellow_1(A_71),C_127,B_128) = k11_lattice3(k2_yellow_1(A_71),B_128,C_127)
      | ~ m1_subset_1(C_127,A_71)
      | ~ m1_subset_1(B_128,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v2_lattice3(k2_yellow_1(A_71))
      | ~ v5_orders_2(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_365])).

tff(c_377,plain,(
    ! [A_129,C_130,B_131] :
      ( k11_lattice3(k2_yellow_1(A_129),C_130,B_131) = k11_lattice3(k2_yellow_1(A_129),B_131,C_130)
      | ~ m1_subset_1(C_130,A_129)
      | ~ m1_subset_1(B_131,A_129)
      | ~ v2_lattice3(k2_yellow_1(A_129)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_46,c_372])).

tff(c_380,plain,(
    ! [C_130,B_131] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_130,B_131) = k11_lattice3(k2_yellow_1('#skF_2'),B_131,C_130)
      | ~ m1_subset_1(C_130,'#skF_2')
      | ~ m1_subset_1(B_131,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_60,c_377])).

tff(c_559,plain,(
    ! [A_155,B_156,C_157] :
      ( r1_orders_2(A_155,k11_lattice3(A_155,B_156,C_157),B_156)
      | ~ m1_subset_1(k11_lattice3(A_155,B_156,C_157),u1_struct_0(A_155))
      | ~ m1_subset_1(C_157,u1_struct_0(A_155))
      | ~ m1_subset_1(B_156,u1_struct_0(A_155))
      | ~ l1_orders_2(A_155)
      | ~ v2_lattice3(A_155)
      | ~ v5_orders_2(A_155)
      | v2_struct_0(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_561,plain,(
    ! [B_131,C_130] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_131,C_130),B_131)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_130,B_131),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_130,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_131,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_130,'#skF_2')
      | ~ m1_subset_1(B_131,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_559])).

tff(c_567,plain,(
    ! [B_131,C_130] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_131,C_130),B_131)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_130,B_131),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_130,'#skF_2')
      | ~ m1_subset_1(B_131,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_60,c_32,c_46,c_46,c_46,c_561])).

tff(c_661,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_567])).

tff(c_664,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_661,c_44])).

tff(c_668,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_664])).

tff(c_670,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_671,plain,(
    ! [B_160,C_161] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_160,C_161),B_160)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_161,B_160),'#skF_2')
      | ~ m1_subset_1(C_161,'#skF_2')
      | ~ m1_subset_1(B_160,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_567])).

tff(c_440,plain,(
    ! [A_134,B_135,C_136] :
      ( r3_orders_2(A_134,B_135,C_136)
      | ~ r1_orders_2(A_134,B_135,C_136)
      | ~ m1_subset_1(C_136,u1_struct_0(A_134))
      | ~ m1_subset_1(B_135,u1_struct_0(A_134))
      | ~ l1_orders_2(A_134)
      | ~ v3_orders_2(A_134)
      | v2_struct_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_447,plain,(
    ! [A_71,B_135,C_136] :
      ( r3_orders_2(k2_yellow_1(A_71),B_135,C_136)
      | ~ r1_orders_2(k2_yellow_1(A_71),B_135,C_136)
      | ~ m1_subset_1(C_136,A_71)
      | ~ m1_subset_1(B_135,u1_struct_0(k2_yellow_1(A_71)))
      | ~ l1_orders_2(k2_yellow_1(A_71))
      | ~ v3_orders_2(k2_yellow_1(A_71))
      | v2_struct_0(k2_yellow_1(A_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_440])).

tff(c_464,plain,(
    ! [A_140,B_141,C_142] :
      ( r3_orders_2(k2_yellow_1(A_140),B_141,C_142)
      | ~ r1_orders_2(k2_yellow_1(A_140),B_141,C_142)
      | ~ m1_subset_1(C_142,A_140)
      | ~ m1_subset_1(B_141,A_140)
      | v2_struct_0(k2_yellow_1(A_140)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_46,c_447])).

tff(c_473,plain,(
    ! [B_141,C_142,A_140] :
      ( r1_tarski(B_141,C_142)
      | v1_xboole_0(A_140)
      | ~ r1_orders_2(k2_yellow_1(A_140),B_141,C_142)
      | ~ m1_subset_1(C_142,A_140)
      | ~ m1_subset_1(B_141,A_140)
      | v2_struct_0(k2_yellow_1(A_140)) ) ),
    inference(resolution,[status(thm)],[c_464,c_65])).

tff(c_674,plain,(
    ! [B_160,C_161] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_160,C_161),B_160)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_160,C_161),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_161,B_160),'#skF_2')
      | ~ m1_subset_1(C_161,'#skF_2')
      | ~ m1_subset_1(B_160,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_671,c_473])).

tff(c_715,plain,(
    ! [B_167,C_168] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_167,C_168),B_167)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_167,C_168),'#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_168,B_167),'#skF_2')
      | ~ m1_subset_1(C_168,'#skF_2')
      | ~ m1_subset_1(B_167,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_670,c_62,c_674])).

tff(c_120,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_tarski(A_95,k3_xboole_0(B_96,C_97))
      | ~ r1_tarski(A_95,C_97)
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_124,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_120,c_54])).

tff(c_159,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_124])).

tff(c_718,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_715,c_159])).

tff(c_727,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_718])).

tff(c_728,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_727])).

tff(c_731,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_493,c_728])).

tff(c_735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_731])).

tff(c_736,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_727])).

tff(c_740,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_493,c_736])).

tff(c_750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_740])).

tff(c_751,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_124])).

tff(c_1392,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1389,c_751])).

tff(c_1401,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_1392])).

tff(c_1402,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1401])).

tff(c_1405,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_1016,c_1402])).

tff(c_1409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_63,c_1405])).

tff(c_1410,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1401])).

tff(c_1414,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1016,c_1410])).

tff(c_1424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_64,c_1414])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:24:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.79/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.63  
% 3.79/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.63  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.79/1.63  
% 3.79/1.63  %Foreground sorts:
% 3.79/1.63  
% 3.79/1.63  
% 3.79/1.63  %Background operators:
% 3.79/1.63  
% 3.79/1.63  
% 3.79/1.63  %Foreground operators:
% 3.79/1.63  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.79/1.63  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.79/1.63  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.79/1.63  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.79/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.79/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.79/1.63  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.79/1.63  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.79/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.79/1.63  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.79/1.63  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.79/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.79/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.79/1.63  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.79/1.63  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.79/1.63  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.79/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.79/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.79/1.63  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.79/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.79/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.79/1.63  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.79/1.63  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.79/1.63  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.79/1.63  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.79/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.79/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.79/1.63  
% 3.79/1.65  tff(f_143, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.79/1.65  tff(f_170, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.79/1.65  tff(f_131, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.79/1.65  tff(f_123, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.79/1.65  tff(f_105, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.79/1.65  tff(f_60, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k12_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k12_lattice3)).
% 3.79/1.65  tff(f_119, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 3.79/1.65  tff(f_93, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 3.79/1.65  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.79/1.65  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.79/1.65  tff(f_156, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.79/1.65  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.79/1.65  tff(c_46, plain, (![A_71]: (u1_struct_0(k2_yellow_1(A_71))=A_71)), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.79/1.65  tff(c_58, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.79/1.65  tff(c_63, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_58])).
% 3.79/1.65  tff(c_56, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.79/1.65  tff(c_64, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_56])).
% 3.79/1.65  tff(c_60, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.79/1.65  tff(c_40, plain, (![A_69]: (v5_orders_2(k2_yellow_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.79/1.65  tff(c_32, plain, (![A_68]: (l1_orders_2(k2_yellow_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_123])).
% 3.79/1.65  tff(c_979, plain, (![A_201, B_202, C_203]: (k12_lattice3(A_201, B_202, C_203)=k11_lattice3(A_201, B_202, C_203) | ~m1_subset_1(C_203, u1_struct_0(A_201)) | ~m1_subset_1(B_202, u1_struct_0(A_201)) | ~l1_orders_2(A_201) | ~v2_lattice3(A_201) | ~v5_orders_2(A_201))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.79/1.65  tff(c_986, plain, (![A_71, B_202, C_203]: (k12_lattice3(k2_yellow_1(A_71), B_202, C_203)=k11_lattice3(k2_yellow_1(A_71), B_202, C_203) | ~m1_subset_1(C_203, A_71) | ~m1_subset_1(B_202, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_979])).
% 3.79/1.65  tff(c_997, plain, (![A_204, B_205, C_206]: (k12_lattice3(k2_yellow_1(A_204), B_205, C_206)=k11_lattice3(k2_yellow_1(A_204), B_205, C_206) | ~m1_subset_1(C_206, A_204) | ~m1_subset_1(B_205, A_204) | ~v2_lattice3(k2_yellow_1(A_204)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_986])).
% 3.79/1.65  tff(c_1001, plain, (![B_207, C_208]: (k12_lattice3(k2_yellow_1('#skF_2'), B_207, C_208)=k11_lattice3(k2_yellow_1('#skF_2'), B_207, C_208) | ~m1_subset_1(C_208, '#skF_2') | ~m1_subset_1(B_207, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_997])).
% 3.79/1.65  tff(c_779, plain, (![A_174, B_175, C_176]: (m1_subset_1(k12_lattice3(A_174, B_175, C_176), u1_struct_0(A_174)) | ~m1_subset_1(C_176, u1_struct_0(A_174)) | ~m1_subset_1(B_175, u1_struct_0(A_174)) | ~l1_orders_2(A_174) | ~v2_lattice3(A_174) | ~v5_orders_2(A_174))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.79/1.65  tff(c_782, plain, (![A_71, B_175, C_176]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_71), B_175, C_176), A_71) | ~m1_subset_1(C_176, u1_struct_0(k2_yellow_1(A_71))) | ~m1_subset_1(B_175, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_779])).
% 3.79/1.65  tff(c_784, plain, (![A_71, B_175, C_176]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_71), B_175, C_176), A_71) | ~m1_subset_1(C_176, A_71) | ~m1_subset_1(B_175, A_71) | ~v2_lattice3(k2_yellow_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_46, c_782])).
% 3.79/1.65  tff(c_1007, plain, (![B_207, C_208]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_207, C_208), '#skF_2') | ~m1_subset_1(C_208, '#skF_2') | ~m1_subset_1(B_207, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_208, '#skF_2') | ~m1_subset_1(B_207, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1001, c_784])).
% 3.79/1.65  tff(c_1016, plain, (![B_207, C_208]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_207, C_208), '#skF_2') | ~m1_subset_1(C_208, '#skF_2') | ~m1_subset_1(B_207, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1007])).
% 3.79/1.65  tff(c_62, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.79/1.65  tff(c_894, plain, (![A_190, C_191, B_192]: (k11_lattice3(A_190, C_191, B_192)=k11_lattice3(A_190, B_192, C_191) | ~m1_subset_1(C_191, u1_struct_0(A_190)) | ~m1_subset_1(B_192, u1_struct_0(A_190)) | ~l1_orders_2(A_190) | ~v2_lattice3(A_190) | ~v5_orders_2(A_190))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.79/1.65  tff(c_901, plain, (![A_71, C_191, B_192]: (k11_lattice3(k2_yellow_1(A_71), C_191, B_192)=k11_lattice3(k2_yellow_1(A_71), B_192, C_191) | ~m1_subset_1(C_191, A_71) | ~m1_subset_1(B_192, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_894])).
% 3.79/1.65  tff(c_911, plain, (![A_196, C_197, B_198]: (k11_lattice3(k2_yellow_1(A_196), C_197, B_198)=k11_lattice3(k2_yellow_1(A_196), B_198, C_197) | ~m1_subset_1(C_197, A_196) | ~m1_subset_1(B_198, A_196) | ~v2_lattice3(k2_yellow_1(A_196)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_901])).
% 3.79/1.65  tff(c_914, plain, (![C_197, B_198]: (k11_lattice3(k2_yellow_1('#skF_2'), C_197, B_198)=k11_lattice3(k2_yellow_1('#skF_2'), B_198, C_197) | ~m1_subset_1(C_197, '#skF_2') | ~m1_subset_1(B_198, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_911])).
% 3.79/1.65  tff(c_1179, plain, (![A_227, B_228, C_229]: (r1_orders_2(A_227, k11_lattice3(A_227, B_228, C_229), C_229) | ~m1_subset_1(k11_lattice3(A_227, B_228, C_229), u1_struct_0(A_227)) | ~m1_subset_1(C_229, u1_struct_0(A_227)) | ~m1_subset_1(B_228, u1_struct_0(A_227)) | ~l1_orders_2(A_227) | ~v2_lattice3(A_227) | ~v5_orders_2(A_227) | v2_struct_0(A_227))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/1.65  tff(c_1181, plain, (![B_198, C_197]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_198, C_197), C_197) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_197, B_198), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_197, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_198, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_197, '#skF_2') | ~m1_subset_1(B_198, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_914, c_1179])).
% 3.79/1.65  tff(c_1187, plain, (![B_198, C_197]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_198, C_197), C_197) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_197, B_198), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_197, '#skF_2') | ~m1_subset_1(B_198, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60, c_32, c_46, c_46, c_46, c_1181])).
% 3.79/1.65  tff(c_1281, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1187])).
% 3.79/1.65  tff(c_44, plain, (![A_70]: (~v2_struct_0(k2_yellow_1(A_70)) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.79/1.65  tff(c_1284, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1281, c_44])).
% 3.79/1.65  tff(c_1288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_1284])).
% 3.79/1.65  tff(c_1290, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1187])).
% 3.79/1.65  tff(c_1291, plain, (![B_232, C_233]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_232, C_233), C_233) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_233, B_232), '#skF_2') | ~m1_subset_1(C_233, '#skF_2') | ~m1_subset_1(B_232, '#skF_2'))), inference(splitRight, [status(thm)], [c_1187])).
% 3.79/1.65  tff(c_36, plain, (![A_69]: (v3_orders_2(k2_yellow_1(A_69)))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.79/1.65  tff(c_879, plain, (![A_187, B_188, C_189]: (r3_orders_2(A_187, B_188, C_189) | ~r1_orders_2(A_187, B_188, C_189) | ~m1_subset_1(C_189, u1_struct_0(A_187)) | ~m1_subset_1(B_188, u1_struct_0(A_187)) | ~l1_orders_2(A_187) | ~v3_orders_2(A_187) | v2_struct_0(A_187))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.79/1.65  tff(c_886, plain, (![A_71, B_188, C_189]: (r3_orders_2(k2_yellow_1(A_71), B_188, C_189) | ~r1_orders_2(k2_yellow_1(A_71), B_188, C_189) | ~m1_subset_1(C_189, A_71) | ~m1_subset_1(B_188, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v3_orders_2(k2_yellow_1(A_71)) | v2_struct_0(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_879])).
% 3.79/1.65  tff(c_906, plain, (![A_193, B_194, C_195]: (r3_orders_2(k2_yellow_1(A_193), B_194, C_195) | ~r1_orders_2(k2_yellow_1(A_193), B_194, C_195) | ~m1_subset_1(C_195, A_193) | ~m1_subset_1(B_194, A_193) | v2_struct_0(k2_yellow_1(A_193)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_46, c_886])).
% 3.79/1.65  tff(c_52, plain, (![B_76, C_78, A_72]: (r1_tarski(B_76, C_78) | ~r3_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~m1_subset_1(C_78, u1_struct_0(k2_yellow_1(A_72))) | ~m1_subset_1(B_76, u1_struct_0(k2_yellow_1(A_72))) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_156])).
% 3.79/1.65  tff(c_65, plain, (![B_76, C_78, A_72]: (r1_tarski(B_76, C_78) | ~r3_orders_2(k2_yellow_1(A_72), B_76, C_78) | ~m1_subset_1(C_78, A_72) | ~m1_subset_1(B_76, A_72) | v1_xboole_0(A_72))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_46, c_52])).
% 3.79/1.65  tff(c_910, plain, (![B_194, C_195, A_193]: (r1_tarski(B_194, C_195) | v1_xboole_0(A_193) | ~r1_orders_2(k2_yellow_1(A_193), B_194, C_195) | ~m1_subset_1(C_195, A_193) | ~m1_subset_1(B_194, A_193) | v2_struct_0(k2_yellow_1(A_193)))), inference(resolution, [status(thm)], [c_906, c_65])).
% 3.79/1.65  tff(c_1294, plain, (![B_232, C_233]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_232, C_233), C_233) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_232, C_233), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_233, B_232), '#skF_2') | ~m1_subset_1(C_233, '#skF_2') | ~m1_subset_1(B_232, '#skF_2'))), inference(resolution, [status(thm)], [c_1291, c_910])).
% 3.79/1.65  tff(c_1389, plain, (![B_242, C_243]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_242, C_243), C_243) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_242, C_243), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_243, B_242), '#skF_2') | ~m1_subset_1(C_243, '#skF_2') | ~m1_subset_1(B_242, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1290, c_62, c_1294])).
% 3.79/1.65  tff(c_452, plain, (![A_137, B_138, C_139]: (k12_lattice3(A_137, B_138, C_139)=k11_lattice3(A_137, B_138, C_139) | ~m1_subset_1(C_139, u1_struct_0(A_137)) | ~m1_subset_1(B_138, u1_struct_0(A_137)) | ~l1_orders_2(A_137) | ~v2_lattice3(A_137) | ~v5_orders_2(A_137))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.79/1.65  tff(c_459, plain, (![A_71, B_138, C_139]: (k12_lattice3(k2_yellow_1(A_71), B_138, C_139)=k11_lattice3(k2_yellow_1(A_71), B_138, C_139) | ~m1_subset_1(C_139, A_71) | ~m1_subset_1(B_138, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_452])).
% 3.79/1.65  tff(c_474, plain, (![A_143, B_144, C_145]: (k12_lattice3(k2_yellow_1(A_143), B_144, C_145)=k11_lattice3(k2_yellow_1(A_143), B_144, C_145) | ~m1_subset_1(C_145, A_143) | ~m1_subset_1(B_144, A_143) | ~v2_lattice3(k2_yellow_1(A_143)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_459])).
% 3.79/1.65  tff(c_478, plain, (![B_146, C_147]: (k12_lattice3(k2_yellow_1('#skF_2'), B_146, C_147)=k11_lattice3(k2_yellow_1('#skF_2'), B_146, C_147) | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_474])).
% 3.79/1.65  tff(c_242, plain, (![A_110, B_111, C_112]: (m1_subset_1(k12_lattice3(A_110, B_111, C_112), u1_struct_0(A_110)) | ~m1_subset_1(C_112, u1_struct_0(A_110)) | ~m1_subset_1(B_111, u1_struct_0(A_110)) | ~l1_orders_2(A_110) | ~v2_lattice3(A_110) | ~v5_orders_2(A_110))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.79/1.65  tff(c_245, plain, (![A_71, B_111, C_112]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_71), B_111, C_112), A_71) | ~m1_subset_1(C_112, u1_struct_0(k2_yellow_1(A_71))) | ~m1_subset_1(B_111, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_242])).
% 3.79/1.65  tff(c_247, plain, (![A_71, B_111, C_112]: (m1_subset_1(k12_lattice3(k2_yellow_1(A_71), B_111, C_112), A_71) | ~m1_subset_1(C_112, A_71) | ~m1_subset_1(B_111, A_71) | ~v2_lattice3(k2_yellow_1(A_71)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_46, c_245])).
% 3.79/1.65  tff(c_484, plain, (![B_146, C_147]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_146, C_147), '#skF_2') | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2') | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_478, c_247])).
% 3.79/1.65  tff(c_493, plain, (![B_146, C_147]: (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_146, C_147), '#skF_2') | ~m1_subset_1(C_147, '#skF_2') | ~m1_subset_1(B_146, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_484])).
% 3.79/1.65  tff(c_365, plain, (![A_126, C_127, B_128]: (k11_lattice3(A_126, C_127, B_128)=k11_lattice3(A_126, B_128, C_127) | ~m1_subset_1(C_127, u1_struct_0(A_126)) | ~m1_subset_1(B_128, u1_struct_0(A_126)) | ~l1_orders_2(A_126) | ~v2_lattice3(A_126) | ~v5_orders_2(A_126))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.79/1.65  tff(c_372, plain, (![A_71, C_127, B_128]: (k11_lattice3(k2_yellow_1(A_71), C_127, B_128)=k11_lattice3(k2_yellow_1(A_71), B_128, C_127) | ~m1_subset_1(C_127, A_71) | ~m1_subset_1(B_128, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v2_lattice3(k2_yellow_1(A_71)) | ~v5_orders_2(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_365])).
% 3.79/1.65  tff(c_377, plain, (![A_129, C_130, B_131]: (k11_lattice3(k2_yellow_1(A_129), C_130, B_131)=k11_lattice3(k2_yellow_1(A_129), B_131, C_130) | ~m1_subset_1(C_130, A_129) | ~m1_subset_1(B_131, A_129) | ~v2_lattice3(k2_yellow_1(A_129)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_46, c_372])).
% 3.79/1.65  tff(c_380, plain, (![C_130, B_131]: (k11_lattice3(k2_yellow_1('#skF_2'), C_130, B_131)=k11_lattice3(k2_yellow_1('#skF_2'), B_131, C_130) | ~m1_subset_1(C_130, '#skF_2') | ~m1_subset_1(B_131, '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_377])).
% 3.79/1.65  tff(c_559, plain, (![A_155, B_156, C_157]: (r1_orders_2(A_155, k11_lattice3(A_155, B_156, C_157), B_156) | ~m1_subset_1(k11_lattice3(A_155, B_156, C_157), u1_struct_0(A_155)) | ~m1_subset_1(C_157, u1_struct_0(A_155)) | ~m1_subset_1(B_156, u1_struct_0(A_155)) | ~l1_orders_2(A_155) | ~v2_lattice3(A_155) | ~v5_orders_2(A_155) | v2_struct_0(A_155))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.79/1.65  tff(c_561, plain, (![B_131, C_130]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_131, C_130), B_131) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_130, B_131), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_130, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_131, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_130, '#skF_2') | ~m1_subset_1(B_131, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_380, c_559])).
% 3.79/1.65  tff(c_567, plain, (![B_131, C_130]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_131, C_130), B_131) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_130, B_131), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_130, '#skF_2') | ~m1_subset_1(B_131, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_60, c_32, c_46, c_46, c_46, c_561])).
% 3.79/1.65  tff(c_661, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_567])).
% 3.79/1.65  tff(c_664, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_661, c_44])).
% 3.79/1.65  tff(c_668, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_664])).
% 3.79/1.65  tff(c_670, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_567])).
% 3.79/1.65  tff(c_671, plain, (![B_160, C_161]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_160, C_161), B_160) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_161, B_160), '#skF_2') | ~m1_subset_1(C_161, '#skF_2') | ~m1_subset_1(B_160, '#skF_2'))), inference(splitRight, [status(thm)], [c_567])).
% 3.79/1.65  tff(c_440, plain, (![A_134, B_135, C_136]: (r3_orders_2(A_134, B_135, C_136) | ~r1_orders_2(A_134, B_135, C_136) | ~m1_subset_1(C_136, u1_struct_0(A_134)) | ~m1_subset_1(B_135, u1_struct_0(A_134)) | ~l1_orders_2(A_134) | ~v3_orders_2(A_134) | v2_struct_0(A_134))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.79/1.65  tff(c_447, plain, (![A_71, B_135, C_136]: (r3_orders_2(k2_yellow_1(A_71), B_135, C_136) | ~r1_orders_2(k2_yellow_1(A_71), B_135, C_136) | ~m1_subset_1(C_136, A_71) | ~m1_subset_1(B_135, u1_struct_0(k2_yellow_1(A_71))) | ~l1_orders_2(k2_yellow_1(A_71)) | ~v3_orders_2(k2_yellow_1(A_71)) | v2_struct_0(k2_yellow_1(A_71)))), inference(superposition, [status(thm), theory('equality')], [c_46, c_440])).
% 3.79/1.65  tff(c_464, plain, (![A_140, B_141, C_142]: (r3_orders_2(k2_yellow_1(A_140), B_141, C_142) | ~r1_orders_2(k2_yellow_1(A_140), B_141, C_142) | ~m1_subset_1(C_142, A_140) | ~m1_subset_1(B_141, A_140) | v2_struct_0(k2_yellow_1(A_140)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_46, c_447])).
% 3.79/1.65  tff(c_473, plain, (![B_141, C_142, A_140]: (r1_tarski(B_141, C_142) | v1_xboole_0(A_140) | ~r1_orders_2(k2_yellow_1(A_140), B_141, C_142) | ~m1_subset_1(C_142, A_140) | ~m1_subset_1(B_141, A_140) | v2_struct_0(k2_yellow_1(A_140)))), inference(resolution, [status(thm)], [c_464, c_65])).
% 3.79/1.65  tff(c_674, plain, (![B_160, C_161]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_160, C_161), B_160) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_160, C_161), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_161, B_160), '#skF_2') | ~m1_subset_1(C_161, '#skF_2') | ~m1_subset_1(B_160, '#skF_2'))), inference(resolution, [status(thm)], [c_671, c_473])).
% 3.79/1.65  tff(c_715, plain, (![B_167, C_168]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_167, C_168), B_167) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_167, C_168), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_168, B_167), '#skF_2') | ~m1_subset_1(C_168, '#skF_2') | ~m1_subset_1(B_167, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_670, c_62, c_674])).
% 3.79/1.65  tff(c_120, plain, (![A_95, B_96, C_97]: (r1_tarski(A_95, k3_xboole_0(B_96, C_97)) | ~r1_tarski(A_95, C_97) | ~r1_tarski(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.65  tff(c_54, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 3.79/1.65  tff(c_124, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_120, c_54])).
% 3.79/1.65  tff(c_159, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_124])).
% 3.79/1.65  tff(c_718, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_715, c_159])).
% 3.79/1.65  tff(c_727, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_718])).
% 3.79/1.65  tff(c_728, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_727])).
% 3.79/1.65  tff(c_731, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_493, c_728])).
% 3.79/1.65  tff(c_735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_731])).
% 3.79/1.65  tff(c_736, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_727])).
% 3.79/1.65  tff(c_740, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_493, c_736])).
% 3.79/1.65  tff(c_750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_740])).
% 3.79/1.65  tff(c_751, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_124])).
% 3.79/1.65  tff(c_1392, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1389, c_751])).
% 3.79/1.65  tff(c_1401, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_1392])).
% 3.79/1.65  tff(c_1402, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1401])).
% 3.79/1.65  tff(c_1405, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_1016, c_1402])).
% 3.79/1.65  tff(c_1409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_63, c_1405])).
% 3.79/1.65  tff(c_1410, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_1401])).
% 3.79/1.65  tff(c_1414, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1016, c_1410])).
% 3.79/1.65  tff(c_1424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_64, c_1414])).
% 3.79/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.65  
% 3.79/1.65  Inference rules
% 3.79/1.65  ----------------------
% 3.79/1.65  #Ref     : 0
% 3.79/1.65  #Sup     : 319
% 3.79/1.65  #Fact    : 0
% 3.79/1.65  #Define  : 0
% 3.79/1.65  #Split   : 5
% 3.79/1.65  #Chain   : 0
% 3.79/1.65  #Close   : 0
% 3.79/1.65  
% 3.79/1.65  Ordering : KBO
% 3.79/1.65  
% 3.79/1.65  Simplification rules
% 3.79/1.65  ----------------------
% 3.79/1.65  #Subsume      : 16
% 3.79/1.65  #Demod        : 308
% 3.79/1.65  #Tautology    : 162
% 3.79/1.65  #SimpNegUnit  : 12
% 3.79/1.65  #BackRed      : 0
% 3.79/1.65  
% 3.79/1.65  #Partial instantiations: 0
% 3.79/1.65  #Strategies tried      : 1
% 3.79/1.65  
% 3.79/1.65  Timing (in seconds)
% 3.79/1.65  ----------------------
% 3.79/1.65  Preprocessing        : 0.35
% 3.79/1.65  Parsing              : 0.18
% 3.79/1.65  CNF conversion       : 0.03
% 3.79/1.65  Main loop            : 0.52
% 3.79/1.65  Inferencing          : 0.19
% 3.79/1.65  Reduction            : 0.18
% 3.79/1.65  Demodulation         : 0.14
% 3.79/1.65  BG Simplification    : 0.03
% 3.79/1.65  Subsumption          : 0.08
% 3.79/1.65  Abstraction          : 0.04
% 3.79/1.65  MUC search           : 0.00
% 3.79/1.65  Cooper               : 0.00
% 3.79/1.65  Total                : 0.91
% 3.79/1.65  Index Insertion      : 0.00
% 3.79/1.65  Index Deletion       : 0.00
% 3.79/1.65  Index Matching       : 0.00
% 3.79/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
