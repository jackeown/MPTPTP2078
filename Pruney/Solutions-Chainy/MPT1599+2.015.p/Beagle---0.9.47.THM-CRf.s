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

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.50s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 402 expanded)
%              Number of leaves         :   38 ( 170 expanded)
%              Depth                    :   14
%              Number of atoms          :  316 (1186 expanded)
%              Number of equality atoms :   13 ( 192 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_127,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_154,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_115,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_103,axiom,(
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

tff(f_89,axiom,(
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

tff(f_123,axiom,(
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

tff(f_140,axiom,(
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

tff(c_44,plain,(
    ! [A_68] : u1_struct_0(k2_yellow_1(A_68)) = A_68 ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_61,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_62,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_54])).

tff(c_30,plain,(
    ! [A_65] : l1_orders_2(k2_yellow_1(A_65)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_353,plain,(
    ! [A_144,B_145,C_146] :
      ( m1_subset_1(k11_lattice3(A_144,B_145,C_146),u1_struct_0(A_144))
      | ~ m1_subset_1(C_146,u1_struct_0(A_144))
      | ~ m1_subset_1(B_145,u1_struct_0(A_144))
      | ~ l1_orders_2(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_356,plain,(
    ! [A_68,B_145,C_146] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_68),B_145,C_146),A_68)
      | ~ m1_subset_1(C_146,u1_struct_0(k2_yellow_1(A_68)))
      | ~ m1_subset_1(B_145,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_353])).

tff(c_358,plain,(
    ! [A_68,B_145,C_146] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_68),B_145,C_146),A_68)
      | ~ m1_subset_1(C_146,A_68)
      | ~ m1_subset_1(B_145,A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44,c_44,c_356])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_38,plain,(
    ! [A_66] : v5_orders_2(k2_yellow_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_58,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_366,plain,(
    ! [A_153,C_154,B_155] :
      ( k11_lattice3(A_153,C_154,B_155) = k11_lattice3(A_153,B_155,C_154)
      | ~ m1_subset_1(C_154,u1_struct_0(A_153))
      | ~ m1_subset_1(B_155,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v2_lattice3(A_153)
      | ~ v5_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_373,plain,(
    ! [A_68,C_154,B_155] :
      ( k11_lattice3(k2_yellow_1(A_68),C_154,B_155) = k11_lattice3(k2_yellow_1(A_68),B_155,C_154)
      | ~ m1_subset_1(C_154,A_68)
      | ~ m1_subset_1(B_155,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68))
      | ~ v2_lattice3(k2_yellow_1(A_68))
      | ~ v5_orders_2(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_366])).

tff(c_379,plain,(
    ! [A_159,C_160,B_161] :
      ( k11_lattice3(k2_yellow_1(A_159),C_160,B_161) = k11_lattice3(k2_yellow_1(A_159),B_161,C_160)
      | ~ m1_subset_1(C_160,A_159)
      | ~ m1_subset_1(B_161,A_159)
      | ~ v2_lattice3(k2_yellow_1(A_159)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_373])).

tff(c_382,plain,(
    ! [C_160,B_161] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_160,B_161) = k11_lattice3(k2_yellow_1('#skF_2'),B_161,C_160)
      | ~ m1_subset_1(C_160,'#skF_2')
      | ~ m1_subset_1(B_161,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_379])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] :
      ( m1_subset_1(k11_lattice3(A_9,B_10,C_11),u1_struct_0(A_9))
      | ~ m1_subset_1(C_11,u1_struct_0(A_9))
      | ~ m1_subset_1(B_10,u1_struct_0(A_9))
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_496,plain,(
    ! [A_173,B_174,C_175] :
      ( r1_orders_2(A_173,k11_lattice3(A_173,B_174,C_175),B_174)
      | ~ m1_subset_1(k11_lattice3(A_173,B_174,C_175),u1_struct_0(A_173))
      | ~ m1_subset_1(C_175,u1_struct_0(A_173))
      | ~ m1_subset_1(B_174,u1_struct_0(A_173))
      | ~ l1_orders_2(A_173)
      | ~ v2_lattice3(A_173)
      | ~ v5_orders_2(A_173)
      | v2_struct_0(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_512,plain,(
    ! [A_176,B_177,C_178] :
      ( r1_orders_2(A_176,k11_lattice3(A_176,B_177,C_178),B_177)
      | ~ v2_lattice3(A_176)
      | ~ v5_orders_2(A_176)
      | v2_struct_0(A_176)
      | ~ m1_subset_1(C_178,u1_struct_0(A_176))
      | ~ m1_subset_1(B_177,u1_struct_0(A_176))
      | ~ l1_orders_2(A_176) ) ),
    inference(resolution,[status(thm)],[c_10,c_496])).

tff(c_519,plain,(
    ! [C_160,B_161] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_160,B_161),B_161)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_160,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_161,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_160,'#skF_2')
      | ~ m1_subset_1(B_161,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_512])).

tff(c_527,plain,(
    ! [C_160,B_161] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_160,B_161),B_161)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_160,'#skF_2')
      | ~ m1_subset_1(B_161,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44,c_44,c_38,c_58,c_519])).

tff(c_530,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_42,plain,(
    ! [A_67] :
      ( ~ v2_struct_0(k2_yellow_1(A_67))
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_549,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_530,c_42])).

tff(c_553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_549])).

tff(c_555,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_556,plain,(
    ! [C_182,B_183] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_182,B_183),B_183)
      | ~ m1_subset_1(C_182,'#skF_2')
      | ~ m1_subset_1(B_183,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_34,plain,(
    ! [A_66] : v3_orders_2(k2_yellow_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_463,plain,(
    ! [A_164,B_165,C_166] :
      ( r3_orders_2(A_164,B_165,C_166)
      | ~ r1_orders_2(A_164,B_165,C_166)
      | ~ m1_subset_1(C_166,u1_struct_0(A_164))
      | ~ m1_subset_1(B_165,u1_struct_0(A_164))
      | ~ l1_orders_2(A_164)
      | ~ v3_orders_2(A_164)
      | v2_struct_0(A_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_470,plain,(
    ! [A_68,B_165,C_166] :
      ( r3_orders_2(k2_yellow_1(A_68),B_165,C_166)
      | ~ r1_orders_2(k2_yellow_1(A_68),B_165,C_166)
      | ~ m1_subset_1(C_166,A_68)
      | ~ m1_subset_1(B_165,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68))
      | ~ v3_orders_2(k2_yellow_1(A_68))
      | v2_struct_0(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_463])).

tff(c_481,plain,(
    ! [A_167,B_168,C_169] :
      ( r3_orders_2(k2_yellow_1(A_167),B_168,C_169)
      | ~ r1_orders_2(k2_yellow_1(A_167),B_168,C_169)
      | ~ m1_subset_1(C_169,A_167)
      | ~ m1_subset_1(B_168,A_167)
      | v2_struct_0(k2_yellow_1(A_167)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_470])).

tff(c_50,plain,(
    ! [B_73,C_75,A_69] :
      ( r1_tarski(B_73,C_75)
      | ~ r3_orders_2(k2_yellow_1(A_69),B_73,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(k2_yellow_1(A_69)))
      | ~ m1_subset_1(B_73,u1_struct_0(k2_yellow_1(A_69)))
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_63,plain,(
    ! [B_73,C_75,A_69] :
      ( r1_tarski(B_73,C_75)
      | ~ r3_orders_2(k2_yellow_1(A_69),B_73,C_75)
      | ~ m1_subset_1(C_75,A_69)
      | ~ m1_subset_1(B_73,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_44,c_50])).

tff(c_490,plain,(
    ! [B_168,C_169,A_167] :
      ( r1_tarski(B_168,C_169)
      | v1_xboole_0(A_167)
      | ~ r1_orders_2(k2_yellow_1(A_167),B_168,C_169)
      | ~ m1_subset_1(C_169,A_167)
      | ~ m1_subset_1(B_168,A_167)
      | v2_struct_0(k2_yellow_1(A_167)) ) ),
    inference(resolution,[status(thm)],[c_481,c_63])).

tff(c_559,plain,(
    ! [C_182,B_183] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_182,B_183),B_183)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_182,B_183),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_182,'#skF_2')
      | ~ m1_subset_1(B_183,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_556,c_490])).

tff(c_569,plain,(
    ! [C_184,B_185] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_184,B_185),B_185)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_184,B_185),'#skF_2')
      | ~ m1_subset_1(C_184,'#skF_2')
      | ~ m1_subset_1(B_185,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_60,c_559])).

tff(c_112,plain,(
    ! [A_99,B_100,C_101] :
      ( m1_subset_1(k11_lattice3(A_99,B_100,C_101),u1_struct_0(A_99))
      | ~ m1_subset_1(C_101,u1_struct_0(A_99))
      | ~ m1_subset_1(B_100,u1_struct_0(A_99))
      | ~ l1_orders_2(A_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    ! [A_68,B_100,C_101] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_68),B_100,C_101),A_68)
      | ~ m1_subset_1(C_101,u1_struct_0(k2_yellow_1(A_68)))
      | ~ m1_subset_1(B_100,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_112])).

tff(c_117,plain,(
    ! [A_68,B_100,C_101] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_68),B_100,C_101),A_68)
      | ~ m1_subset_1(C_101,A_68)
      | ~ m1_subset_1(B_100,A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44,c_44,c_115])).

tff(c_119,plain,(
    ! [A_105,C_106,B_107] :
      ( k11_lattice3(A_105,C_106,B_107) = k11_lattice3(A_105,B_107,C_106)
      | ~ m1_subset_1(C_106,u1_struct_0(A_105))
      | ~ m1_subset_1(B_107,u1_struct_0(A_105))
      | ~ l1_orders_2(A_105)
      | ~ v2_lattice3(A_105)
      | ~ v5_orders_2(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_126,plain,(
    ! [A_68,C_106,B_107] :
      ( k11_lattice3(k2_yellow_1(A_68),C_106,B_107) = k11_lattice3(k2_yellow_1(A_68),B_107,C_106)
      | ~ m1_subset_1(C_106,A_68)
      | ~ m1_subset_1(B_107,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68))
      | ~ v2_lattice3(k2_yellow_1(A_68))
      | ~ v5_orders_2(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_119])).

tff(c_131,plain,(
    ! [A_108,C_109,B_110] :
      ( k11_lattice3(k2_yellow_1(A_108),C_109,B_110) = k11_lattice3(k2_yellow_1(A_108),B_110,C_109)
      | ~ m1_subset_1(C_109,A_108)
      | ~ m1_subset_1(B_110,A_108)
      | ~ v2_lattice3(k2_yellow_1(A_108)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_30,c_44,c_126])).

tff(c_134,plain,(
    ! [C_109,B_110] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_109,B_110) = k11_lattice3(k2_yellow_1('#skF_2'),B_110,C_109)
      | ~ m1_subset_1(C_109,'#skF_2')
      | ~ m1_subset_1(B_110,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_242,plain,(
    ! [A_128,B_129,C_130] :
      ( r1_orders_2(A_128,k11_lattice3(A_128,B_129,C_130),C_130)
      | ~ m1_subset_1(k11_lattice3(A_128,B_129,C_130),u1_struct_0(A_128))
      | ~ m1_subset_1(C_130,u1_struct_0(A_128))
      | ~ m1_subset_1(B_129,u1_struct_0(A_128))
      | ~ l1_orders_2(A_128)
      | ~ v2_lattice3(A_128)
      | ~ v5_orders_2(A_128)
      | v2_struct_0(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_258,plain,(
    ! [A_131,B_132,C_133] :
      ( r1_orders_2(A_131,k11_lattice3(A_131,B_132,C_133),C_133)
      | ~ v2_lattice3(A_131)
      | ~ v5_orders_2(A_131)
      | v2_struct_0(A_131)
      | ~ m1_subset_1(C_133,u1_struct_0(A_131))
      | ~ m1_subset_1(B_132,u1_struct_0(A_131))
      | ~ l1_orders_2(A_131) ) ),
    inference(resolution,[status(thm)],[c_10,c_242])).

tff(c_265,plain,(
    ! [C_109,B_110] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_109,B_110),C_109)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_109,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_110,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_109,'#skF_2')
      | ~ m1_subset_1(B_110,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_258])).

tff(c_273,plain,(
    ! [C_109,B_110] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_109,B_110),C_109)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_109,'#skF_2')
      | ~ m1_subset_1(B_110,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44,c_44,c_38,c_58,c_265])).

tff(c_292,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_273])).

tff(c_295,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_292,c_42])).

tff(c_299,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_295])).

tff(c_301,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_273])).

tff(c_268,plain,(
    ! [B_110,C_109] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_110,C_109),B_110)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(B_110,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_109,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_109,'#skF_2')
      | ~ m1_subset_1(B_110,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_258])).

tff(c_275,plain,(
    ! [B_110,C_109] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_110,C_109),B_110)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_109,'#skF_2')
      | ~ m1_subset_1(B_110,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_44,c_44,c_38,c_58,c_268])).

tff(c_303,plain,(
    ! [B_137,C_138] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_138),B_137)
      | ~ m1_subset_1(C_138,'#skF_2')
      | ~ m1_subset_1(B_137,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_275])).

tff(c_204,plain,(
    ! [A_113,B_114,C_115] :
      ( r3_orders_2(A_113,B_114,C_115)
      | ~ r1_orders_2(A_113,B_114,C_115)
      | ~ m1_subset_1(C_115,u1_struct_0(A_113))
      | ~ m1_subset_1(B_114,u1_struct_0(A_113))
      | ~ l1_orders_2(A_113)
      | ~ v3_orders_2(A_113)
      | v2_struct_0(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_211,plain,(
    ! [A_68,B_114,C_115] :
      ( r3_orders_2(k2_yellow_1(A_68),B_114,C_115)
      | ~ r1_orders_2(k2_yellow_1(A_68),B_114,C_115)
      | ~ m1_subset_1(C_115,A_68)
      | ~ m1_subset_1(B_114,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68))
      | ~ v3_orders_2(k2_yellow_1(A_68))
      | v2_struct_0(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_204])).

tff(c_226,plain,(
    ! [A_119,B_120,C_121] :
      ( r3_orders_2(k2_yellow_1(A_119),B_120,C_121)
      | ~ r1_orders_2(k2_yellow_1(A_119),B_120,C_121)
      | ~ m1_subset_1(C_121,A_119)
      | ~ m1_subset_1(B_120,A_119)
      | v2_struct_0(k2_yellow_1(A_119)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_44,c_211])).

tff(c_235,plain,(
    ! [B_120,C_121,A_119] :
      ( r1_tarski(B_120,C_121)
      | v1_xboole_0(A_119)
      | ~ r1_orders_2(k2_yellow_1(A_119),B_120,C_121)
      | ~ m1_subset_1(C_121,A_119)
      | ~ m1_subset_1(B_120,A_119)
      | v2_struct_0(k2_yellow_1(A_119)) ) ),
    inference(resolution,[status(thm)],[c_226,c_63])).

tff(c_306,plain,(
    ! [B_137,C_138] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_138),B_137)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_138),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_138,'#skF_2')
      | ~ m1_subset_1(B_137,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_303,c_235])).

tff(c_316,plain,(
    ! [B_139,C_140] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_139,C_140),B_139)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_139,C_140),'#skF_2')
      | ~ m1_subset_1(C_140,'#skF_2')
      | ~ m1_subset_1(B_139,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_301,c_60,c_306])).

tff(c_100,plain,(
    ! [A_90,B_91,C_92] :
      ( r1_tarski(A_90,k3_xboole_0(B_91,C_92))
      | ~ r1_tarski(A_90,C_92)
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_104,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_100,c_52])).

tff(c_106,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_104])).

tff(c_319,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_316,c_106])).

tff(c_328,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_319])).

tff(c_337,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_117,c_328])).

tff(c_345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_337])).

tff(c_346,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_104])).

tff(c_572,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_569,c_346])).

tff(c_581,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_61,c_572])).

tff(c_590,plain,
    ( ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_358,c_581])).

tff(c_598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_62,c_590])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:31:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.97  
% 4.16/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.16/1.98  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k3_xboole_0 > k2_tarski > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.16/1.98  
% 4.16/1.98  %Foreground sorts:
% 4.16/1.98  
% 4.16/1.98  
% 4.16/1.98  %Background operators:
% 4.16/1.98  
% 4.16/1.98  
% 4.16/1.98  %Foreground operators:
% 4.16/1.98  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 4.16/1.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.16/1.98  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 4.16/1.98  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 4.16/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.98  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 4.16/1.98  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 4.16/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.98  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 4.16/1.98  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.16/1.98  tff('#skF_2', type, '#skF_2': $i).
% 4.16/1.98  tff('#skF_3', type, '#skF_3': $i).
% 4.16/1.98  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 4.16/1.98  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 4.16/1.98  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 4.16/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.98  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.98  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 4.16/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.98  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.16/1.98  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 4.16/1.98  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 4.16/1.98  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.16/1.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.16/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.16/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.16/1.98  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.16/1.98  
% 4.50/2.01  tff(f_127, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 4.50/2.01  tff(f_154, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 4.50/2.01  tff(f_107, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 4.50/2.01  tff(f_56, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 4.50/2.01  tff(f_115, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 4.50/2.01  tff(f_103, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 4.50/2.01  tff(f_89, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 4.50/2.01  tff(f_123, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 4.50/2.01  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 4.50/2.01  tff(f_140, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 4.50/2.01  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.50/2.01  tff(c_44, plain, (![A_68]: (u1_struct_0(k2_yellow_1(A_68))=A_68)), inference(cnfTransformation, [status(thm)], [f_127])).
% 4.50/2.01  tff(c_56, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.50/2.01  tff(c_61, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 4.50/2.01  tff(c_54, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.50/2.01  tff(c_62, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_54])).
% 4.50/2.01  tff(c_30, plain, (![A_65]: (l1_orders_2(k2_yellow_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.50/2.01  tff(c_353, plain, (![A_144, B_145, C_146]: (m1_subset_1(k11_lattice3(A_144, B_145, C_146), u1_struct_0(A_144)) | ~m1_subset_1(C_146, u1_struct_0(A_144)) | ~m1_subset_1(B_145, u1_struct_0(A_144)) | ~l1_orders_2(A_144))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/2.01  tff(c_356, plain, (![A_68, B_145, C_146]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_68), B_145, C_146), A_68) | ~m1_subset_1(C_146, u1_struct_0(k2_yellow_1(A_68))) | ~m1_subset_1(B_145, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_353])).
% 4.50/2.01  tff(c_358, plain, (![A_68, B_145, C_146]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_68), B_145, C_146), A_68) | ~m1_subset_1(C_146, A_68) | ~m1_subset_1(B_145, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44, c_44, c_356])).
% 4.50/2.01  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.50/2.01  tff(c_38, plain, (![A_66]: (v5_orders_2(k2_yellow_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.50/2.01  tff(c_58, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.50/2.01  tff(c_366, plain, (![A_153, C_154, B_155]: (k11_lattice3(A_153, C_154, B_155)=k11_lattice3(A_153, B_155, C_154) | ~m1_subset_1(C_154, u1_struct_0(A_153)) | ~m1_subset_1(B_155, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v2_lattice3(A_153) | ~v5_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.50/2.01  tff(c_373, plain, (![A_68, C_154, B_155]: (k11_lattice3(k2_yellow_1(A_68), C_154, B_155)=k11_lattice3(k2_yellow_1(A_68), B_155, C_154) | ~m1_subset_1(C_154, A_68) | ~m1_subset_1(B_155, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)) | ~v2_lattice3(k2_yellow_1(A_68)) | ~v5_orders_2(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_366])).
% 4.50/2.01  tff(c_379, plain, (![A_159, C_160, B_161]: (k11_lattice3(k2_yellow_1(A_159), C_160, B_161)=k11_lattice3(k2_yellow_1(A_159), B_161, C_160) | ~m1_subset_1(C_160, A_159) | ~m1_subset_1(B_161, A_159) | ~v2_lattice3(k2_yellow_1(A_159)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_373])).
% 4.50/2.01  tff(c_382, plain, (![C_160, B_161]: (k11_lattice3(k2_yellow_1('#skF_2'), C_160, B_161)=k11_lattice3(k2_yellow_1('#skF_2'), B_161, C_160) | ~m1_subset_1(C_160, '#skF_2') | ~m1_subset_1(B_161, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_379])).
% 4.50/2.01  tff(c_10, plain, (![A_9, B_10, C_11]: (m1_subset_1(k11_lattice3(A_9, B_10, C_11), u1_struct_0(A_9)) | ~m1_subset_1(C_11, u1_struct_0(A_9)) | ~m1_subset_1(B_10, u1_struct_0(A_9)) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/2.01  tff(c_496, plain, (![A_173, B_174, C_175]: (r1_orders_2(A_173, k11_lattice3(A_173, B_174, C_175), B_174) | ~m1_subset_1(k11_lattice3(A_173, B_174, C_175), u1_struct_0(A_173)) | ~m1_subset_1(C_175, u1_struct_0(A_173)) | ~m1_subset_1(B_174, u1_struct_0(A_173)) | ~l1_orders_2(A_173) | ~v2_lattice3(A_173) | ~v5_orders_2(A_173) | v2_struct_0(A_173))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.50/2.01  tff(c_512, plain, (![A_176, B_177, C_178]: (r1_orders_2(A_176, k11_lattice3(A_176, B_177, C_178), B_177) | ~v2_lattice3(A_176) | ~v5_orders_2(A_176) | v2_struct_0(A_176) | ~m1_subset_1(C_178, u1_struct_0(A_176)) | ~m1_subset_1(B_177, u1_struct_0(A_176)) | ~l1_orders_2(A_176))), inference(resolution, [status(thm)], [c_10, c_496])).
% 4.50/2.01  tff(c_519, plain, (![C_160, B_161]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_160, B_161), B_161) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_160, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_161, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_160, '#skF_2') | ~m1_subset_1(B_161, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_512])).
% 4.50/2.01  tff(c_527, plain, (![C_160, B_161]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_160, B_161), B_161) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_160, '#skF_2') | ~m1_subset_1(B_161, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44, c_44, c_38, c_58, c_519])).
% 4.50/2.01  tff(c_530, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_527])).
% 4.50/2.01  tff(c_42, plain, (![A_67]: (~v2_struct_0(k2_yellow_1(A_67)) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.50/2.01  tff(c_549, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_530, c_42])).
% 4.50/2.01  tff(c_553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_549])).
% 4.50/2.01  tff(c_555, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_527])).
% 4.50/2.01  tff(c_556, plain, (![C_182, B_183]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_182, B_183), B_183) | ~m1_subset_1(C_182, '#skF_2') | ~m1_subset_1(B_183, '#skF_2'))), inference(splitRight, [status(thm)], [c_527])).
% 4.50/2.01  tff(c_34, plain, (![A_66]: (v3_orders_2(k2_yellow_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.50/2.01  tff(c_463, plain, (![A_164, B_165, C_166]: (r3_orders_2(A_164, B_165, C_166) | ~r1_orders_2(A_164, B_165, C_166) | ~m1_subset_1(C_166, u1_struct_0(A_164)) | ~m1_subset_1(B_165, u1_struct_0(A_164)) | ~l1_orders_2(A_164) | ~v3_orders_2(A_164) | v2_struct_0(A_164))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.50/2.01  tff(c_470, plain, (![A_68, B_165, C_166]: (r3_orders_2(k2_yellow_1(A_68), B_165, C_166) | ~r1_orders_2(k2_yellow_1(A_68), B_165, C_166) | ~m1_subset_1(C_166, A_68) | ~m1_subset_1(B_165, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)) | ~v3_orders_2(k2_yellow_1(A_68)) | v2_struct_0(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_463])).
% 4.50/2.01  tff(c_481, plain, (![A_167, B_168, C_169]: (r3_orders_2(k2_yellow_1(A_167), B_168, C_169) | ~r1_orders_2(k2_yellow_1(A_167), B_168, C_169) | ~m1_subset_1(C_169, A_167) | ~m1_subset_1(B_168, A_167) | v2_struct_0(k2_yellow_1(A_167)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_470])).
% 4.50/2.01  tff(c_50, plain, (![B_73, C_75, A_69]: (r1_tarski(B_73, C_75) | ~r3_orders_2(k2_yellow_1(A_69), B_73, C_75) | ~m1_subset_1(C_75, u1_struct_0(k2_yellow_1(A_69))) | ~m1_subset_1(B_73, u1_struct_0(k2_yellow_1(A_69))) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_140])).
% 4.50/2.01  tff(c_63, plain, (![B_73, C_75, A_69]: (r1_tarski(B_73, C_75) | ~r3_orders_2(k2_yellow_1(A_69), B_73, C_75) | ~m1_subset_1(C_75, A_69) | ~m1_subset_1(B_73, A_69) | v1_xboole_0(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_44, c_50])).
% 4.50/2.01  tff(c_490, plain, (![B_168, C_169, A_167]: (r1_tarski(B_168, C_169) | v1_xboole_0(A_167) | ~r1_orders_2(k2_yellow_1(A_167), B_168, C_169) | ~m1_subset_1(C_169, A_167) | ~m1_subset_1(B_168, A_167) | v2_struct_0(k2_yellow_1(A_167)))), inference(resolution, [status(thm)], [c_481, c_63])).
% 4.50/2.01  tff(c_559, plain, (![C_182, B_183]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_182, B_183), B_183) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_182, B_183), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_182, '#skF_2') | ~m1_subset_1(B_183, '#skF_2'))), inference(resolution, [status(thm)], [c_556, c_490])).
% 4.50/2.01  tff(c_569, plain, (![C_184, B_185]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_184, B_185), B_185) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_184, B_185), '#skF_2') | ~m1_subset_1(C_184, '#skF_2') | ~m1_subset_1(B_185, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_555, c_60, c_559])).
% 4.50/2.01  tff(c_112, plain, (![A_99, B_100, C_101]: (m1_subset_1(k11_lattice3(A_99, B_100, C_101), u1_struct_0(A_99)) | ~m1_subset_1(C_101, u1_struct_0(A_99)) | ~m1_subset_1(B_100, u1_struct_0(A_99)) | ~l1_orders_2(A_99))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.50/2.01  tff(c_115, plain, (![A_68, B_100, C_101]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_68), B_100, C_101), A_68) | ~m1_subset_1(C_101, u1_struct_0(k2_yellow_1(A_68))) | ~m1_subset_1(B_100, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_112])).
% 4.50/2.01  tff(c_117, plain, (![A_68, B_100, C_101]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_68), B_100, C_101), A_68) | ~m1_subset_1(C_101, A_68) | ~m1_subset_1(B_100, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44, c_44, c_115])).
% 4.50/2.01  tff(c_119, plain, (![A_105, C_106, B_107]: (k11_lattice3(A_105, C_106, B_107)=k11_lattice3(A_105, B_107, C_106) | ~m1_subset_1(C_106, u1_struct_0(A_105)) | ~m1_subset_1(B_107, u1_struct_0(A_105)) | ~l1_orders_2(A_105) | ~v2_lattice3(A_105) | ~v5_orders_2(A_105))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.50/2.01  tff(c_126, plain, (![A_68, C_106, B_107]: (k11_lattice3(k2_yellow_1(A_68), C_106, B_107)=k11_lattice3(k2_yellow_1(A_68), B_107, C_106) | ~m1_subset_1(C_106, A_68) | ~m1_subset_1(B_107, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)) | ~v2_lattice3(k2_yellow_1(A_68)) | ~v5_orders_2(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_119])).
% 4.50/2.01  tff(c_131, plain, (![A_108, C_109, B_110]: (k11_lattice3(k2_yellow_1(A_108), C_109, B_110)=k11_lattice3(k2_yellow_1(A_108), B_110, C_109) | ~m1_subset_1(C_109, A_108) | ~m1_subset_1(B_110, A_108) | ~v2_lattice3(k2_yellow_1(A_108)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_30, c_44, c_126])).
% 4.50/2.01  tff(c_134, plain, (![C_109, B_110]: (k11_lattice3(k2_yellow_1('#skF_2'), C_109, B_110)=k11_lattice3(k2_yellow_1('#skF_2'), B_110, C_109) | ~m1_subset_1(C_109, '#skF_2') | ~m1_subset_1(B_110, '#skF_2'))), inference(resolution, [status(thm)], [c_58, c_131])).
% 4.50/2.01  tff(c_242, plain, (![A_128, B_129, C_130]: (r1_orders_2(A_128, k11_lattice3(A_128, B_129, C_130), C_130) | ~m1_subset_1(k11_lattice3(A_128, B_129, C_130), u1_struct_0(A_128)) | ~m1_subset_1(C_130, u1_struct_0(A_128)) | ~m1_subset_1(B_129, u1_struct_0(A_128)) | ~l1_orders_2(A_128) | ~v2_lattice3(A_128) | ~v5_orders_2(A_128) | v2_struct_0(A_128))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.50/2.01  tff(c_258, plain, (![A_131, B_132, C_133]: (r1_orders_2(A_131, k11_lattice3(A_131, B_132, C_133), C_133) | ~v2_lattice3(A_131) | ~v5_orders_2(A_131) | v2_struct_0(A_131) | ~m1_subset_1(C_133, u1_struct_0(A_131)) | ~m1_subset_1(B_132, u1_struct_0(A_131)) | ~l1_orders_2(A_131))), inference(resolution, [status(thm)], [c_10, c_242])).
% 4.50/2.01  tff(c_265, plain, (![C_109, B_110]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_109, B_110), C_109) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_109, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_110, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_109, '#skF_2') | ~m1_subset_1(B_110, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_258])).
% 4.50/2.01  tff(c_273, plain, (![C_109, B_110]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_109, B_110), C_109) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_109, '#skF_2') | ~m1_subset_1(B_110, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44, c_44, c_38, c_58, c_265])).
% 4.50/2.01  tff(c_292, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_273])).
% 4.50/2.01  tff(c_295, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_292, c_42])).
% 4.50/2.01  tff(c_299, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_295])).
% 4.50/2.01  tff(c_301, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_273])).
% 4.50/2.01  tff(c_268, plain, (![B_110, C_109]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_110, C_109), B_110) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(B_110, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_109, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_109, '#skF_2') | ~m1_subset_1(B_110, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_258])).
% 4.50/2.01  tff(c_275, plain, (![B_110, C_109]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_110, C_109), B_110) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_109, '#skF_2') | ~m1_subset_1(B_110, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_44, c_44, c_38, c_58, c_268])).
% 4.50/2.01  tff(c_303, plain, (![B_137, C_138]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_138), B_137) | ~m1_subset_1(C_138, '#skF_2') | ~m1_subset_1(B_137, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_301, c_275])).
% 4.50/2.01  tff(c_204, plain, (![A_113, B_114, C_115]: (r3_orders_2(A_113, B_114, C_115) | ~r1_orders_2(A_113, B_114, C_115) | ~m1_subset_1(C_115, u1_struct_0(A_113)) | ~m1_subset_1(B_114, u1_struct_0(A_113)) | ~l1_orders_2(A_113) | ~v3_orders_2(A_113) | v2_struct_0(A_113))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.50/2.01  tff(c_211, plain, (![A_68, B_114, C_115]: (r3_orders_2(k2_yellow_1(A_68), B_114, C_115) | ~r1_orders_2(k2_yellow_1(A_68), B_114, C_115) | ~m1_subset_1(C_115, A_68) | ~m1_subset_1(B_114, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)) | ~v3_orders_2(k2_yellow_1(A_68)) | v2_struct_0(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_204])).
% 4.50/2.01  tff(c_226, plain, (![A_119, B_120, C_121]: (r3_orders_2(k2_yellow_1(A_119), B_120, C_121) | ~r1_orders_2(k2_yellow_1(A_119), B_120, C_121) | ~m1_subset_1(C_121, A_119) | ~m1_subset_1(B_120, A_119) | v2_struct_0(k2_yellow_1(A_119)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_44, c_211])).
% 4.50/2.01  tff(c_235, plain, (![B_120, C_121, A_119]: (r1_tarski(B_120, C_121) | v1_xboole_0(A_119) | ~r1_orders_2(k2_yellow_1(A_119), B_120, C_121) | ~m1_subset_1(C_121, A_119) | ~m1_subset_1(B_120, A_119) | v2_struct_0(k2_yellow_1(A_119)))), inference(resolution, [status(thm)], [c_226, c_63])).
% 4.50/2.01  tff(c_306, plain, (![B_137, C_138]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_138), B_137) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_138), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_138, '#skF_2') | ~m1_subset_1(B_137, '#skF_2'))), inference(resolution, [status(thm)], [c_303, c_235])).
% 4.50/2.01  tff(c_316, plain, (![B_139, C_140]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_139, C_140), B_139) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_139, C_140), '#skF_2') | ~m1_subset_1(C_140, '#skF_2') | ~m1_subset_1(B_139, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_301, c_60, c_306])).
% 4.50/2.01  tff(c_100, plain, (![A_90, B_91, C_92]: (r1_tarski(A_90, k3_xboole_0(B_91, C_92)) | ~r1_tarski(A_90, C_92) | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.50/2.01  tff(c_52, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_154])).
% 4.50/2.01  tff(c_104, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_100, c_52])).
% 4.50/2.01  tff(c_106, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_104])).
% 4.50/2.01  tff(c_319, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_316, c_106])).
% 4.50/2.01  tff(c_328, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_319])).
% 4.50/2.01  tff(c_337, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_117, c_328])).
% 4.50/2.01  tff(c_345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_337])).
% 4.50/2.01  tff(c_346, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_104])).
% 4.50/2.01  tff(c_572, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_569, c_346])).
% 4.50/2.01  tff(c_581, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_61, c_572])).
% 4.50/2.01  tff(c_590, plain, (~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_358, c_581])).
% 4.50/2.01  tff(c_598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_61, c_62, c_590])).
% 4.50/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.50/2.01  
% 4.50/2.01  Inference rules
% 4.50/2.01  ----------------------
% 4.50/2.01  #Ref     : 0
% 4.50/2.02  #Sup     : 111
% 4.50/2.02  #Fact    : 0
% 4.50/2.02  #Define  : 0
% 4.50/2.02  #Split   : 3
% 4.50/2.02  #Chain   : 0
% 4.50/2.02  #Close   : 0
% 4.50/2.02  
% 4.50/2.02  Ordering : KBO
% 4.50/2.02  
% 4.50/2.02  Simplification rules
% 4.50/2.02  ----------------------
% 4.50/2.02  #Subsume      : 17
% 4.50/2.02  #Demod        : 188
% 4.50/2.02  #Tautology    : 31
% 4.50/2.02  #SimpNegUnit  : 5
% 4.50/2.02  #BackRed      : 0
% 4.50/2.02  
% 4.50/2.02  #Partial instantiations: 0
% 4.50/2.02  #Strategies tried      : 1
% 4.50/2.02  
% 4.50/2.02  Timing (in seconds)
% 4.50/2.02  ----------------------
% 4.50/2.02  Preprocessing        : 0.56
% 4.50/2.02  Parsing              : 0.30
% 4.50/2.02  CNF conversion       : 0.05
% 4.50/2.02  Main loop            : 0.58
% 4.50/2.02  Inferencing          : 0.21
% 4.50/2.02  Reduction            : 0.18
% 4.50/2.02  Demodulation         : 0.14
% 4.50/2.02  BG Simplification    : 0.04
% 4.50/2.02  Subsumption          : 0.11
% 4.50/2.02  Abstraction          : 0.03
% 4.50/2.02  MUC search           : 0.00
% 4.50/2.02  Cooper               : 0.00
% 4.50/2.02  Total                : 1.22
% 4.50/2.02  Index Insertion      : 0.00
% 4.50/2.02  Index Deletion       : 0.00
% 4.50/2.02  Index Matching       : 0.00
% 4.50/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
