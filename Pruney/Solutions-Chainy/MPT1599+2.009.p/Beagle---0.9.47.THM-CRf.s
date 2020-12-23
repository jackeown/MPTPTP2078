%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:23 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 764 expanded)
%              Number of leaves         :   37 ( 312 expanded)
%              Depth                    :   15
%              Number of atoms          :  358 (2282 expanded)
%              Number of equality atoms :   14 ( 427 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_110,axiom,(
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

tff(f_96,axiom,(
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

tff(f_55,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ( v2_lattice3(A)
       => ~ v2_struct_0(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_lattice3)).

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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_42,plain,(
    ! [A_68] : u1_struct_0(k2_yellow_1(A_68)) = A_68 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_60,plain,(
    m1_subset_1('#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_52])).

tff(c_54,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_59,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_54])).

tff(c_32,plain,(
    ! [A_66] : l1_orders_2(k2_yellow_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_662,plain,(
    ! [A_159,B_160,C_161] :
      ( m1_subset_1(k11_lattice3(A_159,B_160,C_161),u1_struct_0(A_159))
      | ~ m1_subset_1(C_161,u1_struct_0(A_159))
      | ~ m1_subset_1(B_160,u1_struct_0(A_159))
      | ~ l1_orders_2(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_665,plain,(
    ! [A_68,B_160,C_161] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_68),B_160,C_161),A_68)
      | ~ m1_subset_1(C_161,u1_struct_0(k2_yellow_1(A_68)))
      | ~ m1_subset_1(B_160,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_662])).

tff(c_667,plain,(
    ! [A_68,B_160,C_161] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_68),B_160,C_161),A_68)
      | ~ m1_subset_1(C_161,A_68)
      | ~ m1_subset_1(B_160,A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42,c_42,c_665])).

tff(c_56,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_40,plain,(
    ! [A_67] : v5_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_762,plain,(
    ! [A_172,C_173,B_174] :
      ( k11_lattice3(A_172,C_173,B_174) = k11_lattice3(A_172,B_174,C_173)
      | ~ m1_subset_1(C_173,u1_struct_0(A_172))
      | ~ m1_subset_1(B_174,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v2_lattice3(A_172)
      | ~ v5_orders_2(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_769,plain,(
    ! [A_68,C_173,B_174] :
      ( k11_lattice3(k2_yellow_1(A_68),C_173,B_174) = k11_lattice3(k2_yellow_1(A_68),B_174,C_173)
      | ~ m1_subset_1(C_173,A_68)
      | ~ m1_subset_1(B_174,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68))
      | ~ v2_lattice3(k2_yellow_1(A_68))
      | ~ v5_orders_2(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_762])).

tff(c_789,plain,(
    ! [A_178,C_179,B_180] :
      ( k11_lattice3(k2_yellow_1(A_178),C_179,B_180) = k11_lattice3(k2_yellow_1(A_178),B_180,C_179)
      | ~ m1_subset_1(C_179,A_178)
      | ~ m1_subset_1(B_180,A_178)
      | ~ v2_lattice3(k2_yellow_1(A_178)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_42,c_769])).

tff(c_792,plain,(
    ! [C_179,B_180] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_179,B_180) = k11_lattice3(k2_yellow_1('#skF_2'),B_180,C_179)
      | ~ m1_subset_1(C_179,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_789])).

tff(c_987,plain,(
    ! [A_200,B_201,C_202] :
      ( r1_orders_2(A_200,k11_lattice3(A_200,B_201,C_202),C_202)
      | ~ m1_subset_1(k11_lattice3(A_200,B_201,C_202),u1_struct_0(A_200))
      | ~ m1_subset_1(C_202,u1_struct_0(A_200))
      | ~ m1_subset_1(B_201,u1_struct_0(A_200))
      | ~ l1_orders_2(A_200)
      | ~ v2_lattice3(A_200)
      | ~ v5_orders_2(A_200)
      | v2_struct_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_989,plain,(
    ! [B_180,C_179] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_180,C_179),C_179)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_179,B_180),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_179,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_180,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_179,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_987])).

tff(c_997,plain,(
    ! [B_180,C_179] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_180,C_179),C_179)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_179,B_180),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_179,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_56,c_32,c_42,c_42,c_42,c_989])).

tff(c_1053,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_997])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v2_struct_0(A_9)
      | ~ v2_lattice3(A_9)
      | ~ l1_orders_2(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1056,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_1053,c_10])).

tff(c_1060,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56,c_1056])).

tff(c_1062,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_997])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] :
      ( m1_subset_1(k11_lattice3(A_10,B_11,C_12),u1_struct_0(A_10))
      | ~ m1_subset_1(C_12,u1_struct_0(A_10))
      | ~ m1_subset_1(B_11,u1_struct_0(A_10))
      | ~ l1_orders_2(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1090,plain,(
    ! [A_211,B_212,C_213] :
      ( r1_orders_2(A_211,k11_lattice3(A_211,B_212,C_213),C_213)
      | ~ v2_lattice3(A_211)
      | ~ v5_orders_2(A_211)
      | v2_struct_0(A_211)
      | ~ m1_subset_1(C_213,u1_struct_0(A_211))
      | ~ m1_subset_1(B_212,u1_struct_0(A_211))
      | ~ l1_orders_2(A_211) ) ),
    inference(resolution,[status(thm)],[c_12,c_987])).

tff(c_1097,plain,(
    ! [C_179,B_180] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_179,B_180),C_179)
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_179,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_180,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_179,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_792,c_1090])).

tff(c_1105,plain,(
    ! [C_179,B_180] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_179,B_180),C_179)
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_179,'#skF_2')
      | ~ m1_subset_1(B_180,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42,c_42,c_40,c_56,c_1097])).

tff(c_1110,plain,(
    ! [C_214,B_215] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_214,B_215),C_214)
      | ~ m1_subset_1(C_214,'#skF_2')
      | ~ m1_subset_1(B_215,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1062,c_1105])).

tff(c_36,plain,(
    ! [A_67] : v3_orders_2(k2_yellow_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_777,plain,(
    ! [A_175,B_176,C_177] :
      ( r3_orders_2(A_175,B_176,C_177)
      | ~ r1_orders_2(A_175,B_176,C_177)
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | ~ v3_orders_2(A_175)
      | v2_struct_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_784,plain,(
    ! [A_68,B_176,C_177] :
      ( r3_orders_2(k2_yellow_1(A_68),B_176,C_177)
      | ~ r1_orders_2(k2_yellow_1(A_68),B_176,C_177)
      | ~ m1_subset_1(C_177,A_68)
      | ~ m1_subset_1(B_176,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68))
      | ~ v3_orders_2(k2_yellow_1(A_68))
      | v2_struct_0(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_777])).

tff(c_901,plain,(
    ! [A_189,B_190,C_191] :
      ( r3_orders_2(k2_yellow_1(A_189),B_190,C_191)
      | ~ r1_orders_2(k2_yellow_1(A_189),B_190,C_191)
      | ~ m1_subset_1(C_191,A_189)
      | ~ m1_subset_1(B_190,A_189)
      | v2_struct_0(k2_yellow_1(A_189)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_42,c_784])).

tff(c_48,plain,(
    ! [B_73,C_75,A_69] :
      ( r1_tarski(B_73,C_75)
      | ~ r3_orders_2(k2_yellow_1(A_69),B_73,C_75)
      | ~ m1_subset_1(C_75,u1_struct_0(k2_yellow_1(A_69)))
      | ~ m1_subset_1(B_73,u1_struct_0(k2_yellow_1(A_69)))
      | v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_61,plain,(
    ! [B_73,C_75,A_69] :
      ( r1_tarski(B_73,C_75)
      | ~ r3_orders_2(k2_yellow_1(A_69),B_73,C_75)
      | ~ m1_subset_1(C_75,A_69)
      | ~ m1_subset_1(B_73,A_69)
      | v1_xboole_0(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_48])).

tff(c_910,plain,(
    ! [B_190,C_191,A_189] :
      ( r1_tarski(B_190,C_191)
      | v1_xboole_0(A_189)
      | ~ r1_orders_2(k2_yellow_1(A_189),B_190,C_191)
      | ~ m1_subset_1(C_191,A_189)
      | ~ m1_subset_1(B_190,A_189)
      | v2_struct_0(k2_yellow_1(A_189)) ) ),
    inference(resolution,[status(thm)],[c_901,c_61])).

tff(c_1113,plain,(
    ! [C_214,B_215] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_214,B_215),C_214)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_214,B_215),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_214,'#skF_2')
      | ~ m1_subset_1(B_215,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1110,c_910])).

tff(c_1123,plain,(
    ! [C_216,B_217] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),C_216,B_217),C_216)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_216,B_217),'#skF_2')
      | ~ m1_subset_1(C_216,'#skF_2')
      | ~ m1_subset_1(B_217,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_1062,c_58,c_1113])).

tff(c_793,plain,(
    ! [C_181,B_182] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_181,B_182) = k11_lattice3(k2_yellow_1('#skF_2'),B_182,C_181)
      | ~ m1_subset_1(C_181,'#skF_2')
      | ~ m1_subset_1(B_182,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_789])).

tff(c_237,plain,(
    ! [A_107,B_108,C_109] :
      ( m1_subset_1(k11_lattice3(A_107,B_108,C_109),u1_struct_0(A_107))
      | ~ m1_subset_1(C_109,u1_struct_0(A_107))
      | ~ m1_subset_1(B_108,u1_struct_0(A_107))
      | ~ l1_orders_2(A_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_240,plain,(
    ! [A_68,B_108,C_109] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_68),B_108,C_109),A_68)
      | ~ m1_subset_1(C_109,u1_struct_0(k2_yellow_1(A_68)))
      | ~ m1_subset_1(B_108,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_237])).

tff(c_242,plain,(
    ! [A_68,B_108,C_109] :
      ( m1_subset_1(k11_lattice3(k2_yellow_1(A_68),B_108,C_109),A_68)
      | ~ m1_subset_1(C_109,A_68)
      | ~ m1_subset_1(B_108,A_68) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_42,c_42,c_240])).

tff(c_388,plain,(
    ! [A_132,C_133,B_134] :
      ( k11_lattice3(A_132,C_133,B_134) = k11_lattice3(A_132,B_134,C_133)
      | ~ m1_subset_1(C_133,u1_struct_0(A_132))
      | ~ m1_subset_1(B_134,u1_struct_0(A_132))
      | ~ l1_orders_2(A_132)
      | ~ v2_lattice3(A_132)
      | ~ v5_orders_2(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_395,plain,(
    ! [A_68,C_133,B_134] :
      ( k11_lattice3(k2_yellow_1(A_68),C_133,B_134) = k11_lattice3(k2_yellow_1(A_68),B_134,C_133)
      | ~ m1_subset_1(C_133,A_68)
      | ~ m1_subset_1(B_134,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68))
      | ~ v2_lattice3(k2_yellow_1(A_68))
      | ~ v5_orders_2(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_388])).

tff(c_400,plain,(
    ! [A_135,C_136,B_137] :
      ( k11_lattice3(k2_yellow_1(A_135),C_136,B_137) = k11_lattice3(k2_yellow_1(A_135),B_137,C_136)
      | ~ m1_subset_1(C_136,A_135)
      | ~ m1_subset_1(B_137,A_135)
      | ~ v2_lattice3(k2_yellow_1(A_135)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_32,c_42,c_395])).

tff(c_403,plain,(
    ! [C_136,B_137] :
      ( k11_lattice3(k2_yellow_1('#skF_2'),C_136,B_137) = k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_136)
      | ~ m1_subset_1(C_136,'#skF_2')
      | ~ m1_subset_1(B_137,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_56,c_400])).

tff(c_477,plain,(
    ! [A_140,B_141,C_142] :
      ( r1_orders_2(A_140,k11_lattice3(A_140,B_141,C_142),C_142)
      | ~ m1_subset_1(k11_lattice3(A_140,B_141,C_142),u1_struct_0(A_140))
      | ~ m1_subset_1(C_142,u1_struct_0(A_140))
      | ~ m1_subset_1(B_141,u1_struct_0(A_140))
      | ~ l1_orders_2(A_140)
      | ~ v2_lattice3(A_140)
      | ~ v5_orders_2(A_140)
      | v2_struct_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_481,plain,(
    ! [C_136,B_137] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_136,B_137),B_137)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_136),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_137,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_136,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_136,'#skF_2')
      | ~ m1_subset_1(B_137,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_477])).

tff(c_489,plain,(
    ! [C_136,B_137] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),C_136,B_137),B_137)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_136),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_136,'#skF_2')
      | ~ m1_subset_1(B_137,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_56,c_32,c_42,c_42,c_42,c_481])).

tff(c_542,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_489])).

tff(c_545,plain,
    ( ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_542,c_10])).

tff(c_549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_56,c_545])).

tff(c_551,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_489])).

tff(c_567,plain,(
    ! [A_147,B_148,C_149] :
      ( r1_orders_2(A_147,k11_lattice3(A_147,B_148,C_149),B_148)
      | ~ m1_subset_1(k11_lattice3(A_147,B_148,C_149),u1_struct_0(A_147))
      | ~ m1_subset_1(C_149,u1_struct_0(A_147))
      | ~ m1_subset_1(B_148,u1_struct_0(A_147))
      | ~ l1_orders_2(A_147)
      | ~ v2_lattice3(A_147)
      | ~ v5_orders_2(A_147)
      | v2_struct_0(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_569,plain,(
    ! [B_137,C_136] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_136),B_137)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_136,B_137),u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(C_136,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ m1_subset_1(B_137,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_136,'#skF_2')
      | ~ m1_subset_1(B_137,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_567])).

tff(c_577,plain,(
    ! [B_137,C_136] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_137,C_136),B_137)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_136,B_137),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(C_136,'#skF_2')
      | ~ m1_subset_1(B_137,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_56,c_32,c_42,c_42,c_42,c_569])).

tff(c_585,plain,(
    ! [B_150,C_151] :
      ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),B_150,C_151),B_150)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_151,B_150),'#skF_2')
      | ~ m1_subset_1(C_151,'#skF_2')
      | ~ m1_subset_1(B_150,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_577])).

tff(c_281,plain,(
    ! [A_115,B_116,C_117] :
      ( r3_orders_2(A_115,B_116,C_117)
      | ~ r1_orders_2(A_115,B_116,C_117)
      | ~ m1_subset_1(C_117,u1_struct_0(A_115))
      | ~ m1_subset_1(B_116,u1_struct_0(A_115))
      | ~ l1_orders_2(A_115)
      | ~ v3_orders_2(A_115)
      | v2_struct_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_288,plain,(
    ! [A_68,B_116,C_117] :
      ( r3_orders_2(k2_yellow_1(A_68),B_116,C_117)
      | ~ r1_orders_2(k2_yellow_1(A_68),B_116,C_117)
      | ~ m1_subset_1(C_117,A_68)
      | ~ m1_subset_1(B_116,u1_struct_0(k2_yellow_1(A_68)))
      | ~ l1_orders_2(k2_yellow_1(A_68))
      | ~ v3_orders_2(k2_yellow_1(A_68))
      | v2_struct_0(k2_yellow_1(A_68)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_281])).

tff(c_296,plain,(
    ! [A_118,B_119,C_120] :
      ( r3_orders_2(k2_yellow_1(A_118),B_119,C_120)
      | ~ r1_orders_2(k2_yellow_1(A_118),B_119,C_120)
      | ~ m1_subset_1(C_120,A_118)
      | ~ m1_subset_1(B_119,A_118)
      | v2_struct_0(k2_yellow_1(A_118)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_32,c_42,c_288])).

tff(c_300,plain,(
    ! [B_119,C_120,A_118] :
      ( r1_tarski(B_119,C_120)
      | v1_xboole_0(A_118)
      | ~ r1_orders_2(k2_yellow_1(A_118),B_119,C_120)
      | ~ m1_subset_1(C_120,A_118)
      | ~ m1_subset_1(B_119,A_118)
      | v2_struct_0(k2_yellow_1(A_118)) ) ),
    inference(resolution,[status(thm)],[c_296,c_61])).

tff(c_588,plain,(
    ! [B_150,C_151] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_150,C_151),B_150)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_150,C_151),'#skF_2')
      | v2_struct_0(k2_yellow_1('#skF_2'))
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_151,B_150),'#skF_2')
      | ~ m1_subset_1(C_151,'#skF_2')
      | ~ m1_subset_1(B_150,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_585,c_300])).

tff(c_599,plain,(
    ! [B_152,C_153] :
      ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),B_152,C_153),B_152)
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),B_152,C_153),'#skF_2')
      | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),C_153,B_152),'#skF_2')
      | ~ m1_subset_1(C_153,'#skF_2')
      | ~ m1_subset_1(B_152,'#skF_2') ) ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_58,c_588])).

tff(c_115,plain,(
    ! [A_92,B_93,C_94] :
      ( r1_tarski(A_92,k3_xboole_0(B_93,C_94))
      | ~ r1_tarski(A_92,C_94)
      | ~ r1_tarski(A_92,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_119,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_115,c_50])).

tff(c_154,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_119])).

tff(c_602,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_599,c_154])).

tff(c_611,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_602])).

tff(c_612,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_611])).

tff(c_615,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_242,c_612])).

tff(c_619,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_615])).

tff(c_621,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_620,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_611])).

tff(c_624,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_403,c_620])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_621,c_624])).

tff(c_634,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_119])).

tff(c_826,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_634])).

tff(c_861,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_826])).

tff(c_1126,plain,
    ( ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1123,c_861])).

tff(c_1135,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_60,c_1126])).

tff(c_1138,plain,
    ( ~ m1_subset_1('#skF_3','#skF_2')
    | ~ m1_subset_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_667,c_1135])).

tff(c_1142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_59,c_1138])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:16:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.55  
% 3.36/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.55  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k11_lattice3 > k4_xboole_0 > k3_xboole_0 > #nlpp > u1_struct_0 > u1_orders_2 > k2_yellow_1 > k1_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.36/1.55  
% 3.36/1.55  %Foreground sorts:
% 3.36/1.55  
% 3.36/1.55  
% 3.36/1.55  %Background operators:
% 3.36/1.55  
% 3.36/1.55  
% 3.36/1.55  %Foreground operators:
% 3.36/1.55  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.36/1.55  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.36/1.55  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.36/1.55  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.55  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.36/1.55  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.36/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.55  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.36/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.36/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.36/1.55  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.36/1.55  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.36/1.55  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.55  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.36/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.55  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.36/1.55  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.36/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.36/1.55  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.36/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.36/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.36/1.55  
% 3.36/1.57  tff(f_126, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.36/1.57  tff(f_153, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.36/1.57  tff(f_114, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.36/1.57  tff(f_63, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 3.36/1.57  tff(f_122, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.36/1.57  tff(f_110, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (k11_lattice3(A, B, C) = k11_lattice3(A, C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_lattice3)).
% 3.36/1.57  tff(f_96, axiom, (![A]: ((((~v2_struct_0(A) & v5_orders_2(A)) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k11_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l28_lattice3)).
% 3.36/1.57  tff(f_55, axiom, (![A]: (l1_orders_2(A) => (v2_lattice3(A) => ~v2_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_lattice3)).
% 3.36/1.57  tff(f_48, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.36/1.57  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.36/1.57  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.36/1.57  tff(c_42, plain, (![A_68]: (u1_struct_0(k2_yellow_1(A_68))=A_68)), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.36/1.57  tff(c_52, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.36/1.57  tff(c_60, plain, (m1_subset_1('#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_52])).
% 3.36/1.57  tff(c_54, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.36/1.57  tff(c_59, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_54])).
% 3.36/1.57  tff(c_32, plain, (![A_66]: (l1_orders_2(k2_yellow_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.36/1.57  tff(c_662, plain, (![A_159, B_160, C_161]: (m1_subset_1(k11_lattice3(A_159, B_160, C_161), u1_struct_0(A_159)) | ~m1_subset_1(C_161, u1_struct_0(A_159)) | ~m1_subset_1(B_160, u1_struct_0(A_159)) | ~l1_orders_2(A_159))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.57  tff(c_665, plain, (![A_68, B_160, C_161]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_68), B_160, C_161), A_68) | ~m1_subset_1(C_161, u1_struct_0(k2_yellow_1(A_68))) | ~m1_subset_1(B_160, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_662])).
% 3.36/1.57  tff(c_667, plain, (![A_68, B_160, C_161]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_68), B_160, C_161), A_68) | ~m1_subset_1(C_161, A_68) | ~m1_subset_1(B_160, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42, c_42, c_665])).
% 3.36/1.57  tff(c_56, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.36/1.57  tff(c_40, plain, (![A_67]: (v5_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.36/1.57  tff(c_762, plain, (![A_172, C_173, B_174]: (k11_lattice3(A_172, C_173, B_174)=k11_lattice3(A_172, B_174, C_173) | ~m1_subset_1(C_173, u1_struct_0(A_172)) | ~m1_subset_1(B_174, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v2_lattice3(A_172) | ~v5_orders_2(A_172))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.57  tff(c_769, plain, (![A_68, C_173, B_174]: (k11_lattice3(k2_yellow_1(A_68), C_173, B_174)=k11_lattice3(k2_yellow_1(A_68), B_174, C_173) | ~m1_subset_1(C_173, A_68) | ~m1_subset_1(B_174, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)) | ~v2_lattice3(k2_yellow_1(A_68)) | ~v5_orders_2(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_762])).
% 3.36/1.57  tff(c_789, plain, (![A_178, C_179, B_180]: (k11_lattice3(k2_yellow_1(A_178), C_179, B_180)=k11_lattice3(k2_yellow_1(A_178), B_180, C_179) | ~m1_subset_1(C_179, A_178) | ~m1_subset_1(B_180, A_178) | ~v2_lattice3(k2_yellow_1(A_178)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_42, c_769])).
% 3.36/1.57  tff(c_792, plain, (![C_179, B_180]: (k11_lattice3(k2_yellow_1('#skF_2'), C_179, B_180)=k11_lattice3(k2_yellow_1('#skF_2'), B_180, C_179) | ~m1_subset_1(C_179, '#skF_2') | ~m1_subset_1(B_180, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_789])).
% 3.36/1.57  tff(c_987, plain, (![A_200, B_201, C_202]: (r1_orders_2(A_200, k11_lattice3(A_200, B_201, C_202), C_202) | ~m1_subset_1(k11_lattice3(A_200, B_201, C_202), u1_struct_0(A_200)) | ~m1_subset_1(C_202, u1_struct_0(A_200)) | ~m1_subset_1(B_201, u1_struct_0(A_200)) | ~l1_orders_2(A_200) | ~v2_lattice3(A_200) | ~v5_orders_2(A_200) | v2_struct_0(A_200))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.57  tff(c_989, plain, (![B_180, C_179]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_180, C_179), C_179) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_179, B_180), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_179, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_180, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_179, '#skF_2') | ~m1_subset_1(B_180, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_792, c_987])).
% 3.36/1.57  tff(c_997, plain, (![B_180, C_179]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_180, C_179), C_179) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_179, B_180), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_179, '#skF_2') | ~m1_subset_1(B_180, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_56, c_32, c_42, c_42, c_42, c_989])).
% 3.36/1.57  tff(c_1053, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_997])).
% 3.36/1.57  tff(c_10, plain, (![A_9]: (~v2_struct_0(A_9) | ~v2_lattice3(A_9) | ~l1_orders_2(A_9))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.36/1.57  tff(c_1056, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_1053, c_10])).
% 3.36/1.57  tff(c_1060, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_56, c_1056])).
% 3.36/1.57  tff(c_1062, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_997])).
% 3.36/1.57  tff(c_58, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.36/1.57  tff(c_12, plain, (![A_10, B_11, C_12]: (m1_subset_1(k11_lattice3(A_10, B_11, C_12), u1_struct_0(A_10)) | ~m1_subset_1(C_12, u1_struct_0(A_10)) | ~m1_subset_1(B_11, u1_struct_0(A_10)) | ~l1_orders_2(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.57  tff(c_1090, plain, (![A_211, B_212, C_213]: (r1_orders_2(A_211, k11_lattice3(A_211, B_212, C_213), C_213) | ~v2_lattice3(A_211) | ~v5_orders_2(A_211) | v2_struct_0(A_211) | ~m1_subset_1(C_213, u1_struct_0(A_211)) | ~m1_subset_1(B_212, u1_struct_0(A_211)) | ~l1_orders_2(A_211))), inference(resolution, [status(thm)], [c_12, c_987])).
% 3.36/1.57  tff(c_1097, plain, (![C_179, B_180]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_179, B_180), C_179) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_179, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_180, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_179, '#skF_2') | ~m1_subset_1(B_180, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_792, c_1090])).
% 3.36/1.57  tff(c_1105, plain, (![C_179, B_180]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_179, B_180), C_179) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_179, '#skF_2') | ~m1_subset_1(B_180, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42, c_42, c_40, c_56, c_1097])).
% 3.36/1.57  tff(c_1110, plain, (![C_214, B_215]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_214, B_215), C_214) | ~m1_subset_1(C_214, '#skF_2') | ~m1_subset_1(B_215, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1062, c_1105])).
% 3.36/1.57  tff(c_36, plain, (![A_67]: (v3_orders_2(k2_yellow_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.36/1.57  tff(c_777, plain, (![A_175, B_176, C_177]: (r3_orders_2(A_175, B_176, C_177) | ~r1_orders_2(A_175, B_176, C_177) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | ~v3_orders_2(A_175) | v2_struct_0(A_175))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.36/1.57  tff(c_784, plain, (![A_68, B_176, C_177]: (r3_orders_2(k2_yellow_1(A_68), B_176, C_177) | ~r1_orders_2(k2_yellow_1(A_68), B_176, C_177) | ~m1_subset_1(C_177, A_68) | ~m1_subset_1(B_176, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)) | ~v3_orders_2(k2_yellow_1(A_68)) | v2_struct_0(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_777])).
% 3.36/1.57  tff(c_901, plain, (![A_189, B_190, C_191]: (r3_orders_2(k2_yellow_1(A_189), B_190, C_191) | ~r1_orders_2(k2_yellow_1(A_189), B_190, C_191) | ~m1_subset_1(C_191, A_189) | ~m1_subset_1(B_190, A_189) | v2_struct_0(k2_yellow_1(A_189)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_42, c_784])).
% 3.36/1.57  tff(c_48, plain, (![B_73, C_75, A_69]: (r1_tarski(B_73, C_75) | ~r3_orders_2(k2_yellow_1(A_69), B_73, C_75) | ~m1_subset_1(C_75, u1_struct_0(k2_yellow_1(A_69))) | ~m1_subset_1(B_73, u1_struct_0(k2_yellow_1(A_69))) | v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.36/1.57  tff(c_61, plain, (![B_73, C_75, A_69]: (r1_tarski(B_73, C_75) | ~r3_orders_2(k2_yellow_1(A_69), B_73, C_75) | ~m1_subset_1(C_75, A_69) | ~m1_subset_1(B_73, A_69) | v1_xboole_0(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_48])).
% 3.36/1.57  tff(c_910, plain, (![B_190, C_191, A_189]: (r1_tarski(B_190, C_191) | v1_xboole_0(A_189) | ~r1_orders_2(k2_yellow_1(A_189), B_190, C_191) | ~m1_subset_1(C_191, A_189) | ~m1_subset_1(B_190, A_189) | v2_struct_0(k2_yellow_1(A_189)))), inference(resolution, [status(thm)], [c_901, c_61])).
% 3.36/1.57  tff(c_1113, plain, (![C_214, B_215]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_214, B_215), C_214) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_214, B_215), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_214, '#skF_2') | ~m1_subset_1(B_215, '#skF_2'))), inference(resolution, [status(thm)], [c_1110, c_910])).
% 3.36/1.57  tff(c_1123, plain, (![C_216, B_217]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), C_216, B_217), C_216) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_216, B_217), '#skF_2') | ~m1_subset_1(C_216, '#skF_2') | ~m1_subset_1(B_217, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1062, c_58, c_1113])).
% 3.36/1.57  tff(c_793, plain, (![C_181, B_182]: (k11_lattice3(k2_yellow_1('#skF_2'), C_181, B_182)=k11_lattice3(k2_yellow_1('#skF_2'), B_182, C_181) | ~m1_subset_1(C_181, '#skF_2') | ~m1_subset_1(B_182, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_789])).
% 3.36/1.57  tff(c_237, plain, (![A_107, B_108, C_109]: (m1_subset_1(k11_lattice3(A_107, B_108, C_109), u1_struct_0(A_107)) | ~m1_subset_1(C_109, u1_struct_0(A_107)) | ~m1_subset_1(B_108, u1_struct_0(A_107)) | ~l1_orders_2(A_107))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.36/1.57  tff(c_240, plain, (![A_68, B_108, C_109]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_68), B_108, C_109), A_68) | ~m1_subset_1(C_109, u1_struct_0(k2_yellow_1(A_68))) | ~m1_subset_1(B_108, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_237])).
% 3.36/1.57  tff(c_242, plain, (![A_68, B_108, C_109]: (m1_subset_1(k11_lattice3(k2_yellow_1(A_68), B_108, C_109), A_68) | ~m1_subset_1(C_109, A_68) | ~m1_subset_1(B_108, A_68))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_42, c_42, c_240])).
% 3.36/1.57  tff(c_388, plain, (![A_132, C_133, B_134]: (k11_lattice3(A_132, C_133, B_134)=k11_lattice3(A_132, B_134, C_133) | ~m1_subset_1(C_133, u1_struct_0(A_132)) | ~m1_subset_1(B_134, u1_struct_0(A_132)) | ~l1_orders_2(A_132) | ~v2_lattice3(A_132) | ~v5_orders_2(A_132))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.36/1.57  tff(c_395, plain, (![A_68, C_133, B_134]: (k11_lattice3(k2_yellow_1(A_68), C_133, B_134)=k11_lattice3(k2_yellow_1(A_68), B_134, C_133) | ~m1_subset_1(C_133, A_68) | ~m1_subset_1(B_134, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)) | ~v2_lattice3(k2_yellow_1(A_68)) | ~v5_orders_2(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_388])).
% 3.36/1.57  tff(c_400, plain, (![A_135, C_136, B_137]: (k11_lattice3(k2_yellow_1(A_135), C_136, B_137)=k11_lattice3(k2_yellow_1(A_135), B_137, C_136) | ~m1_subset_1(C_136, A_135) | ~m1_subset_1(B_137, A_135) | ~v2_lattice3(k2_yellow_1(A_135)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_32, c_42, c_395])).
% 3.36/1.57  tff(c_403, plain, (![C_136, B_137]: (k11_lattice3(k2_yellow_1('#skF_2'), C_136, B_137)=k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_136) | ~m1_subset_1(C_136, '#skF_2') | ~m1_subset_1(B_137, '#skF_2'))), inference(resolution, [status(thm)], [c_56, c_400])).
% 3.36/1.57  tff(c_477, plain, (![A_140, B_141, C_142]: (r1_orders_2(A_140, k11_lattice3(A_140, B_141, C_142), C_142) | ~m1_subset_1(k11_lattice3(A_140, B_141, C_142), u1_struct_0(A_140)) | ~m1_subset_1(C_142, u1_struct_0(A_140)) | ~m1_subset_1(B_141, u1_struct_0(A_140)) | ~l1_orders_2(A_140) | ~v2_lattice3(A_140) | ~v5_orders_2(A_140) | v2_struct_0(A_140))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.57  tff(c_481, plain, (![C_136, B_137]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_136, B_137), B_137) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_136), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_137, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_136, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_136, '#skF_2') | ~m1_subset_1(B_137, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_403, c_477])).
% 3.36/1.57  tff(c_489, plain, (![C_136, B_137]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), C_136, B_137), B_137) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_136), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_136, '#skF_2') | ~m1_subset_1(B_137, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_56, c_32, c_42, c_42, c_42, c_481])).
% 3.36/1.57  tff(c_542, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_489])).
% 3.36/1.57  tff(c_545, plain, (~v2_lattice3(k2_yellow_1('#skF_2')) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_542, c_10])).
% 3.36/1.57  tff(c_549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_56, c_545])).
% 3.36/1.57  tff(c_551, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_489])).
% 3.36/1.57  tff(c_567, plain, (![A_147, B_148, C_149]: (r1_orders_2(A_147, k11_lattice3(A_147, B_148, C_149), B_148) | ~m1_subset_1(k11_lattice3(A_147, B_148, C_149), u1_struct_0(A_147)) | ~m1_subset_1(C_149, u1_struct_0(A_147)) | ~m1_subset_1(B_148, u1_struct_0(A_147)) | ~l1_orders_2(A_147) | ~v2_lattice3(A_147) | ~v5_orders_2(A_147) | v2_struct_0(A_147))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.36/1.57  tff(c_569, plain, (![B_137, C_136]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_136), B_137) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_136, B_137), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(C_136, u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(B_137, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_136, '#skF_2') | ~m1_subset_1(B_137, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_403, c_567])).
% 3.36/1.57  tff(c_577, plain, (![B_137, C_136]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_137, C_136), B_137) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_136, B_137), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(C_136, '#skF_2') | ~m1_subset_1(B_137, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_56, c_32, c_42, c_42, c_42, c_569])).
% 3.36/1.57  tff(c_585, plain, (![B_150, C_151]: (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), B_150, C_151), B_150) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_151, B_150), '#skF_2') | ~m1_subset_1(C_151, '#skF_2') | ~m1_subset_1(B_150, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_551, c_577])).
% 3.36/1.57  tff(c_281, plain, (![A_115, B_116, C_117]: (r3_orders_2(A_115, B_116, C_117) | ~r1_orders_2(A_115, B_116, C_117) | ~m1_subset_1(C_117, u1_struct_0(A_115)) | ~m1_subset_1(B_116, u1_struct_0(A_115)) | ~l1_orders_2(A_115) | ~v3_orders_2(A_115) | v2_struct_0(A_115))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.36/1.57  tff(c_288, plain, (![A_68, B_116, C_117]: (r3_orders_2(k2_yellow_1(A_68), B_116, C_117) | ~r1_orders_2(k2_yellow_1(A_68), B_116, C_117) | ~m1_subset_1(C_117, A_68) | ~m1_subset_1(B_116, u1_struct_0(k2_yellow_1(A_68))) | ~l1_orders_2(k2_yellow_1(A_68)) | ~v3_orders_2(k2_yellow_1(A_68)) | v2_struct_0(k2_yellow_1(A_68)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_281])).
% 3.36/1.57  tff(c_296, plain, (![A_118, B_119, C_120]: (r3_orders_2(k2_yellow_1(A_118), B_119, C_120) | ~r1_orders_2(k2_yellow_1(A_118), B_119, C_120) | ~m1_subset_1(C_120, A_118) | ~m1_subset_1(B_119, A_118) | v2_struct_0(k2_yellow_1(A_118)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_32, c_42, c_288])).
% 3.36/1.57  tff(c_300, plain, (![B_119, C_120, A_118]: (r1_tarski(B_119, C_120) | v1_xboole_0(A_118) | ~r1_orders_2(k2_yellow_1(A_118), B_119, C_120) | ~m1_subset_1(C_120, A_118) | ~m1_subset_1(B_119, A_118) | v2_struct_0(k2_yellow_1(A_118)))), inference(resolution, [status(thm)], [c_296, c_61])).
% 3.36/1.57  tff(c_588, plain, (![B_150, C_151]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_150, C_151), B_150) | v1_xboole_0('#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_150, C_151), '#skF_2') | v2_struct_0(k2_yellow_1('#skF_2')) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_151, B_150), '#skF_2') | ~m1_subset_1(C_151, '#skF_2') | ~m1_subset_1(B_150, '#skF_2'))), inference(resolution, [status(thm)], [c_585, c_300])).
% 3.36/1.57  tff(c_599, plain, (![B_152, C_153]: (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), B_152, C_153), B_152) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), B_152, C_153), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), C_153, B_152), '#skF_2') | ~m1_subset_1(C_153, '#skF_2') | ~m1_subset_1(B_152, '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_551, c_58, c_588])).
% 3.36/1.57  tff(c_115, plain, (![A_92, B_93, C_94]: (r1_tarski(A_92, k3_xboole_0(B_93, C_94)) | ~r1_tarski(A_92, C_94) | ~r1_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.36/1.57  tff(c_50, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 3.36/1.57  tff(c_119, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_115, c_50])).
% 3.36/1.57  tff(c_154, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_119])).
% 3.36/1.57  tff(c_602, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_599, c_154])).
% 3.36/1.57  tff(c_611, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_602])).
% 3.36/1.57  tff(c_612, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_611])).
% 3.36/1.57  tff(c_615, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_242, c_612])).
% 3.36/1.57  tff(c_619, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_615])).
% 3.36/1.57  tff(c_621, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_611])).
% 3.36/1.57  tff(c_620, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_2')), inference(splitRight, [status(thm)], [c_611])).
% 3.36/1.57  tff(c_624, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_403, c_620])).
% 3.36/1.57  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_621, c_624])).
% 3.36/1.57  tff(c_634, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_119])).
% 3.36/1.57  tff(c_826, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_793, c_634])).
% 3.36/1.57  tff(c_861, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_826])).
% 3.36/1.57  tff(c_1126, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1123, c_861])).
% 3.36/1.57  tff(c_1135, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_60, c_1126])).
% 3.36/1.57  tff(c_1138, plain, (~m1_subset_1('#skF_3', '#skF_2') | ~m1_subset_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_667, c_1135])).
% 3.36/1.57  tff(c_1142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_59, c_1138])).
% 3.36/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.57  
% 3.36/1.57  Inference rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Ref     : 0
% 3.36/1.57  #Sup     : 250
% 3.36/1.57  #Fact    : 0
% 3.36/1.57  #Define  : 0
% 3.36/1.57  #Split   : 4
% 3.36/1.57  #Chain   : 0
% 3.36/1.57  #Close   : 0
% 3.36/1.57  
% 3.36/1.57  Ordering : KBO
% 3.36/1.57  
% 3.36/1.57  Simplification rules
% 3.36/1.57  ----------------------
% 3.36/1.57  #Subsume      : 17
% 3.36/1.57  #Demod        : 270
% 3.36/1.57  #Tautology    : 121
% 3.36/1.57  #SimpNegUnit  : 8
% 3.36/1.57  #BackRed      : 0
% 3.36/1.57  
% 3.36/1.57  #Partial instantiations: 0
% 3.36/1.57  #Strategies tried      : 1
% 3.36/1.57  
% 3.36/1.57  Timing (in seconds)
% 3.36/1.57  ----------------------
% 3.36/1.57  Preprocessing        : 0.34
% 3.36/1.57  Parsing              : 0.19
% 3.36/1.57  CNF conversion       : 0.03
% 3.36/1.57  Main loop            : 0.46
% 3.36/1.57  Inferencing          : 0.17
% 3.36/1.57  Reduction            : 0.16
% 3.36/1.57  Demodulation         : 0.12
% 3.36/1.57  BG Simplification    : 0.03
% 3.36/1.57  Subsumption          : 0.07
% 3.36/1.57  Abstraction          : 0.02
% 3.36/1.57  MUC search           : 0.00
% 3.36/1.57  Cooper               : 0.00
% 3.36/1.57  Total                : 0.83
% 3.36/1.58  Index Insertion      : 0.00
% 3.36/1.58  Index Deletion       : 0.00
% 3.36/1.58  Index Matching       : 0.00
% 3.36/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
