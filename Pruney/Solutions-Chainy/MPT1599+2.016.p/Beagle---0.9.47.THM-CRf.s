%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:24 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 550 expanded)
%              Number of leaves         :   34 ( 228 expanded)
%              Depth                    :   12
%              Number of atoms          :  245 (1705 expanded)
%              Number of equality atoms :   10 (  99 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v2_lattice3,type,(
    v2_lattice3: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v2_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k11_lattice3(k2_yellow_1(A),B,C),k3_xboole_0(B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k11_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k11_lattice3)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v2_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k12_lattice3(A,B,C) = k11_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

tff(f_96,axiom,(
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

tff(f_116,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_63,plain,(
    ! [A_79,B_80,C_81] :
      ( r1_tarski(A_79,k3_xboole_0(B_80,C_81))
      | ~ r1_tarski(A_79,C_81)
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),k3_xboole_0('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,
    ( ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_46])).

tff(c_68,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_28,plain,(
    ! [A_59] : l1_orders_2(k2_yellow_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k11_lattice3(A_7,B_8,C_9),u1_struct_0(A_7))
      | ~ m1_subset_1(C_9,u1_struct_0(A_7))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_60] : v5_orders_2(k2_yellow_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    v2_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_125,plain,(
    ! [A_96,B_97,C_98] :
      ( k12_lattice3(A_96,B_97,C_98) = k11_lattice3(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v2_lattice3(A_96)
      | ~ v5_orders_2(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_129,plain,(
    ! [B_97] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_4')
      | ~ m1_subset_1(B_97,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_139,plain,(
    ! [B_99] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_99,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_99,'#skF_4')
      | ~ m1_subset_1(B_99,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_129])).

tff(c_154,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_139])).

tff(c_246,plain,(
    ! [A_106,B_107,C_108] :
      ( r1_orders_2(A_106,k12_lattice3(A_106,B_107,C_108),B_107)
      | ~ m1_subset_1(k12_lattice3(A_106,B_107,C_108),u1_struct_0(A_106))
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v2_lattice3(A_106)
      | ~ v5_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_252,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_246])).

tff(c_260,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_50,c_48,c_154,c_252])).

tff(c_443,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_446,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_443])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50,c_48,c_446])).

tff(c_452,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_451,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_32,plain,(
    ! [A_60] : v3_orders_2(k2_yellow_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_187,plain,(
    ! [A_101,B_102,C_103] :
      ( r3_orders_2(A_101,B_102,C_103)
      | ~ r1_orders_2(A_101,B_102,C_103)
      | ~ m1_subset_1(C_103,u1_struct_0(A_101))
      | ~ m1_subset_1(B_102,u1_struct_0(A_101))
      | ~ l1_orders_2(A_101)
      | ~ v3_orders_2(A_101)
      | v2_struct_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_191,plain,(
    ! [B_102] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_4')
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_187])).

tff(c_197,plain,(
    ! [B_102] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_4')
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_191])).

tff(c_201,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_197])).

tff(c_40,plain,(
    ! [A_61] :
      ( ~ v2_struct_0(k2_yellow_1(A_61))
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_204,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_201,c_40])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_204])).

tff(c_210,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_197])).

tff(c_193,plain,(
    ! [B_102] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_3')
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_50,c_187])).

tff(c_200,plain,(
    ! [B_102] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_3')
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_193])).

tff(c_211,plain,(
    ! [B_102] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_3')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_102,'#skF_3')
      | ~ m1_subset_1(B_102,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_200])).

tff(c_464,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_452,c_211])).

tff(c_486,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_464])).

tff(c_44,plain,(
    ! [B_66,C_68,A_62] :
      ( r1_tarski(B_66,C_68)
      | ~ r3_orders_2(k2_yellow_1(A_62),B_66,C_68)
      | ~ m1_subset_1(C_68,u1_struct_0(k2_yellow_1(A_62)))
      | ~ m1_subset_1(B_66,u1_struct_0(k2_yellow_1(A_62)))
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_504,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_486,c_44])).

tff(c_511,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_50,c_504])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_68,c_511])).

tff(c_514,plain,(
    ~ r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_632,plain,(
    ! [A_141,B_142,C_143] :
      ( k12_lattice3(A_141,B_142,C_143) = k11_lattice3(A_141,B_142,C_143)
      | ~ m1_subset_1(C_143,u1_struct_0(A_141))
      | ~ m1_subset_1(B_142,u1_struct_0(A_141))
      | ~ l1_orders_2(A_141)
      | ~ v2_lattice3(A_141)
      | ~ v5_orders_2(A_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_636,plain,(
    ! [B_142] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_142,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_142,'#skF_4')
      | ~ m1_subset_1(B_142,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v2_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_632])).

tff(c_647,plain,(
    ! [B_144] :
      ( k12_lattice3(k2_yellow_1('#skF_2'),B_144,'#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),B_144,'#skF_4')
      | ~ m1_subset_1(B_144,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_636])).

tff(c_662,plain,(
    k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_647])).

tff(c_803,plain,(
    ! [A_156,B_157,C_158] :
      ( r1_orders_2(A_156,k12_lattice3(A_156,B_157,C_158),B_157)
      | ~ m1_subset_1(k12_lattice3(A_156,B_157,C_158),u1_struct_0(A_156))
      | ~ m1_subset_1(C_158,u1_struct_0(A_156))
      | ~ m1_subset_1(B_157,u1_struct_0(A_156))
      | ~ l1_orders_2(A_156)
      | ~ v2_lattice3(A_156)
      | ~ v5_orders_2(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_809,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_803])).

tff(c_817,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_3')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_50,c_48,c_662,c_809])).

tff(c_836,plain,(
    ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_817])).

tff(c_839,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_836])).

tff(c_843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50,c_48,c_839])).

tff(c_845,plain,(
    m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_817])).

tff(c_722,plain,(
    ! [A_153,B_154,C_155] :
      ( r1_orders_2(A_153,k12_lattice3(A_153,B_154,C_155),C_155)
      | ~ m1_subset_1(k12_lattice3(A_153,B_154,C_155),u1_struct_0(A_153))
      | ~ m1_subset_1(C_155,u1_struct_0(A_153))
      | ~ m1_subset_1(B_154,u1_struct_0(A_153))
      | ~ l1_orders_2(A_153)
      | ~ v2_lattice3(A_153)
      | ~ v5_orders_2(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_728,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k12_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v2_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_662,c_722])).

tff(c_736,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_50,c_48,c_662,c_728])).

tff(c_1334,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_736])).

tff(c_571,plain,(
    ! [A_133,B_134,C_135] :
      ( r3_orders_2(A_133,B_134,C_135)
      | ~ r1_orders_2(A_133,B_134,C_135)
      | ~ m1_subset_1(C_135,u1_struct_0(A_133))
      | ~ m1_subset_1(B_134,u1_struct_0(A_133))
      | ~ l1_orders_2(A_133)
      | ~ v3_orders_2(A_133)
      | v2_struct_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_575,plain,(
    ! [B_134] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_134,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_134,'#skF_4')
      | ~ m1_subset_1(B_134,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_571])).

tff(c_581,plain,(
    ! [B_134] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_134,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_134,'#skF_4')
      | ~ m1_subset_1(B_134,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_575])).

tff(c_585,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_581])).

tff(c_589,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_585,c_40])).

tff(c_593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_589])).

tff(c_594,plain,(
    ! [B_134] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_134,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_134,'#skF_4')
      | ~ m1_subset_1(B_134,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(splitRight,[status(thm)],[c_581])).

tff(c_878,plain,
    ( r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ r1_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_845,c_594])).

tff(c_1481,plain,(
    r3_orders_2(k2_yellow_1('#skF_2'),k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_878])).

tff(c_1485,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1481,c_44])).

tff(c_1492,plain,
    ( r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_845,c_48,c_1485])).

tff(c_1494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_514,c_1492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:45:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.65  
% 3.70/1.65  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.66  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v2_lattice3 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k12_lattice3 > k11_lattice3 > k3_xboole_0 > #nlpp > u1_struct_0 > k2_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.70/1.66  
% 3.70/1.66  %Foreground sorts:
% 3.70/1.66  
% 3.70/1.66  
% 3.70/1.66  %Background operators:
% 3.70/1.66  
% 3.70/1.66  
% 3.70/1.66  %Foreground operators:
% 3.70/1.66  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.70/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.70/1.66  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.70/1.66  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.66  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.70/1.66  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.70/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.70/1.66  tff(k11_lattice3, type, k11_lattice3: ($i * $i * $i) > $i).
% 3.70/1.66  tff(k12_lattice3, type, k12_lattice3: ($i * $i * $i) > $i).
% 3.70/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.70/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.70/1.66  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.70/1.66  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.70/1.66  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.70/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.70/1.66  tff(v2_lattice3, type, v2_lattice3: $i > $o).
% 3.70/1.66  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.70/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.70/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.66  
% 3.70/1.68  tff(f_143, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v2_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k11_lattice3(k2_yellow_1(A), B, C), k3_xboole_0(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_yellow_1)).
% 3.70/1.68  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.70/1.68  tff(f_100, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.70/1.68  tff(f_54, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k11_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k11_lattice3)).
% 3.70/1.68  tff(f_108, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.70/1.68  tff(f_66, axiom, (![A, B, C]: (((((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k12_lattice3(A, B, C) = k11_lattice3(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 3.70/1.68  tff(f_96, axiom, (![A]: (((v5_orders_2(A) & v2_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k12_lattice3(A, B, C)) <=> ((r1_orders_2(A, D, B) & r1_orders_2(A, D, C)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, E, B) & r1_orders_2(A, E, C)) => r1_orders_2(A, E, D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_yellow_0)).
% 3.70/1.68  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.70/1.68  tff(f_116, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.70/1.68  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.70/1.68  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.70/1.68  tff(c_63, plain, (![A_79, B_80, C_81]: (r1_tarski(A_79, k3_xboole_0(B_80, C_81)) | ~r1_tarski(A_79, C_81) | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.68  tff(c_46, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), k3_xboole_0('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.70/1.68  tff(c_67, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_63, c_46])).
% 3.70/1.68  tff(c_68, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_67])).
% 3.70/1.68  tff(c_28, plain, (![A_59]: (l1_orders_2(k2_yellow_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.70/1.68  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.70/1.68  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.70/1.68  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k11_lattice3(A_7, B_8, C_9), u1_struct_0(A_7)) | ~m1_subset_1(C_9, u1_struct_0(A_7)) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.70/1.68  tff(c_36, plain, (![A_60]: (v5_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.70/1.68  tff(c_52, plain, (v2_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.70/1.68  tff(c_125, plain, (![A_96, B_97, C_98]: (k12_lattice3(A_96, B_97, C_98)=k11_lattice3(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v2_lattice3(A_96) | ~v5_orders_2(A_96))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.70/1.68  tff(c_129, plain, (![B_97]: (k12_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_4') | ~m1_subset_1(B_97, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_125])).
% 3.70/1.68  tff(c_139, plain, (![B_99]: (k12_lattice3(k2_yellow_1('#skF_2'), B_99, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_99, '#skF_4') | ~m1_subset_1(B_99, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_129])).
% 3.70/1.68  tff(c_154, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_139])).
% 3.70/1.68  tff(c_246, plain, (![A_106, B_107, C_108]: (r1_orders_2(A_106, k12_lattice3(A_106, B_107, C_108), B_107) | ~m1_subset_1(k12_lattice3(A_106, B_107, C_108), u1_struct_0(A_106)) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v2_lattice3(A_106) | ~v5_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.70/1.68  tff(c_252, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_246])).
% 3.70/1.68  tff(c_260, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_50, c_48, c_154, c_252])).
% 3.70/1.68  tff(c_443, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_260])).
% 3.70/1.68  tff(c_446, plain, (~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_443])).
% 3.70/1.68  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_50, c_48, c_446])).
% 3.70/1.68  tff(c_452, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(splitRight, [status(thm)], [c_260])).
% 3.70/1.68  tff(c_451, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_260])).
% 3.70/1.68  tff(c_32, plain, (![A_60]: (v3_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.70/1.68  tff(c_187, plain, (![A_101, B_102, C_103]: (r3_orders_2(A_101, B_102, C_103) | ~r1_orders_2(A_101, B_102, C_103) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.70/1.68  tff(c_191, plain, (![B_102]: (r3_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_187])).
% 3.70/1.68  tff(c_197, plain, (![B_102]: (r3_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_191])).
% 3.70/1.68  tff(c_201, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_197])).
% 3.70/1.68  tff(c_40, plain, (![A_61]: (~v2_struct_0(k2_yellow_1(A_61)) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.70/1.68  tff(c_204, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_201, c_40])).
% 3.70/1.68  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_204])).
% 3.70/1.68  tff(c_210, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_197])).
% 3.70/1.68  tff(c_193, plain, (![B_102]: (r3_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_3') | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_50, c_187])).
% 3.70/1.68  tff(c_200, plain, (![B_102]: (r3_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_3') | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_193])).
% 3.70/1.68  tff(c_211, plain, (![B_102]: (r3_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_3') | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_210, c_200])).
% 3.70/1.68  tff(c_464, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_452, c_211])).
% 3.70/1.68  tff(c_486, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_451, c_464])).
% 3.70/1.68  tff(c_44, plain, (![B_66, C_68, A_62]: (r1_tarski(B_66, C_68) | ~r3_orders_2(k2_yellow_1(A_62), B_66, C_68) | ~m1_subset_1(C_68, u1_struct_0(k2_yellow_1(A_62))) | ~m1_subset_1(B_66, u1_struct_0(k2_yellow_1(A_62))) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_129])).
% 3.70/1.68  tff(c_504, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_486, c_44])).
% 3.70/1.68  tff(c_511, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_50, c_504])).
% 3.70/1.68  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_68, c_511])).
% 3.70/1.68  tff(c_514, plain, (~r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_67])).
% 3.70/1.68  tff(c_632, plain, (![A_141, B_142, C_143]: (k12_lattice3(A_141, B_142, C_143)=k11_lattice3(A_141, B_142, C_143) | ~m1_subset_1(C_143, u1_struct_0(A_141)) | ~m1_subset_1(B_142, u1_struct_0(A_141)) | ~l1_orders_2(A_141) | ~v2_lattice3(A_141) | ~v5_orders_2(A_141))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.70/1.68  tff(c_636, plain, (![B_142]: (k12_lattice3(k2_yellow_1('#skF_2'), B_142, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_142, '#skF_4') | ~m1_subset_1(B_142, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_632])).
% 3.70/1.68  tff(c_647, plain, (![B_144]: (k12_lattice3(k2_yellow_1('#skF_2'), B_144, '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), B_144, '#skF_4') | ~m1_subset_1(B_144, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_636])).
% 3.70/1.68  tff(c_662, plain, (k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_647])).
% 3.70/1.68  tff(c_803, plain, (![A_156, B_157, C_158]: (r1_orders_2(A_156, k12_lattice3(A_156, B_157, C_158), B_157) | ~m1_subset_1(k12_lattice3(A_156, B_157, C_158), u1_struct_0(A_156)) | ~m1_subset_1(C_158, u1_struct_0(A_156)) | ~m1_subset_1(B_157, u1_struct_0(A_156)) | ~l1_orders_2(A_156) | ~v2_lattice3(A_156) | ~v5_orders_2(A_156))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.70/1.68  tff(c_809, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_803])).
% 3.70/1.68  tff(c_817, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_3') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_50, c_48, c_662, c_809])).
% 3.70/1.68  tff(c_836, plain, (~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_817])).
% 3.70/1.68  tff(c_839, plain, (~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_836])).
% 3.70/1.68  tff(c_843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_50, c_48, c_839])).
% 3.70/1.68  tff(c_845, plain, (m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(splitRight, [status(thm)], [c_817])).
% 3.70/1.68  tff(c_722, plain, (![A_153, B_154, C_155]: (r1_orders_2(A_153, k12_lattice3(A_153, B_154, C_155), C_155) | ~m1_subset_1(k12_lattice3(A_153, B_154, C_155), u1_struct_0(A_153)) | ~m1_subset_1(C_155, u1_struct_0(A_153)) | ~m1_subset_1(B_154, u1_struct_0(A_153)) | ~l1_orders_2(A_153) | ~v2_lattice3(A_153) | ~v5_orders_2(A_153))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.70/1.68  tff(c_728, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k12_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v2_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_662, c_722])).
% 3.70/1.68  tff(c_736, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_50, c_48, c_662, c_728])).
% 3.70/1.68  tff(c_1334, plain, (r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_736])).
% 3.70/1.68  tff(c_571, plain, (![A_133, B_134, C_135]: (r3_orders_2(A_133, B_134, C_135) | ~r1_orders_2(A_133, B_134, C_135) | ~m1_subset_1(C_135, u1_struct_0(A_133)) | ~m1_subset_1(B_134, u1_struct_0(A_133)) | ~l1_orders_2(A_133) | ~v3_orders_2(A_133) | v2_struct_0(A_133))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.70/1.68  tff(c_575, plain, (![B_134]: (r3_orders_2(k2_yellow_1('#skF_2'), B_134, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_134, '#skF_4') | ~m1_subset_1(B_134, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_571])).
% 3.70/1.68  tff(c_581, plain, (![B_134]: (r3_orders_2(k2_yellow_1('#skF_2'), B_134, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_134, '#skF_4') | ~m1_subset_1(B_134, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_575])).
% 3.70/1.68  tff(c_585, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_581])).
% 3.70/1.68  tff(c_589, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_585, c_40])).
% 3.70/1.68  tff(c_593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_589])).
% 3.70/1.68  tff(c_594, plain, (![B_134]: (r3_orders_2(k2_yellow_1('#skF_2'), B_134, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_134, '#skF_4') | ~m1_subset_1(B_134, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_581])).
% 3.70/1.68  tff(c_878, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_845, c_594])).
% 3.70/1.68  tff(c_1481, plain, (r3_orders_2(k2_yellow_1('#skF_2'), k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1334, c_878])).
% 3.70/1.68  tff(c_1485, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1481, c_44])).
% 3.70/1.68  tff(c_1492, plain, (r1_tarski(k11_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), '#skF_4') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_845, c_48, c_1485])).
% 3.70/1.68  tff(c_1494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_514, c_1492])).
% 3.70/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.68  
% 3.70/1.68  Inference rules
% 3.70/1.68  ----------------------
% 3.70/1.68  #Ref     : 0
% 3.70/1.68  #Sup     : 275
% 3.70/1.68  #Fact    : 0
% 3.70/1.68  #Define  : 0
% 3.70/1.68  #Split   : 34
% 3.70/1.68  #Chain   : 0
% 3.70/1.68  #Close   : 0
% 3.70/1.68  
% 3.70/1.68  Ordering : KBO
% 3.70/1.68  
% 3.70/1.68  Simplification rules
% 3.70/1.68  ----------------------
% 3.70/1.68  #Subsume      : 2
% 3.70/1.68  #Demod        : 556
% 3.70/1.68  #Tautology    : 70
% 3.70/1.68  #SimpNegUnit  : 66
% 3.70/1.68  #BackRed      : 0
% 3.70/1.68  
% 3.70/1.68  #Partial instantiations: 0
% 3.70/1.68  #Strategies tried      : 1
% 3.70/1.68  
% 3.70/1.68  Timing (in seconds)
% 3.70/1.68  ----------------------
% 3.70/1.68  Preprocessing        : 0.34
% 3.70/1.68  Parsing              : 0.18
% 3.70/1.68  CNF conversion       : 0.03
% 3.70/1.68  Main loop            : 0.54
% 3.70/1.68  Inferencing          : 0.17
% 3.70/1.68  Reduction            : 0.21
% 3.70/1.68  Demodulation         : 0.15
% 3.70/1.68  BG Simplification    : 0.03
% 3.70/1.68  Subsumption          : 0.10
% 3.70/1.68  Abstraction          : 0.03
% 3.70/1.68  MUC search           : 0.00
% 3.70/1.68  Cooper               : 0.00
% 3.70/1.68  Total                : 0.92
% 3.70/1.68  Index Insertion      : 0.00
% 3.70/1.68  Index Deletion       : 0.00
% 3.70/1.68  Index Matching       : 0.00
% 3.70/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
