%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:22 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 558 expanded)
%              Number of leaves         :   34 ( 230 expanded)
%              Depth                    :   16
%              Number of atoms          :  273 (1742 expanded)
%              Number of equality atoms :   10 (  99 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

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

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_143,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( v1_lattice3(k2_yellow_1(A))
         => ! [B] :
              ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
             => ! [C] :
                  ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
                 => r1_tarski(k2_xboole_0(B,C),k10_lattice3(k2_yellow_1(A),B,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_1)).

tff(f_100,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => m1_subset_1(k10_lattice3(A,B,C),u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_lattice3)).

tff(f_108,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( v5_orders_2(A)
        & v1_lattice3(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => k13_lattice3(A,B,C) = k10_lattice3(A,B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

tff(f_96,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_116,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(f_129,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

tff(c_63,plain,(
    ! [A_79,C_80,B_81] :
      ( r1_tarski(k2_xboole_0(A_79,C_80),B_81)
      | ~ r1_tarski(C_80,B_81)
      | ~ r1_tarski(A_79,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_3','#skF_4'),k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_67,plain,
    ( ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_63,c_46])).

tff(c_68,plain,(
    ~ r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_28,plain,(
    ! [A_59] : l1_orders_2(k2_yellow_1(A_59)) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9] :
      ( m1_subset_1(k10_lattice3(A_7,B_8,C_9),u1_struct_0(A_7))
      | ~ m1_subset_1(C_9,u1_struct_0(A_7))
      | ~ m1_subset_1(B_8,u1_struct_0(A_7))
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_36,plain,(
    ! [A_60] : v5_orders_2(k2_yellow_1(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_52,plain,(
    v1_lattice3(k2_yellow_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_125,plain,(
    ! [A_96,B_97,C_98] :
      ( k13_lattice3(A_96,B_97,C_98) = k10_lattice3(A_96,B_97,C_98)
      | ~ m1_subset_1(C_98,u1_struct_0(A_96))
      | ~ m1_subset_1(B_97,u1_struct_0(A_96))
      | ~ l1_orders_2(A_96)
      | ~ v1_lattice3(A_96)
      | ~ v5_orders_2(A_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_129,plain,(
    ! [B_97] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),B_97,'#skF_4')
      | ~ m1_subset_1(B_97,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_139,plain,(
    ! [B_99] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_99,'#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),B_99,'#skF_4')
      | ~ m1_subset_1(B_99,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_129])).

tff(c_154,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_139])).

tff(c_246,plain,(
    ! [A_106,B_107,C_108] :
      ( r1_orders_2(A_106,B_107,k13_lattice3(A_106,B_107,C_108))
      | ~ m1_subset_1(k13_lattice3(A_106,B_107,C_108),u1_struct_0(A_106))
      | ~ m1_subset_1(C_108,u1_struct_0(A_106))
      | ~ m1_subset_1(B_107,u1_struct_0(A_106))
      | ~ l1_orders_2(A_106)
      | ~ v1_lattice3(A_106)
      | ~ v5_orders_2(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_252,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),'#skF_3',k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_246])).

tff(c_260,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),'#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_50,c_48,c_154,c_252])).

tff(c_413,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_416,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_413])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50,c_48,c_416])).

tff(c_421,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),'#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_422,plain,(
    m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
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

tff(c_4,plain,(
    ! [A_4,B_5,C_6] :
      ( r3_orders_2(A_4,B_5,C_6)
      | ~ r1_orders_2(A_4,B_5,C_6)
      | ~ m1_subset_1(C_6,u1_struct_0(A_4))
      | ~ m1_subset_1(B_5,u1_struct_0(A_4))
      | ~ l1_orders_2(A_4)
      | ~ v3_orders_2(A_4)
      | v2_struct_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_430,plain,(
    ! [B_5] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_5,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_422,c_4])).

tff(c_451,plain,(
    ! [B_5] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_5,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_430])).

tff(c_962,plain,(
    ! [B_150] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_150,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_150,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_150,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_451])).

tff(c_44,plain,(
    ! [B_66,C_68,A_62] :
      ( r1_tarski(B_66,C_68)
      | ~ r3_orders_2(k2_yellow_1(A_62),B_66,C_68)
      | ~ m1_subset_1(C_68,u1_struct_0(k2_yellow_1(A_62)))
      | ~ m1_subset_1(B_66,u1_struct_0(k2_yellow_1(A_62)))
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_966,plain,(
    ! [B_150] :
      ( r1_tarski(B_150,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_150,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_150,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_962,c_44])).

tff(c_973,plain,(
    ! [B_150] :
      ( r1_tarski(B_150,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_150,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_150,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_966])).

tff(c_985,plain,(
    ! [B_155] :
      ( r1_tarski(B_155,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_155,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_155,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_973])).

tff(c_1002,plain,
    ( r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_421,c_985])).

tff(c_1015,plain,(
    r1_tarski('#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_1002])).

tff(c_1017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1015])).

tff(c_1018,plain,(
    ~ r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_1136,plain,(
    ! [A_175,B_176,C_177] :
      ( k13_lattice3(A_175,B_176,C_177) = k10_lattice3(A_175,B_176,C_177)
      | ~ m1_subset_1(C_177,u1_struct_0(A_175))
      | ~ m1_subset_1(B_176,u1_struct_0(A_175))
      | ~ l1_orders_2(A_175)
      | ~ v1_lattice3(A_175)
      | ~ v5_orders_2(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1140,plain,(
    ! [B_176] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_176,'#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),B_176,'#skF_4')
      | ~ m1_subset_1(B_176,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v1_lattice3(k2_yellow_1('#skF_2'))
      | ~ v5_orders_2(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1136])).

tff(c_1151,plain,(
    ! [B_178] :
      ( k13_lattice3(k2_yellow_1('#skF_2'),B_178,'#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),B_178,'#skF_4')
      | ~ m1_subset_1(B_178,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_1140])).

tff(c_1166,plain,(
    k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') = k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1151])).

tff(c_1212,plain,(
    ! [A_182,B_183,C_184] :
      ( r1_orders_2(A_182,B_183,k13_lattice3(A_182,B_183,C_184))
      | ~ m1_subset_1(k13_lattice3(A_182,B_183,C_184),u1_struct_0(A_182))
      | ~ m1_subset_1(C_184,u1_struct_0(A_182))
      | ~ m1_subset_1(B_183,u1_struct_0(A_182))
      | ~ l1_orders_2(A_182)
      | ~ v1_lattice3(A_182)
      | ~ v5_orders_2(A_182) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1218,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),'#skF_3',k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_1212])).

tff(c_1226,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),'#skF_3',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_50,c_48,c_1166,c_1218])).

tff(c_1239,plain,(
    ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1226])).

tff(c_1282,plain,
    ( ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_8,c_1239])).

tff(c_1286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_50,c_48,c_1282])).

tff(c_1288,plain,(
    m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_1226])).

tff(c_1369,plain,(
    ! [A_185,C_186,B_187] :
      ( r1_orders_2(A_185,C_186,k13_lattice3(A_185,B_187,C_186))
      | ~ m1_subset_1(k13_lattice3(A_185,B_187,C_186),u1_struct_0(A_185))
      | ~ m1_subset_1(C_186,u1_struct_0(A_185))
      | ~ m1_subset_1(B_187,u1_struct_0(A_185))
      | ~ l1_orders_2(A_185)
      | ~ v1_lattice3(A_185)
      | ~ v5_orders_2(A_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1375,plain,
    ( r1_orders_2(k2_yellow_1('#skF_2'),'#skF_4',k13_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ m1_subset_1('#skF_3',u1_struct_0(k2_yellow_1('#skF_2')))
    | ~ l1_orders_2(k2_yellow_1('#skF_2'))
    | ~ v1_lattice3(k2_yellow_1('#skF_2'))
    | ~ v5_orders_2(k2_yellow_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1166,c_1369])).

tff(c_1383,plain,(
    r1_orders_2(k2_yellow_1('#skF_2'),'#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52,c_28,c_50,c_48,c_1288,c_1166,c_1375])).

tff(c_1075,plain,(
    ! [A_167,B_168,C_169] :
      ( r3_orders_2(A_167,B_168,C_169)
      | ~ r1_orders_2(A_167,B_168,C_169)
      | ~ m1_subset_1(C_169,u1_struct_0(A_167))
      | ~ m1_subset_1(B_168,u1_struct_0(A_167))
      | ~ l1_orders_2(A_167)
      | ~ v3_orders_2(A_167)
      | v2_struct_0(A_167) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1079,plain,(
    ! [B_168] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_168,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_168,'#skF_4')
      | ~ m1_subset_1(B_168,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_48,c_1075])).

tff(c_1085,plain,(
    ! [B_168] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_168,'#skF_4')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_168,'#skF_4')
      | ~ m1_subset_1(B_168,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1079])).

tff(c_1089,plain,(
    v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1085])).

tff(c_1092,plain,(
    v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1089,c_40])).

tff(c_1096,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1092])).

tff(c_1098,plain,(
    ~ v2_struct_0(k2_yellow_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1085])).

tff(c_1344,plain,(
    ! [B_5] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_5,u1_struct_0(k2_yellow_1('#skF_2')))
      | ~ l1_orders_2(k2_yellow_1('#skF_2'))
      | ~ v3_orders_2(k2_yellow_1('#skF_2'))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_1288,c_4])).

tff(c_1362,plain,(
    ! [B_5] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_5,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_5,u1_struct_0(k2_yellow_1('#skF_2')))
      | v2_struct_0(k2_yellow_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_1344])).

tff(c_2278,plain,(
    ! [B_244] :
      ( r3_orders_2(k2_yellow_1('#skF_2'),B_244,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_244,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_244,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1098,c_1362])).

tff(c_2282,plain,(
    ! [B_244] :
      ( r1_tarski(B_244,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'),u1_struct_0(k2_yellow_1('#skF_2')))
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_244,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_244,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_2278,c_44])).

tff(c_2289,plain,(
    ! [B_244] :
      ( r1_tarski(B_244,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | v1_xboole_0('#skF_2')
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_244,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_244,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_2282])).

tff(c_2300,plain,(
    ! [B_249] :
      ( r1_tarski(B_249,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ r1_orders_2(k2_yellow_1('#skF_2'),B_249,k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
      | ~ m1_subset_1(B_249,u1_struct_0(k2_yellow_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_2289])).

tff(c_2318,plain,
    ( r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4'))
    | ~ m1_subset_1('#skF_4',u1_struct_0(k2_yellow_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1383,c_2300])).

tff(c_2334,plain,(
    r1_tarski('#skF_4',k10_lattice3(k2_yellow_1('#skF_2'),'#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2318])).

tff(c_2336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1018,c_2334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:11:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.94/2.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.71  
% 6.94/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.94/2.72  %$ r3_orders_2 > r1_orders_2 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > v1_lattice3 > l1_orders_2 > k13_lattice3 > k10_lattice3 > k2_xboole_0 > #nlpp > u1_struct_0 > k2_yellow_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 6.94/2.72  
% 6.94/2.72  %Foreground sorts:
% 6.94/2.72  
% 6.94/2.72  
% 6.94/2.72  %Background operators:
% 6.94/2.72  
% 6.94/2.72  
% 6.94/2.72  %Foreground operators:
% 6.94/2.72  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 6.94/2.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.94/2.72  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 6.94/2.72  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 6.94/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.94/2.72  tff(k13_lattice3, type, k13_lattice3: ($i * $i * $i) > $i).
% 6.94/2.72  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 6.94/2.72  tff(k10_lattice3, type, k10_lattice3: ($i * $i * $i) > $i).
% 6.94/2.72  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 6.94/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.94/2.72  tff(v1_lattice3, type, v1_lattice3: $i > $o).
% 6.94/2.72  tff('#skF_2', type, '#skF_2': $i).
% 6.94/2.72  tff('#skF_3', type, '#skF_3': $i).
% 6.94/2.72  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 6.94/2.72  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 6.94/2.72  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 6.94/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.94/2.72  tff('#skF_4', type, '#skF_4': $i).
% 6.94/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.94/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.94/2.72  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.94/2.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.94/2.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.94/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.94/2.72  
% 7.15/2.75  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.15/2.75  tff(f_143, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (v1_lattice3(k2_yellow_1(A)) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => r1_tarski(k2_xboole_0(B, C), k10_lattice3(k2_yellow_1(A), B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_1)).
% 7.15/2.75  tff(f_100, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 7.15/2.75  tff(f_54, axiom, (![A, B, C]: (((l1_orders_2(A) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => m1_subset_1(k10_lattice3(A, B, C), u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 7.15/2.75  tff(f_108, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 7.15/2.75  tff(f_66, axiom, (![A, B, C]: (((((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (k13_lattice3(A, B, C) = k10_lattice3(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 7.15/2.75  tff(f_96, axiom, (![A]: (((v5_orders_2(A) & v1_lattice3(A)) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => (![D]: (m1_subset_1(D, u1_struct_0(A)) => ((D = k13_lattice3(A, B, C)) <=> ((r1_orders_2(A, B, D) & r1_orders_2(A, C, D)) & (![E]: (m1_subset_1(E, u1_struct_0(A)) => ((r1_orders_2(A, B, E) & r1_orders_2(A, C, E)) => r1_orders_2(A, D, E)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_yellow_0)).
% 7.15/2.75  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 7.15/2.75  tff(f_116, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 7.15/2.75  tff(f_129, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 7.15/2.75  tff(c_63, plain, (![A_79, C_80, B_81]: (r1_tarski(k2_xboole_0(A_79, C_80), B_81) | ~r1_tarski(C_80, B_81) | ~r1_tarski(A_79, B_81))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.15/2.75  tff(c_46, plain, (~r1_tarski(k2_xboole_0('#skF_3', '#skF_4'), k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.15/2.75  tff(c_67, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_63, c_46])).
% 7.15/2.75  tff(c_68, plain, (~r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_67])).
% 7.15/2.75  tff(c_50, plain, (m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.15/2.75  tff(c_28, plain, (![A_59]: (l1_orders_2(k2_yellow_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_100])).
% 7.15/2.75  tff(c_48, plain, (m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.15/2.75  tff(c_8, plain, (![A_7, B_8, C_9]: (m1_subset_1(k10_lattice3(A_7, B_8, C_9), u1_struct_0(A_7)) | ~m1_subset_1(C_9, u1_struct_0(A_7)) | ~m1_subset_1(B_8, u1_struct_0(A_7)) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.15/2.75  tff(c_36, plain, (![A_60]: (v5_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.15/2.75  tff(c_52, plain, (v1_lattice3(k2_yellow_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.15/2.75  tff(c_125, plain, (![A_96, B_97, C_98]: (k13_lattice3(A_96, B_97, C_98)=k10_lattice3(A_96, B_97, C_98) | ~m1_subset_1(C_98, u1_struct_0(A_96)) | ~m1_subset_1(B_97, u1_struct_0(A_96)) | ~l1_orders_2(A_96) | ~v1_lattice3(A_96) | ~v5_orders_2(A_96))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.15/2.75  tff(c_129, plain, (![B_97]: (k13_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), B_97, '#skF_4') | ~m1_subset_1(B_97, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_125])).
% 7.15/2.75  tff(c_139, plain, (![B_99]: (k13_lattice3(k2_yellow_1('#skF_2'), B_99, '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), B_99, '#skF_4') | ~m1_subset_1(B_99, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_129])).
% 7.15/2.75  tff(c_154, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_139])).
% 7.15/2.75  tff(c_246, plain, (![A_106, B_107, C_108]: (r1_orders_2(A_106, B_107, k13_lattice3(A_106, B_107, C_108)) | ~m1_subset_1(k13_lattice3(A_106, B_107, C_108), u1_struct_0(A_106)) | ~m1_subset_1(C_108, u1_struct_0(A_106)) | ~m1_subset_1(B_107, u1_struct_0(A_106)) | ~l1_orders_2(A_106) | ~v1_lattice3(A_106) | ~v5_orders_2(A_106))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.15/2.75  tff(c_252, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_3', k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_246])).
% 7.15/2.75  tff(c_260, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_50, c_48, c_154, c_252])).
% 7.15/2.75  tff(c_413, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_260])).
% 7.15/2.75  tff(c_416, plain, (~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_413])).
% 7.15/2.75  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_50, c_48, c_416])).
% 7.15/2.75  tff(c_421, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_260])).
% 7.15/2.75  tff(c_54, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 7.15/2.75  tff(c_422, plain, (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(splitRight, [status(thm)], [c_260])).
% 7.15/2.75  tff(c_32, plain, (![A_60]: (v3_orders_2(k2_yellow_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.15/2.75  tff(c_187, plain, (![A_101, B_102, C_103]: (r3_orders_2(A_101, B_102, C_103) | ~r1_orders_2(A_101, B_102, C_103) | ~m1_subset_1(C_103, u1_struct_0(A_101)) | ~m1_subset_1(B_102, u1_struct_0(A_101)) | ~l1_orders_2(A_101) | ~v3_orders_2(A_101) | v2_struct_0(A_101))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.15/2.75  tff(c_191, plain, (![B_102]: (r3_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_187])).
% 7.22/2.75  tff(c_197, plain, (![B_102]: (r3_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_102, '#skF_4') | ~m1_subset_1(B_102, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_191])).
% 7.22/2.75  tff(c_201, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_197])).
% 7.22/2.75  tff(c_40, plain, (![A_61]: (~v2_struct_0(k2_yellow_1(A_61)) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_116])).
% 7.22/2.75  tff(c_204, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_201, c_40])).
% 7.22/2.75  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_204])).
% 7.22/2.75  tff(c_210, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_197])).
% 7.22/2.75  tff(c_4, plain, (![A_4, B_5, C_6]: (r3_orders_2(A_4, B_5, C_6) | ~r1_orders_2(A_4, B_5, C_6) | ~m1_subset_1(C_6, u1_struct_0(A_4)) | ~m1_subset_1(B_5, u1_struct_0(A_4)) | ~l1_orders_2(A_4) | ~v3_orders_2(A_4) | v2_struct_0(A_4))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.22/2.75  tff(c_430, plain, (![B_5]: (r3_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_5, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_422, c_4])).
% 7.22/2.75  tff(c_451, plain, (![B_5]: (r3_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_5, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_430])).
% 7.22/2.75  tff(c_962, plain, (![B_150]: (r3_orders_2(k2_yellow_1('#skF_2'), B_150, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_150, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_150, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_210, c_451])).
% 7.22/2.75  tff(c_44, plain, (![B_66, C_68, A_62]: (r1_tarski(B_66, C_68) | ~r3_orders_2(k2_yellow_1(A_62), B_66, C_68) | ~m1_subset_1(C_68, u1_struct_0(k2_yellow_1(A_62))) | ~m1_subset_1(B_66, u1_struct_0(k2_yellow_1(A_62))) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.22/2.75  tff(c_966, plain, (![B_150]: (r1_tarski(B_150, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_150, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_150, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(resolution, [status(thm)], [c_962, c_44])).
% 7.22/2.75  tff(c_973, plain, (![B_150]: (r1_tarski(B_150, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_150, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_150, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_422, c_966])).
% 7.22/2.75  tff(c_985, plain, (![B_155]: (r1_tarski(B_155, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_155, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_155, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_973])).
% 7.22/2.75  tff(c_1002, plain, (r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_421, c_985])).
% 7.22/2.75  tff(c_1015, plain, (r1_tarski('#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_1002])).
% 7.22/2.75  tff(c_1017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1015])).
% 7.22/2.75  tff(c_1018, plain, (~r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_67])).
% 7.22/2.75  tff(c_1136, plain, (![A_175, B_176, C_177]: (k13_lattice3(A_175, B_176, C_177)=k10_lattice3(A_175, B_176, C_177) | ~m1_subset_1(C_177, u1_struct_0(A_175)) | ~m1_subset_1(B_176, u1_struct_0(A_175)) | ~l1_orders_2(A_175) | ~v1_lattice3(A_175) | ~v5_orders_2(A_175))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.22/2.75  tff(c_1140, plain, (![B_176]: (k13_lattice3(k2_yellow_1('#skF_2'), B_176, '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), B_176, '#skF_4') | ~m1_subset_1(B_176, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_1136])).
% 7.22/2.75  tff(c_1151, plain, (![B_178]: (k13_lattice3(k2_yellow_1('#skF_2'), B_178, '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), B_178, '#skF_4') | ~m1_subset_1(B_178, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_1140])).
% 7.22/2.75  tff(c_1166, plain, (k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')=k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1151])).
% 7.22/2.75  tff(c_1212, plain, (![A_182, B_183, C_184]: (r1_orders_2(A_182, B_183, k13_lattice3(A_182, B_183, C_184)) | ~m1_subset_1(k13_lattice3(A_182, B_183, C_184), u1_struct_0(A_182)) | ~m1_subset_1(C_184, u1_struct_0(A_182)) | ~m1_subset_1(B_183, u1_struct_0(A_182)) | ~l1_orders_2(A_182) | ~v1_lattice3(A_182) | ~v5_orders_2(A_182))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.22/2.75  tff(c_1218, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_3', k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1166, c_1212])).
% 7.22/2.75  tff(c_1226, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_3', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_50, c_48, c_1166, c_1218])).
% 7.22/2.75  tff(c_1239, plain, (~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_1226])).
% 7.22/2.75  tff(c_1282, plain, (~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_1239])).
% 7.22/2.75  tff(c_1286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_50, c_48, c_1282])).
% 7.22/2.75  tff(c_1288, plain, (m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2')))), inference(splitRight, [status(thm)], [c_1226])).
% 7.22/2.75  tff(c_1369, plain, (![A_185, C_186, B_187]: (r1_orders_2(A_185, C_186, k13_lattice3(A_185, B_187, C_186)) | ~m1_subset_1(k13_lattice3(A_185, B_187, C_186), u1_struct_0(A_185)) | ~m1_subset_1(C_186, u1_struct_0(A_185)) | ~m1_subset_1(B_187, u1_struct_0(A_185)) | ~l1_orders_2(A_185) | ~v1_lattice3(A_185) | ~v5_orders_2(A_185))), inference(cnfTransformation, [status(thm)], [f_96])).
% 7.22/2.75  tff(c_1375, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_4', k13_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2'))) | ~m1_subset_1('#skF_3', u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v1_lattice3(k2_yellow_1('#skF_2')) | ~v5_orders_2(k2_yellow_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1166, c_1369])).
% 7.22/2.75  tff(c_1383, plain, (r1_orders_2(k2_yellow_1('#skF_2'), '#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52, c_28, c_50, c_48, c_1288, c_1166, c_1375])).
% 7.22/2.75  tff(c_1075, plain, (![A_167, B_168, C_169]: (r3_orders_2(A_167, B_168, C_169) | ~r1_orders_2(A_167, B_168, C_169) | ~m1_subset_1(C_169, u1_struct_0(A_167)) | ~m1_subset_1(B_168, u1_struct_0(A_167)) | ~l1_orders_2(A_167) | ~v3_orders_2(A_167) | v2_struct_0(A_167))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.22/2.75  tff(c_1079, plain, (![B_168]: (r3_orders_2(k2_yellow_1('#skF_2'), B_168, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_168, '#skF_4') | ~m1_subset_1(B_168, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_48, c_1075])).
% 7.22/2.75  tff(c_1085, plain, (![B_168]: (r3_orders_2(k2_yellow_1('#skF_2'), B_168, '#skF_4') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_168, '#skF_4') | ~m1_subset_1(B_168, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1079])).
% 7.22/2.75  tff(c_1089, plain, (v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1085])).
% 7.22/2.75  tff(c_1092, plain, (v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_1089, c_40])).
% 7.22/2.75  tff(c_1096, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1092])).
% 7.22/2.75  tff(c_1098, plain, (~v2_struct_0(k2_yellow_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1085])).
% 7.22/2.75  tff(c_1344, plain, (![B_5]: (r3_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_5, u1_struct_0(k2_yellow_1('#skF_2'))) | ~l1_orders_2(k2_yellow_1('#skF_2')) | ~v3_orders_2(k2_yellow_1('#skF_2')) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_1288, c_4])).
% 7.22/2.75  tff(c_1362, plain, (![B_5]: (r3_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_5, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_5, u1_struct_0(k2_yellow_1('#skF_2'))) | v2_struct_0(k2_yellow_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_1344])).
% 7.22/2.75  tff(c_2278, plain, (![B_244]: (r3_orders_2(k2_yellow_1('#skF_2'), B_244, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_244, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_244, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_1098, c_1362])).
% 7.22/2.75  tff(c_2282, plain, (![B_244]: (r1_tarski(B_244, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'), u1_struct_0(k2_yellow_1('#skF_2'))) | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_244, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_244, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(resolution, [status(thm)], [c_2278, c_44])).
% 7.22/2.75  tff(c_2289, plain, (![B_244]: (r1_tarski(B_244, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | v1_xboole_0('#skF_2') | ~r1_orders_2(k2_yellow_1('#skF_2'), B_244, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_244, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_1288, c_2282])).
% 7.22/2.75  tff(c_2300, plain, (![B_249]: (r1_tarski(B_249, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~r1_orders_2(k2_yellow_1('#skF_2'), B_249, k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1(B_249, u1_struct_0(k2_yellow_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_54, c_2289])).
% 7.22/2.75  tff(c_2318, plain, (r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4')) | ~m1_subset_1('#skF_4', u1_struct_0(k2_yellow_1('#skF_2')))), inference(resolution, [status(thm)], [c_1383, c_2300])).
% 7.22/2.75  tff(c_2334, plain, (r1_tarski('#skF_4', k10_lattice3(k2_yellow_1('#skF_2'), '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2318])).
% 7.22/2.75  tff(c_2336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1018, c_2334])).
% 7.22/2.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.75  
% 7.22/2.75  Inference rules
% 7.22/2.75  ----------------------
% 7.22/2.75  #Ref     : 0
% 7.22/2.75  #Sup     : 449
% 7.22/2.75  #Fact    : 0
% 7.22/2.75  #Define  : 0
% 7.22/2.75  #Split   : 62
% 7.22/2.75  #Chain   : 0
% 7.22/2.75  #Close   : 0
% 7.22/2.75  
% 7.22/2.75  Ordering : KBO
% 7.22/2.75  
% 7.22/2.75  Simplification rules
% 7.22/2.75  ----------------------
% 7.22/2.75  #Subsume      : 12
% 7.22/2.75  #Demod        : 1008
% 7.22/2.75  #Tautology    : 92
% 7.22/2.75  #SimpNegUnit  : 58
% 7.22/2.75  #BackRed      : 0
% 7.22/2.75  
% 7.22/2.75  #Partial instantiations: 0
% 7.22/2.75  #Strategies tried      : 1
% 7.22/2.75  
% 7.22/2.75  Timing (in seconds)
% 7.22/2.75  ----------------------
% 7.22/2.76  Preprocessing        : 0.52
% 7.22/2.76  Parsing              : 0.26
% 7.22/2.76  CNF conversion       : 0.05
% 7.22/2.76  Main loop            : 1.32
% 7.22/2.76  Inferencing          : 0.43
% 7.22/2.76  Reduction            : 0.49
% 7.22/2.76  Demodulation         : 0.35
% 7.22/2.76  BG Simplification    : 0.05
% 7.22/2.76  Subsumption          : 0.26
% 7.22/2.76  Abstraction          : 0.07
% 7.22/2.76  MUC search           : 0.00
% 7.22/2.76  Cooper               : 0.00
% 7.22/2.76  Total                : 1.91
% 7.22/2.76  Index Insertion      : 0.00
% 7.22/2.76  Index Deletion       : 0.00
% 7.22/2.76  Index Matching       : 0.00
% 7.22/2.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
