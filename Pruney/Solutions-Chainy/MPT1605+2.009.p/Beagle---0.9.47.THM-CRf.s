%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:27 EST 2020

% Result     : Theorem 5.01s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 118 expanded)
%              Number of leaves         :   42 (  61 expanded)
%              Depth                    :   16
%              Number of atoms          :  202 ( 273 expanded)
%              Number of equality atoms :   23 (  51 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r2_lattice3,type,(
    r2_lattice3: ( $i * $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_150,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_117,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_46,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_129,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B,C] :
          ( m1_subset_1(C,u1_struct_0(A))
         => ( r2_lattice3(A,B,C)
          <=> ! [D] :
                ( m1_subset_1(D,u1_struct_0(A))
               => ( r2_hidden(D,B)
                 => r1_orders_2(A,D,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_125,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_113,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_yellow_0)).

tff(f_142,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_yellow_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v2_struct_0(A)
        & l1_struct_0(A) )
     => v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_struct_0)).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_64,plain,(
    r2_hidden(k1_xboole_0,'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_95,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(A_65,B_66)
      | ~ r2_hidden(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_95])).

tff(c_44,plain,(
    ! [A_46] : l1_orders_2(k2_yellow_1(A_46)) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_10,plain,(
    ! [A_7] :
      ( l1_struct_0(A_7)
      | ~ l1_orders_2(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    ! [A_69] :
      ( k1_yellow_0(A_69,k1_xboole_0) = k3_yellow_0(A_69)
      | ~ l1_orders_2(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_109,plain,(
    ! [A_46] : k1_yellow_0(k2_yellow_1(A_46),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_46)) ),
    inference(resolution,[status(thm)],[c_44,c_105])).

tff(c_54,plain,(
    ! [A_48] : u1_struct_0(k2_yellow_1(A_48)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_123,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden('#skF_1'(A_72,B_73,C_74),B_73)
      | r2_lattice3(A_72,B_73,C_74)
      | ~ m1_subset_1(C_74,u1_struct_0(A_72))
      | ~ l1_orders_2(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( ~ r1_tarski(B_5,A_4)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_139,plain,(
    ! [B_82,A_83,C_84] :
      ( ~ r1_tarski(B_82,'#skF_1'(A_83,B_82,C_84))
      | r2_lattice3(A_83,B_82,C_84)
      | ~ m1_subset_1(C_84,u1_struct_0(A_83))
      | ~ l1_orders_2(A_83) ) ),
    inference(resolution,[status(thm)],[c_123,c_6])).

tff(c_145,plain,(
    ! [A_85,C_86] :
      ( r2_lattice3(A_85,k1_xboole_0,C_86)
      | ~ m1_subset_1(C_86,u1_struct_0(A_85))
      | ~ l1_orders_2(A_85) ) ),
    inference(resolution,[status(thm)],[c_2,c_139])).

tff(c_148,plain,(
    ! [A_48,C_86] :
      ( r2_lattice3(k2_yellow_1(A_48),k1_xboole_0,C_86)
      | ~ m1_subset_1(C_86,A_48)
      | ~ l1_orders_2(k2_yellow_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_145])).

tff(c_150,plain,(
    ! [A_48,C_86] :
      ( r2_lattice3(k2_yellow_1(A_48),k1_xboole_0,C_86)
      | ~ m1_subset_1(C_86,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_148])).

tff(c_52,plain,(
    ! [A_47] : v5_orders_2(k2_yellow_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_341,plain,(
    ! [A_166,B_167,C_168] :
      ( m1_subset_1('#skF_2'(A_166,B_167,C_168),u1_struct_0(A_166))
      | k1_yellow_0(A_166,C_168) = B_167
      | ~ r2_lattice3(A_166,C_168,B_167)
      | ~ m1_subset_1(B_167,u1_struct_0(A_166))
      | ~ l1_orders_2(A_166)
      | ~ v5_orders_2(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_349,plain,(
    ! [A_48,B_167,C_168] :
      ( m1_subset_1('#skF_2'(k2_yellow_1(A_48),B_167,C_168),A_48)
      | k1_yellow_0(k2_yellow_1(A_48),C_168) = B_167
      | ~ r2_lattice3(k2_yellow_1(A_48),C_168,B_167)
      | ~ m1_subset_1(B_167,u1_struct_0(k2_yellow_1(A_48)))
      | ~ l1_orders_2(k2_yellow_1(A_48))
      | ~ v5_orders_2(k2_yellow_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_341])).

tff(c_353,plain,(
    ! [A_48,B_167,C_168] :
      ( m1_subset_1('#skF_2'(k2_yellow_1(A_48),B_167,C_168),A_48)
      | k1_yellow_0(k2_yellow_1(A_48),C_168) = B_167
      | ~ r2_lattice3(k2_yellow_1(A_48),C_168,B_167)
      | ~ m1_subset_1(B_167,A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_54,c_349])).

tff(c_48,plain,(
    ! [A_47] : v3_orders_2(k2_yellow_1(A_47)) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_58,plain,(
    ! [A_49,B_53,C_55] :
      ( r3_orders_2(k2_yellow_1(A_49),B_53,C_55)
      | ~ r1_tarski(B_53,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(k2_yellow_1(A_49)))
      | ~ m1_subset_1(B_53,u1_struct_0(k2_yellow_1(A_49)))
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_68,plain,(
    ! [A_49,B_53,C_55] :
      ( r3_orders_2(k2_yellow_1(A_49),B_53,C_55)
      | ~ r1_tarski(B_53,C_55)
      | ~ m1_subset_1(C_55,A_49)
      | ~ m1_subset_1(B_53,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_58])).

tff(c_202,plain,(
    ! [A_114,B_115,C_116] :
      ( r1_orders_2(A_114,B_115,C_116)
      | ~ r3_orders_2(A_114,B_115,C_116)
      | ~ m1_subset_1(C_116,u1_struct_0(A_114))
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v3_orders_2(A_114)
      | v2_struct_0(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_204,plain,(
    ! [A_49,B_53,C_55] :
      ( r1_orders_2(k2_yellow_1(A_49),B_53,C_55)
      | ~ m1_subset_1(C_55,u1_struct_0(k2_yellow_1(A_49)))
      | ~ m1_subset_1(B_53,u1_struct_0(k2_yellow_1(A_49)))
      | ~ l1_orders_2(k2_yellow_1(A_49))
      | ~ v3_orders_2(k2_yellow_1(A_49))
      | v2_struct_0(k2_yellow_1(A_49))
      | ~ r1_tarski(B_53,C_55)
      | ~ m1_subset_1(C_55,A_49)
      | ~ m1_subset_1(B_53,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_68,c_202])).

tff(c_207,plain,(
    ! [A_49,B_53,C_55] :
      ( r1_orders_2(k2_yellow_1(A_49),B_53,C_55)
      | v2_struct_0(k2_yellow_1(A_49))
      | ~ r1_tarski(B_53,C_55)
      | ~ m1_subset_1(C_55,A_49)
      | ~ m1_subset_1(B_53,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_44,c_54,c_54,c_204])).

tff(c_364,plain,(
    ! [A_172,B_173,C_174] :
      ( ~ r1_orders_2(A_172,B_173,'#skF_2'(A_172,B_173,C_174))
      | k1_yellow_0(A_172,C_174) = B_173
      | ~ r2_lattice3(A_172,C_174,B_173)
      | ~ m1_subset_1(B_173,u1_struct_0(A_172))
      | ~ l1_orders_2(A_172)
      | ~ v5_orders_2(A_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_372,plain,(
    ! [A_49,C_174,B_53] :
      ( k1_yellow_0(k2_yellow_1(A_49),C_174) = B_53
      | ~ r2_lattice3(k2_yellow_1(A_49),C_174,B_53)
      | ~ m1_subset_1(B_53,u1_struct_0(k2_yellow_1(A_49)))
      | ~ l1_orders_2(k2_yellow_1(A_49))
      | ~ v5_orders_2(k2_yellow_1(A_49))
      | v2_struct_0(k2_yellow_1(A_49))
      | ~ r1_tarski(B_53,'#skF_2'(k2_yellow_1(A_49),B_53,C_174))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_49),B_53,C_174),A_49)
      | ~ m1_subset_1(B_53,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_207,c_364])).

tff(c_698,plain,(
    ! [A_256,C_257,B_258] :
      ( k1_yellow_0(k2_yellow_1(A_256),C_257) = B_258
      | ~ r2_lattice3(k2_yellow_1(A_256),C_257,B_258)
      | v2_struct_0(k2_yellow_1(A_256))
      | ~ r1_tarski(B_258,'#skF_2'(k2_yellow_1(A_256),B_258,C_257))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_256),B_258,C_257),A_256)
      | ~ m1_subset_1(B_258,A_256)
      | v1_xboole_0(A_256) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_44,c_54,c_372])).

tff(c_703,plain,(
    ! [A_259,C_260] :
      ( k1_yellow_0(k2_yellow_1(A_259),C_260) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_259),C_260,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_259))
      | ~ m1_subset_1('#skF_2'(k2_yellow_1(A_259),k1_xboole_0,C_260),A_259)
      | ~ m1_subset_1(k1_xboole_0,A_259)
      | v1_xboole_0(A_259) ) ),
    inference(resolution,[status(thm)],[c_2,c_698])).

tff(c_730,plain,(
    ! [A_265,C_266] :
      ( v2_struct_0(k2_yellow_1(A_265))
      | v1_xboole_0(A_265)
      | k1_yellow_0(k2_yellow_1(A_265),C_266) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_265),C_266,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_265) ) ),
    inference(resolution,[status(thm)],[c_353,c_703])).

tff(c_734,plain,(
    ! [A_48] :
      ( v2_struct_0(k2_yellow_1(A_48))
      | v1_xboole_0(A_48)
      | k1_yellow_0(k2_yellow_1(A_48),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_48) ) ),
    inference(resolution,[status(thm)],[c_150,c_730])).

tff(c_737,plain,(
    ! [A_267] :
      ( v2_struct_0(k2_yellow_1(A_267))
      | v1_xboole_0(A_267)
      | k3_yellow_0(k2_yellow_1(A_267)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_267) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_734])).

tff(c_110,plain,(
    ! [A_70] :
      ( v1_xboole_0(u1_struct_0(A_70))
      | ~ l1_struct_0(A_70)
      | ~ v2_struct_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_113,plain,(
    ! [A_48] :
      ( v1_xboole_0(A_48)
      | ~ l1_struct_0(k2_yellow_1(A_48))
      | ~ v2_struct_0(k2_yellow_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_110])).

tff(c_742,plain,(
    ! [A_268] :
      ( ~ l1_struct_0(k2_yellow_1(A_268))
      | v1_xboole_0(A_268)
      | k3_yellow_0(k2_yellow_1(A_268)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_268) ) ),
    inference(resolution,[status(thm)],[c_737,c_113])).

tff(c_745,plain,(
    ! [A_268] :
      ( v1_xboole_0(A_268)
      | k3_yellow_0(k2_yellow_1(A_268)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_268)
      | ~ l1_orders_2(k2_yellow_1(A_268)) ) ),
    inference(resolution,[status(thm)],[c_10,c_742])).

tff(c_749,plain,(
    ! [A_269] :
      ( v1_xboole_0(A_269)
      | k3_yellow_0(k2_yellow_1(A_269)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_269) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_745])).

tff(c_62,plain,(
    k3_yellow_0(k2_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_760,plain,
    ( v1_xboole_0('#skF_3')
    | ~ m1_subset_1(k1_xboole_0,'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_62])).

tff(c_767,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_760])).

tff(c_769,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_767])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.01/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/2.15  
% 5.01/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.01/2.16  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_struct_0 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 5.01/2.16  
% 5.01/2.16  %Foreground sorts:
% 5.01/2.16  
% 5.01/2.16  
% 5.01/2.16  %Background operators:
% 5.01/2.16  
% 5.01/2.16  
% 5.01/2.16  %Foreground operators:
% 5.01/2.16  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 5.01/2.16  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.01/2.16  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 5.01/2.16  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 5.01/2.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.01/2.16  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 5.01/2.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.01/2.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.01/2.16  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 5.01/2.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.01/2.16  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 5.01/2.16  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 5.01/2.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.01/2.16  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 5.01/2.16  tff('#skF_3', type, '#skF_3': $i).
% 5.01/2.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.01/2.16  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 5.01/2.16  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 5.01/2.16  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 5.01/2.16  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.01/2.16  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 5.01/2.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.01/2.16  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 5.01/2.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.01/2.16  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 5.01/2.16  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.01/2.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.01/2.16  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.01/2.16  
% 5.16/2.19  tff(f_150, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 5.16/2.19  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 5.16/2.19  tff(f_117, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 5.16/2.19  tff(f_46, axiom, (![A]: (l1_orders_2(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 5.16/2.19  tff(f_79, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 5.16/2.19  tff(f_129, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_yellow_1)).
% 5.16/2.19  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.16/2.19  tff(f_75, axiom, (![A]: (l1_orders_2(A) => (![B, C]: (m1_subset_1(C, u1_struct_0(A)) => (r2_lattice3(A, B, C) <=> (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_hidden(D, B) => r1_orders_2(A, D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 5.16/2.19  tff(f_36, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.16/2.19  tff(f_125, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_yellow_1)).
% 5.16/2.19  tff(f_113, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_yellow_0)).
% 5.16/2.19  tff(f_142, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_yellow_1)).
% 5.16/2.19  tff(f_61, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 5.16/2.19  tff(f_42, axiom, (![A]: ((v2_struct_0(A) & l1_struct_0(A)) => v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_struct_0)).
% 5.16/2.19  tff(c_66, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.16/2.19  tff(c_64, plain, (r2_hidden(k1_xboole_0, '#skF_3')), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.16/2.19  tff(c_95, plain, (![A_65, B_66]: (m1_subset_1(A_65, B_66) | ~r2_hidden(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.16/2.19  tff(c_99, plain, (m1_subset_1(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_64, c_95])).
% 5.16/2.19  tff(c_44, plain, (![A_46]: (l1_orders_2(k2_yellow_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.16/2.19  tff(c_10, plain, (![A_7]: (l1_struct_0(A_7) | ~l1_orders_2(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.16/2.19  tff(c_105, plain, (![A_69]: (k1_yellow_0(A_69, k1_xboole_0)=k3_yellow_0(A_69) | ~l1_orders_2(A_69))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.16/2.19  tff(c_109, plain, (![A_46]: (k1_yellow_0(k2_yellow_1(A_46), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_46)))), inference(resolution, [status(thm)], [c_44, c_105])).
% 5.16/2.19  tff(c_54, plain, (![A_48]: (u1_struct_0(k2_yellow_1(A_48))=A_48)), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.16/2.19  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/2.19  tff(c_123, plain, (![A_72, B_73, C_74]: (r2_hidden('#skF_1'(A_72, B_73, C_74), B_73) | r2_lattice3(A_72, B_73, C_74) | ~m1_subset_1(C_74, u1_struct_0(A_72)) | ~l1_orders_2(A_72))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.16/2.19  tff(c_6, plain, (![B_5, A_4]: (~r1_tarski(B_5, A_4) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.16/2.19  tff(c_139, plain, (![B_82, A_83, C_84]: (~r1_tarski(B_82, '#skF_1'(A_83, B_82, C_84)) | r2_lattice3(A_83, B_82, C_84) | ~m1_subset_1(C_84, u1_struct_0(A_83)) | ~l1_orders_2(A_83))), inference(resolution, [status(thm)], [c_123, c_6])).
% 5.16/2.19  tff(c_145, plain, (![A_85, C_86]: (r2_lattice3(A_85, k1_xboole_0, C_86) | ~m1_subset_1(C_86, u1_struct_0(A_85)) | ~l1_orders_2(A_85))), inference(resolution, [status(thm)], [c_2, c_139])).
% 5.16/2.19  tff(c_148, plain, (![A_48, C_86]: (r2_lattice3(k2_yellow_1(A_48), k1_xboole_0, C_86) | ~m1_subset_1(C_86, A_48) | ~l1_orders_2(k2_yellow_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_145])).
% 5.16/2.19  tff(c_150, plain, (![A_48, C_86]: (r2_lattice3(k2_yellow_1(A_48), k1_xboole_0, C_86) | ~m1_subset_1(C_86, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_148])).
% 5.16/2.19  tff(c_52, plain, (![A_47]: (v5_orders_2(k2_yellow_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.16/2.19  tff(c_341, plain, (![A_166, B_167, C_168]: (m1_subset_1('#skF_2'(A_166, B_167, C_168), u1_struct_0(A_166)) | k1_yellow_0(A_166, C_168)=B_167 | ~r2_lattice3(A_166, C_168, B_167) | ~m1_subset_1(B_167, u1_struct_0(A_166)) | ~l1_orders_2(A_166) | ~v5_orders_2(A_166))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.16/2.19  tff(c_349, plain, (![A_48, B_167, C_168]: (m1_subset_1('#skF_2'(k2_yellow_1(A_48), B_167, C_168), A_48) | k1_yellow_0(k2_yellow_1(A_48), C_168)=B_167 | ~r2_lattice3(k2_yellow_1(A_48), C_168, B_167) | ~m1_subset_1(B_167, u1_struct_0(k2_yellow_1(A_48))) | ~l1_orders_2(k2_yellow_1(A_48)) | ~v5_orders_2(k2_yellow_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_341])).
% 5.16/2.19  tff(c_353, plain, (![A_48, B_167, C_168]: (m1_subset_1('#skF_2'(k2_yellow_1(A_48), B_167, C_168), A_48) | k1_yellow_0(k2_yellow_1(A_48), C_168)=B_167 | ~r2_lattice3(k2_yellow_1(A_48), C_168, B_167) | ~m1_subset_1(B_167, A_48))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_54, c_349])).
% 5.16/2.19  tff(c_48, plain, (![A_47]: (v3_orders_2(k2_yellow_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_125])).
% 5.16/2.19  tff(c_58, plain, (![A_49, B_53, C_55]: (r3_orders_2(k2_yellow_1(A_49), B_53, C_55) | ~r1_tarski(B_53, C_55) | ~m1_subset_1(C_55, u1_struct_0(k2_yellow_1(A_49))) | ~m1_subset_1(B_53, u1_struct_0(k2_yellow_1(A_49))) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_142])).
% 5.16/2.19  tff(c_68, plain, (![A_49, B_53, C_55]: (r3_orders_2(k2_yellow_1(A_49), B_53, C_55) | ~r1_tarski(B_53, C_55) | ~m1_subset_1(C_55, A_49) | ~m1_subset_1(B_53, A_49) | v1_xboole_0(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_58])).
% 5.16/2.19  tff(c_202, plain, (![A_114, B_115, C_116]: (r1_orders_2(A_114, B_115, C_116) | ~r3_orders_2(A_114, B_115, C_116) | ~m1_subset_1(C_116, u1_struct_0(A_114)) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v3_orders_2(A_114) | v2_struct_0(A_114))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.16/2.19  tff(c_204, plain, (![A_49, B_53, C_55]: (r1_orders_2(k2_yellow_1(A_49), B_53, C_55) | ~m1_subset_1(C_55, u1_struct_0(k2_yellow_1(A_49))) | ~m1_subset_1(B_53, u1_struct_0(k2_yellow_1(A_49))) | ~l1_orders_2(k2_yellow_1(A_49)) | ~v3_orders_2(k2_yellow_1(A_49)) | v2_struct_0(k2_yellow_1(A_49)) | ~r1_tarski(B_53, C_55) | ~m1_subset_1(C_55, A_49) | ~m1_subset_1(B_53, A_49) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_68, c_202])).
% 5.16/2.19  tff(c_207, plain, (![A_49, B_53, C_55]: (r1_orders_2(k2_yellow_1(A_49), B_53, C_55) | v2_struct_0(k2_yellow_1(A_49)) | ~r1_tarski(B_53, C_55) | ~m1_subset_1(C_55, A_49) | ~m1_subset_1(B_53, A_49) | v1_xboole_0(A_49))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_44, c_54, c_54, c_204])).
% 5.16/2.19  tff(c_364, plain, (![A_172, B_173, C_174]: (~r1_orders_2(A_172, B_173, '#skF_2'(A_172, B_173, C_174)) | k1_yellow_0(A_172, C_174)=B_173 | ~r2_lattice3(A_172, C_174, B_173) | ~m1_subset_1(B_173, u1_struct_0(A_172)) | ~l1_orders_2(A_172) | ~v5_orders_2(A_172))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.16/2.19  tff(c_372, plain, (![A_49, C_174, B_53]: (k1_yellow_0(k2_yellow_1(A_49), C_174)=B_53 | ~r2_lattice3(k2_yellow_1(A_49), C_174, B_53) | ~m1_subset_1(B_53, u1_struct_0(k2_yellow_1(A_49))) | ~l1_orders_2(k2_yellow_1(A_49)) | ~v5_orders_2(k2_yellow_1(A_49)) | v2_struct_0(k2_yellow_1(A_49)) | ~r1_tarski(B_53, '#skF_2'(k2_yellow_1(A_49), B_53, C_174)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_49), B_53, C_174), A_49) | ~m1_subset_1(B_53, A_49) | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_207, c_364])).
% 5.16/2.19  tff(c_698, plain, (![A_256, C_257, B_258]: (k1_yellow_0(k2_yellow_1(A_256), C_257)=B_258 | ~r2_lattice3(k2_yellow_1(A_256), C_257, B_258) | v2_struct_0(k2_yellow_1(A_256)) | ~r1_tarski(B_258, '#skF_2'(k2_yellow_1(A_256), B_258, C_257)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_256), B_258, C_257), A_256) | ~m1_subset_1(B_258, A_256) | v1_xboole_0(A_256))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_44, c_54, c_372])).
% 5.16/2.19  tff(c_703, plain, (![A_259, C_260]: (k1_yellow_0(k2_yellow_1(A_259), C_260)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_259), C_260, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_259)) | ~m1_subset_1('#skF_2'(k2_yellow_1(A_259), k1_xboole_0, C_260), A_259) | ~m1_subset_1(k1_xboole_0, A_259) | v1_xboole_0(A_259))), inference(resolution, [status(thm)], [c_2, c_698])).
% 5.16/2.19  tff(c_730, plain, (![A_265, C_266]: (v2_struct_0(k2_yellow_1(A_265)) | v1_xboole_0(A_265) | k1_yellow_0(k2_yellow_1(A_265), C_266)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_265), C_266, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_265))), inference(resolution, [status(thm)], [c_353, c_703])).
% 5.16/2.19  tff(c_734, plain, (![A_48]: (v2_struct_0(k2_yellow_1(A_48)) | v1_xboole_0(A_48) | k1_yellow_0(k2_yellow_1(A_48), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_48))), inference(resolution, [status(thm)], [c_150, c_730])).
% 5.16/2.19  tff(c_737, plain, (![A_267]: (v2_struct_0(k2_yellow_1(A_267)) | v1_xboole_0(A_267) | k3_yellow_0(k2_yellow_1(A_267))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_267))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_734])).
% 5.16/2.19  tff(c_110, plain, (![A_70]: (v1_xboole_0(u1_struct_0(A_70)) | ~l1_struct_0(A_70) | ~v2_struct_0(A_70))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.16/2.19  tff(c_113, plain, (![A_48]: (v1_xboole_0(A_48) | ~l1_struct_0(k2_yellow_1(A_48)) | ~v2_struct_0(k2_yellow_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_110])).
% 5.16/2.19  tff(c_742, plain, (![A_268]: (~l1_struct_0(k2_yellow_1(A_268)) | v1_xboole_0(A_268) | k3_yellow_0(k2_yellow_1(A_268))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_268))), inference(resolution, [status(thm)], [c_737, c_113])).
% 5.16/2.19  tff(c_745, plain, (![A_268]: (v1_xboole_0(A_268) | k3_yellow_0(k2_yellow_1(A_268))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_268) | ~l1_orders_2(k2_yellow_1(A_268)))), inference(resolution, [status(thm)], [c_10, c_742])).
% 5.16/2.19  tff(c_749, plain, (![A_269]: (v1_xboole_0(A_269) | k3_yellow_0(k2_yellow_1(A_269))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_269))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_745])).
% 5.16/2.19  tff(c_62, plain, (k3_yellow_0(k2_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_150])).
% 5.16/2.19  tff(c_760, plain, (v1_xboole_0('#skF_3') | ~m1_subset_1(k1_xboole_0, '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_749, c_62])).
% 5.16/2.19  tff(c_767, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_760])).
% 5.16/2.19  tff(c_769, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_767])).
% 5.16/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.16/2.19  
% 5.16/2.19  Inference rules
% 5.16/2.19  ----------------------
% 5.16/2.19  #Ref     : 0
% 5.16/2.19  #Sup     : 124
% 5.16/2.19  #Fact    : 0
% 5.16/2.19  #Define  : 0
% 5.16/2.19  #Split   : 0
% 5.16/2.19  #Chain   : 0
% 5.16/2.19  #Close   : 0
% 5.16/2.19  
% 5.16/2.19  Ordering : KBO
% 5.16/2.19  
% 5.16/2.19  Simplification rules
% 5.16/2.19  ----------------------
% 5.16/2.19  #Subsume      : 18
% 5.16/2.19  #Demod        : 173
% 5.16/2.19  #Tautology    : 22
% 5.16/2.19  #SimpNegUnit  : 1
% 5.16/2.19  #BackRed      : 0
% 5.16/2.19  
% 5.16/2.19  #Partial instantiations: 0
% 5.16/2.19  #Strategies tried      : 1
% 5.16/2.19  
% 5.16/2.19  Timing (in seconds)
% 5.16/2.19  ----------------------
% 5.16/2.19  Preprocessing        : 0.55
% 5.16/2.19  Parsing              : 0.28
% 5.16/2.19  CNF conversion       : 0.04
% 5.16/2.19  Main loop            : 0.74
% 5.16/2.19  Inferencing          : 0.32
% 5.16/2.19  Reduction            : 0.21
% 5.16/2.19  Demodulation         : 0.15
% 5.16/2.19  BG Simplification    : 0.04
% 5.16/2.19  Subsumption          : 0.12
% 5.16/2.19  Abstraction          : 0.04
% 5.16/2.19  MUC search           : 0.00
% 5.16/2.20  Cooper               : 0.00
% 5.16/2.20  Total                : 1.35
% 5.16/2.20  Index Insertion      : 0.00
% 5.16/2.20  Index Deletion       : 0.00
% 5.16/2.20  Index Matching       : 0.00
% 5.16/2.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
