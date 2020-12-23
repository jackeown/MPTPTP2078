%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:26 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.39s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 105 expanded)
%              Number of leaves         :   39 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  179 ( 246 expanded)
%              Number of equality atoms :   21 (  47 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_147,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_59,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_126,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_114,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_93,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

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

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( ~ v2_struct_0(A)
        & v3_orders_2(A)
        & l1_orders_2(A)
        & m1_subset_1(B,u1_struct_0(A))
        & m1_subset_1(C,u1_struct_0(A)) )
     => ( r3_orders_2(A,B,C)
      <=> r1_orders_2(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

tff(f_122,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_64,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_117,plain,(
    ! [B_61,A_62] :
      ( m1_subset_1(B_61,A_62)
      | ~ r2_hidden(B_61,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_123,plain,
    ( m1_subset_1(k1_xboole_0,'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_117])).

tff(c_127,plain,(
    m1_subset_1(k1_xboole_0,'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_123])).

tff(c_40,plain,(
    ! [A_33] : l1_orders_2(k2_yellow_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_96,plain,(
    ! [A_53] :
      ( k1_yellow_0(A_53,k1_xboole_0) = k3_yellow_0(A_53)
      | ~ l1_orders_2(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_100,plain,(
    ! [A_33] : k1_yellow_0(k2_yellow_1(A_33),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_33)) ),
    inference(resolution,[status(thm)],[c_40,c_96])).

tff(c_54,plain,(
    ! [A_36] : u1_struct_0(k2_yellow_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_144,plain,(
    ! [A_67,B_68] :
      ( r2_lattice3(A_67,k1_xboole_0,B_68)
      | ~ m1_subset_1(B_68,u1_struct_0(A_67))
      | ~ l1_orders_2(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_151,plain,(
    ! [A_36,B_68] :
      ( r2_lattice3(k2_yellow_1(A_36),k1_xboole_0,B_68)
      | ~ m1_subset_1(B_68,A_36)
      | ~ l1_orders_2(k2_yellow_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_144])).

tff(c_154,plain,(
    ! [A_36,B_68] :
      ( r2_lattice3(k2_yellow_1(A_36),k1_xboole_0,B_68)
      | ~ m1_subset_1(B_68,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_151])).

tff(c_48,plain,(
    ! [A_34] : v5_orders_2(k2_yellow_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_282,plain,(
    ! [A_130,B_131,C_132] :
      ( m1_subset_1('#skF_1'(A_130,B_131,C_132),u1_struct_0(A_130))
      | k1_yellow_0(A_130,C_132) = B_131
      | ~ r2_lattice3(A_130,C_132,B_131)
      | ~ m1_subset_1(B_131,u1_struct_0(A_130))
      | ~ l1_orders_2(A_130)
      | ~ v5_orders_2(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_296,plain,(
    ! [A_36,B_131,C_132] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_36),B_131,C_132),A_36)
      | k1_yellow_0(k2_yellow_1(A_36),C_132) = B_131
      | ~ r2_lattice3(k2_yellow_1(A_36),C_132,B_131)
      | ~ m1_subset_1(B_131,u1_struct_0(k2_yellow_1(A_36)))
      | ~ l1_orders_2(k2_yellow_1(A_36))
      | ~ v5_orders_2(k2_yellow_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_282])).

tff(c_302,plain,(
    ! [A_36,B_131,C_132] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_36),B_131,C_132),A_36)
      | k1_yellow_0(k2_yellow_1(A_36),C_132) = B_131
      | ~ r2_lattice3(k2_yellow_1(A_36),C_132,B_131)
      | ~ m1_subset_1(B_131,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_54,c_296])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_34] : v3_orders_2(k2_yellow_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_58,plain,(
    ! [A_37,B_41,C_43] :
      ( r3_orders_2(k2_yellow_1(A_37),B_41,C_43)
      | ~ r1_tarski(B_41,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(k2_yellow_1(A_37)))
      | ~ m1_subset_1(B_41,u1_struct_0(k2_yellow_1(A_37)))
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_68,plain,(
    ! [A_37,B_41,C_43] :
      ( r3_orders_2(k2_yellow_1(A_37),B_41,C_43)
      | ~ r1_tarski(B_41,C_43)
      | ~ m1_subset_1(C_43,A_37)
      | ~ m1_subset_1(B_41,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_54,c_58])).

tff(c_213,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_orders_2(A_100,B_101,C_102)
      | ~ r3_orders_2(A_100,B_101,C_102)
      | ~ m1_subset_1(C_102,u1_struct_0(A_100))
      | ~ m1_subset_1(B_101,u1_struct_0(A_100))
      | ~ l1_orders_2(A_100)
      | ~ v3_orders_2(A_100)
      | v2_struct_0(A_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    ! [A_37,B_41,C_43] :
      ( r1_orders_2(k2_yellow_1(A_37),B_41,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(k2_yellow_1(A_37)))
      | ~ m1_subset_1(B_41,u1_struct_0(k2_yellow_1(A_37)))
      | ~ l1_orders_2(k2_yellow_1(A_37))
      | ~ v3_orders_2(k2_yellow_1(A_37))
      | v2_struct_0(k2_yellow_1(A_37))
      | ~ r1_tarski(B_41,C_43)
      | ~ m1_subset_1(C_43,A_37)
      | ~ m1_subset_1(B_41,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_68,c_213])).

tff(c_223,plain,(
    ! [A_37,B_41,C_43] :
      ( r1_orders_2(k2_yellow_1(A_37),B_41,C_43)
      | v2_struct_0(k2_yellow_1(A_37))
      | ~ r1_tarski(B_41,C_43)
      | ~ m1_subset_1(C_43,A_37)
      | ~ m1_subset_1(B_41,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40,c_54,c_54,c_217])).

tff(c_323,plain,(
    ! [A_139,B_140,C_141] :
      ( ~ r1_orders_2(A_139,B_140,'#skF_1'(A_139,B_140,C_141))
      | k1_yellow_0(A_139,C_141) = B_140
      | ~ r2_lattice3(A_139,C_141,B_140)
      | ~ m1_subset_1(B_140,u1_struct_0(A_139))
      | ~ l1_orders_2(A_139)
      | ~ v5_orders_2(A_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_327,plain,(
    ! [A_37,C_141,B_41] :
      ( k1_yellow_0(k2_yellow_1(A_37),C_141) = B_41
      | ~ r2_lattice3(k2_yellow_1(A_37),C_141,B_41)
      | ~ m1_subset_1(B_41,u1_struct_0(k2_yellow_1(A_37)))
      | ~ l1_orders_2(k2_yellow_1(A_37))
      | ~ v5_orders_2(k2_yellow_1(A_37))
      | v2_struct_0(k2_yellow_1(A_37))
      | ~ r1_tarski(B_41,'#skF_1'(k2_yellow_1(A_37),B_41,C_141))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_37),B_41,C_141),A_37)
      | ~ m1_subset_1(B_41,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_223,c_323])).

tff(c_622,plain,(
    ! [A_236,C_237,B_238] :
      ( k1_yellow_0(k2_yellow_1(A_236),C_237) = B_238
      | ~ r2_lattice3(k2_yellow_1(A_236),C_237,B_238)
      | v2_struct_0(k2_yellow_1(A_236))
      | ~ r1_tarski(B_238,'#skF_1'(k2_yellow_1(A_236),B_238,C_237))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_236),B_238,C_237),A_236)
      | ~ m1_subset_1(B_238,A_236)
      | v1_xboole_0(A_236) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40,c_54,c_327])).

tff(c_627,plain,(
    ! [A_239,C_240] :
      ( k1_yellow_0(k2_yellow_1(A_239),C_240) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_239),C_240,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_239))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_239),k1_xboole_0,C_240),A_239)
      | ~ m1_subset_1(k1_xboole_0,A_239)
      | v1_xboole_0(A_239) ) ),
    inference(resolution,[status(thm)],[c_2,c_622])).

tff(c_654,plain,(
    ! [A_245,C_246] :
      ( v2_struct_0(k2_yellow_1(A_245))
      | v1_xboole_0(A_245)
      | k1_yellow_0(k2_yellow_1(A_245),C_246) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_245),C_246,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_245) ) ),
    inference(resolution,[status(thm)],[c_302,c_627])).

tff(c_662,plain,(
    ! [A_36] :
      ( v2_struct_0(k2_yellow_1(A_36))
      | v1_xboole_0(A_36)
      | k1_yellow_0(k2_yellow_1(A_36),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_36) ) ),
    inference(resolution,[status(thm)],[c_154,c_654])).

tff(c_667,plain,(
    ! [A_247] :
      ( v2_struct_0(k2_yellow_1(A_247))
      | v1_xboole_0(A_247)
      | k3_yellow_0(k2_yellow_1(A_247)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_247) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_662])).

tff(c_52,plain,(
    ! [A_35] :
      ( ~ v2_struct_0(k2_yellow_1(A_35))
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_672,plain,(
    ! [A_248] :
      ( v1_xboole_0(A_248)
      | k3_yellow_0(k2_yellow_1(A_248)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_248) ) ),
    inference(resolution,[status(thm)],[c_667,c_52])).

tff(c_62,plain,(
    k3_yellow_0(k2_yellow_1('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_686,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_672,c_62])).

tff(c_693,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_686])).

tff(c_695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:04:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.49  
% 3.39/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.49  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.39/1.49  
% 3.39/1.49  %Foreground sorts:
% 3.39/1.49  
% 3.39/1.49  
% 3.39/1.49  %Background operators:
% 3.39/1.49  
% 3.39/1.49  
% 3.39/1.49  %Foreground operators:
% 3.39/1.49  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.39/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.39/1.49  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.39/1.49  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.39/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.39/1.49  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.39/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.49  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.39/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.49  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.39/1.49  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.39/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.49  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.39/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.39/1.49  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.39/1.49  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.39/1.49  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.39/1.49  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.39/1.49  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.39/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.49  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.39/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.49  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.39/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.39/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.39/1.49  
% 3.39/1.51  tff(f_147, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.39/1.51  tff(f_40, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.39/1.51  tff(f_106, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.39/1.51  tff(f_59, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.39/1.51  tff(f_126, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.39/1.51  tff(f_102, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.39/1.51  tff(f_114, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.39/1.51  tff(f_93, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 3.39/1.51  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.39/1.51  tff(f_139, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.39/1.51  tff(f_55, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.39/1.51  tff(f_122, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.39/1.51  tff(c_66, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.39/1.51  tff(c_64, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.39/1.51  tff(c_117, plain, (![B_61, A_62]: (m1_subset_1(B_61, A_62) | ~r2_hidden(B_61, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.39/1.51  tff(c_123, plain, (m1_subset_1(k1_xboole_0, '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_117])).
% 3.39/1.51  tff(c_127, plain, (m1_subset_1(k1_xboole_0, '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_123])).
% 3.39/1.51  tff(c_40, plain, (![A_33]: (l1_orders_2(k2_yellow_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.39/1.51  tff(c_96, plain, (![A_53]: (k1_yellow_0(A_53, k1_xboole_0)=k3_yellow_0(A_53) | ~l1_orders_2(A_53))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.39/1.51  tff(c_100, plain, (![A_33]: (k1_yellow_0(k2_yellow_1(A_33), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_33)))), inference(resolution, [status(thm)], [c_40, c_96])).
% 3.39/1.51  tff(c_54, plain, (![A_36]: (u1_struct_0(k2_yellow_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.39/1.51  tff(c_144, plain, (![A_67, B_68]: (r2_lattice3(A_67, k1_xboole_0, B_68) | ~m1_subset_1(B_68, u1_struct_0(A_67)) | ~l1_orders_2(A_67))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.39/1.51  tff(c_151, plain, (![A_36, B_68]: (r2_lattice3(k2_yellow_1(A_36), k1_xboole_0, B_68) | ~m1_subset_1(B_68, A_36) | ~l1_orders_2(k2_yellow_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_144])).
% 3.39/1.51  tff(c_154, plain, (![A_36, B_68]: (r2_lattice3(k2_yellow_1(A_36), k1_xboole_0, B_68) | ~m1_subset_1(B_68, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_151])).
% 3.39/1.51  tff(c_48, plain, (![A_34]: (v5_orders_2(k2_yellow_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.39/1.51  tff(c_282, plain, (![A_130, B_131, C_132]: (m1_subset_1('#skF_1'(A_130, B_131, C_132), u1_struct_0(A_130)) | k1_yellow_0(A_130, C_132)=B_131 | ~r2_lattice3(A_130, C_132, B_131) | ~m1_subset_1(B_131, u1_struct_0(A_130)) | ~l1_orders_2(A_130) | ~v5_orders_2(A_130))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.39/1.51  tff(c_296, plain, (![A_36, B_131, C_132]: (m1_subset_1('#skF_1'(k2_yellow_1(A_36), B_131, C_132), A_36) | k1_yellow_0(k2_yellow_1(A_36), C_132)=B_131 | ~r2_lattice3(k2_yellow_1(A_36), C_132, B_131) | ~m1_subset_1(B_131, u1_struct_0(k2_yellow_1(A_36))) | ~l1_orders_2(k2_yellow_1(A_36)) | ~v5_orders_2(k2_yellow_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_282])).
% 3.39/1.51  tff(c_302, plain, (![A_36, B_131, C_132]: (m1_subset_1('#skF_1'(k2_yellow_1(A_36), B_131, C_132), A_36) | k1_yellow_0(k2_yellow_1(A_36), C_132)=B_131 | ~r2_lattice3(k2_yellow_1(A_36), C_132, B_131) | ~m1_subset_1(B_131, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_54, c_296])).
% 3.39/1.51  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.39/1.51  tff(c_44, plain, (![A_34]: (v3_orders_2(k2_yellow_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.39/1.51  tff(c_58, plain, (![A_37, B_41, C_43]: (r3_orders_2(k2_yellow_1(A_37), B_41, C_43) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, u1_struct_0(k2_yellow_1(A_37))) | ~m1_subset_1(B_41, u1_struct_0(k2_yellow_1(A_37))) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.39/1.51  tff(c_68, plain, (![A_37, B_41, C_43]: (r3_orders_2(k2_yellow_1(A_37), B_41, C_43) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, A_37) | ~m1_subset_1(B_41, A_37) | v1_xboole_0(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_54, c_58])).
% 3.39/1.51  tff(c_213, plain, (![A_100, B_101, C_102]: (r1_orders_2(A_100, B_101, C_102) | ~r3_orders_2(A_100, B_101, C_102) | ~m1_subset_1(C_102, u1_struct_0(A_100)) | ~m1_subset_1(B_101, u1_struct_0(A_100)) | ~l1_orders_2(A_100) | ~v3_orders_2(A_100) | v2_struct_0(A_100))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.39/1.51  tff(c_217, plain, (![A_37, B_41, C_43]: (r1_orders_2(k2_yellow_1(A_37), B_41, C_43) | ~m1_subset_1(C_43, u1_struct_0(k2_yellow_1(A_37))) | ~m1_subset_1(B_41, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)) | ~v3_orders_2(k2_yellow_1(A_37)) | v2_struct_0(k2_yellow_1(A_37)) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, A_37) | ~m1_subset_1(B_41, A_37) | v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_68, c_213])).
% 3.39/1.51  tff(c_223, plain, (![A_37, B_41, C_43]: (r1_orders_2(k2_yellow_1(A_37), B_41, C_43) | v2_struct_0(k2_yellow_1(A_37)) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, A_37) | ~m1_subset_1(B_41, A_37) | v1_xboole_0(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40, c_54, c_54, c_217])).
% 3.39/1.51  tff(c_323, plain, (![A_139, B_140, C_141]: (~r1_orders_2(A_139, B_140, '#skF_1'(A_139, B_140, C_141)) | k1_yellow_0(A_139, C_141)=B_140 | ~r2_lattice3(A_139, C_141, B_140) | ~m1_subset_1(B_140, u1_struct_0(A_139)) | ~l1_orders_2(A_139) | ~v5_orders_2(A_139))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.39/1.51  tff(c_327, plain, (![A_37, C_141, B_41]: (k1_yellow_0(k2_yellow_1(A_37), C_141)=B_41 | ~r2_lattice3(k2_yellow_1(A_37), C_141, B_41) | ~m1_subset_1(B_41, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)) | ~v5_orders_2(k2_yellow_1(A_37)) | v2_struct_0(k2_yellow_1(A_37)) | ~r1_tarski(B_41, '#skF_1'(k2_yellow_1(A_37), B_41, C_141)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_37), B_41, C_141), A_37) | ~m1_subset_1(B_41, A_37) | v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_223, c_323])).
% 3.39/1.51  tff(c_622, plain, (![A_236, C_237, B_238]: (k1_yellow_0(k2_yellow_1(A_236), C_237)=B_238 | ~r2_lattice3(k2_yellow_1(A_236), C_237, B_238) | v2_struct_0(k2_yellow_1(A_236)) | ~r1_tarski(B_238, '#skF_1'(k2_yellow_1(A_236), B_238, C_237)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_236), B_238, C_237), A_236) | ~m1_subset_1(B_238, A_236) | v1_xboole_0(A_236))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40, c_54, c_327])).
% 3.39/1.51  tff(c_627, plain, (![A_239, C_240]: (k1_yellow_0(k2_yellow_1(A_239), C_240)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_239), C_240, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_239)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_239), k1_xboole_0, C_240), A_239) | ~m1_subset_1(k1_xboole_0, A_239) | v1_xboole_0(A_239))), inference(resolution, [status(thm)], [c_2, c_622])).
% 3.39/1.51  tff(c_654, plain, (![A_245, C_246]: (v2_struct_0(k2_yellow_1(A_245)) | v1_xboole_0(A_245) | k1_yellow_0(k2_yellow_1(A_245), C_246)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_245), C_246, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_245))), inference(resolution, [status(thm)], [c_302, c_627])).
% 3.39/1.51  tff(c_662, plain, (![A_36]: (v2_struct_0(k2_yellow_1(A_36)) | v1_xboole_0(A_36) | k1_yellow_0(k2_yellow_1(A_36), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_36))), inference(resolution, [status(thm)], [c_154, c_654])).
% 3.39/1.51  tff(c_667, plain, (![A_247]: (v2_struct_0(k2_yellow_1(A_247)) | v1_xboole_0(A_247) | k3_yellow_0(k2_yellow_1(A_247))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_247))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_662])).
% 3.39/1.51  tff(c_52, plain, (![A_35]: (~v2_struct_0(k2_yellow_1(A_35)) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.39/1.51  tff(c_672, plain, (![A_248]: (v1_xboole_0(A_248) | k3_yellow_0(k2_yellow_1(A_248))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_248))), inference(resolution, [status(thm)], [c_667, c_52])).
% 3.39/1.51  tff(c_62, plain, (k3_yellow_0(k2_yellow_1('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.39/1.51  tff(c_686, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_672, c_62])).
% 3.39/1.51  tff(c_693, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_686])).
% 3.39/1.51  tff(c_695, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_693])).
% 3.39/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.39/1.51  
% 3.39/1.51  Inference rules
% 3.39/1.51  ----------------------
% 3.39/1.51  #Ref     : 0
% 3.39/1.51  #Sup     : 121
% 3.39/1.51  #Fact    : 0
% 3.39/1.51  #Define  : 0
% 3.39/1.51  #Split   : 0
% 3.39/1.51  #Chain   : 0
% 3.39/1.51  #Close   : 0
% 3.39/1.51  
% 3.39/1.51  Ordering : KBO
% 3.39/1.51  
% 3.39/1.51  Simplification rules
% 3.39/1.51  ----------------------
% 3.39/1.51  #Subsume      : 17
% 3.39/1.51  #Demod        : 133
% 3.39/1.51  #Tautology    : 27
% 3.39/1.51  #SimpNegUnit  : 2
% 3.39/1.51  #BackRed      : 0
% 3.39/1.51  
% 3.39/1.51  #Partial instantiations: 0
% 3.39/1.51  #Strategies tried      : 1
% 3.39/1.51  
% 3.39/1.51  Timing (in seconds)
% 3.39/1.51  ----------------------
% 3.39/1.51  Preprocessing        : 0.34
% 3.39/1.51  Parsing              : 0.18
% 3.39/1.51  CNF conversion       : 0.02
% 3.39/1.51  Main loop            : 0.41
% 3.39/1.51  Inferencing          : 0.17
% 3.39/1.51  Reduction            : 0.12
% 3.39/1.51  Demodulation         : 0.08
% 3.39/1.51  BG Simplification    : 0.02
% 3.39/1.51  Subsumption          : 0.08
% 3.39/1.51  Abstraction          : 0.02
% 3.39/1.51  MUC search           : 0.00
% 3.39/1.51  Cooper               : 0.00
% 3.39/1.51  Total                : 0.79
% 3.39/1.51  Index Insertion      : 0.00
% 3.39/1.51  Index Deletion       : 0.00
% 3.39/1.51  Index Matching       : 0.00
% 3.39/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
