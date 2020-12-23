%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:27 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 102 expanded)
%              Number of leaves         :   39 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  172 ( 235 expanded)
%              Number of equality atoms :   21 (  46 expanded)
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

tff(f_138,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ( r2_hidden(k1_xboole_0,A)
         => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_97,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & l1_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_1)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => k3_yellow_0(A) = k1_yellow_0(A,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_yellow_0)).

tff(f_117,axiom,(
    ! [A] :
      ( u1_struct_0(k2_yellow_1(A)) = A
      & u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_yellow_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_orders_2(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ( r2_lattice3(A,k1_xboole_0,B)
            & r1_lattice3(A,k1_xboole_0,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

tff(f_105,axiom,(
    ! [A] :
      ( v1_orders_2(k2_yellow_1(A))
      & v3_orders_2(k2_yellow_1(A))
      & v4_orders_2(k2_yellow_1(A))
      & v5_orders_2(k2_yellow_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow_1)).

tff(f_84,axiom,(
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

tff(f_130,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(k2_yellow_1(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(k2_yellow_1(A)))
             => ( r3_orders_2(k2_yellow_1(A),B,C)
              <=> r1_tarski(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow_1)).

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

tff(f_113,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( ~ v2_struct_0(k2_yellow_1(A))
        & v1_orders_2(k2_yellow_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_yellow_1)).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_58,plain,(
    r2_hidden(k1_xboole_0,'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_90,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(A_53,B_54)
      | ~ r2_hidden(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    m1_subset_1(k1_xboole_0,'#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_90])).

tff(c_34,plain,(
    ! [A_33] : l1_orders_2(k2_yellow_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_95,plain,(
    ! [A_55] :
      ( k1_yellow_0(A_55,k1_xboole_0) = k3_yellow_0(A_55)
      | ~ l1_orders_2(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_99,plain,(
    ! [A_33] : k1_yellow_0(k2_yellow_1(A_33),k1_xboole_0) = k3_yellow_0(k2_yellow_1(A_33)) ),
    inference(resolution,[status(thm)],[c_34,c_95])).

tff(c_48,plain,(
    ! [A_36] : u1_struct_0(k2_yellow_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_100,plain,(
    ! [A_56,B_57] :
      ( r2_lattice3(A_56,k1_xboole_0,B_57)
      | ~ m1_subset_1(B_57,u1_struct_0(A_56))
      | ~ l1_orders_2(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_103,plain,(
    ! [A_36,B_57] :
      ( r2_lattice3(k2_yellow_1(A_36),k1_xboole_0,B_57)
      | ~ m1_subset_1(B_57,A_36)
      | ~ l1_orders_2(k2_yellow_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_100])).

tff(c_105,plain,(
    ! [A_36,B_57] :
      ( r2_lattice3(k2_yellow_1(A_36),k1_xboole_0,B_57)
      | ~ m1_subset_1(B_57,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_103])).

tff(c_42,plain,(
    ! [A_34] : v5_orders_2(k2_yellow_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_222,plain,(
    ! [A_114,B_115,C_116] :
      ( m1_subset_1('#skF_1'(A_114,B_115,C_116),u1_struct_0(A_114))
      | k1_yellow_0(A_114,C_116) = B_115
      | ~ r2_lattice3(A_114,C_116,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0(A_114))
      | ~ l1_orders_2(A_114)
      | ~ v5_orders_2(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_233,plain,(
    ! [A_36,B_115,C_116] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_36),B_115,C_116),A_36)
      | k1_yellow_0(k2_yellow_1(A_36),C_116) = B_115
      | ~ r2_lattice3(k2_yellow_1(A_36),C_116,B_115)
      | ~ m1_subset_1(B_115,u1_struct_0(k2_yellow_1(A_36)))
      | ~ l1_orders_2(k2_yellow_1(A_36))
      | ~ v5_orders_2(k2_yellow_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_222])).

tff(c_238,plain,(
    ! [A_36,B_115,C_116] :
      ( m1_subset_1('#skF_1'(k2_yellow_1(A_36),B_115,C_116),A_36)
      | k1_yellow_0(k2_yellow_1(A_36),C_116) = B_115
      | ~ r2_lattice3(k2_yellow_1(A_36),C_116,B_115)
      | ~ m1_subset_1(B_115,A_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_48,c_233])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_34] : v3_orders_2(k2_yellow_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_52,plain,(
    ! [A_37,B_41,C_43] :
      ( r3_orders_2(k2_yellow_1(A_37),B_41,C_43)
      | ~ r1_tarski(B_41,C_43)
      | ~ m1_subset_1(C_43,u1_struct_0(k2_yellow_1(A_37)))
      | ~ m1_subset_1(B_41,u1_struct_0(k2_yellow_1(A_37)))
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_62,plain,(
    ! [A_37,B_41,C_43] :
      ( r3_orders_2(k2_yellow_1(A_37),B_41,C_43)
      | ~ r1_tarski(B_41,C_43)
      | ~ m1_subset_1(C_43,A_37)
      | ~ m1_subset_1(B_41,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_52])).

tff(c_143,plain,(
    ! [A_75,B_76,C_77] :
      ( r1_orders_2(A_75,B_76,C_77)
      | ~ r3_orders_2(A_75,B_76,C_77)
      | ~ m1_subset_1(C_77,u1_struct_0(A_75))
      | ~ m1_subset_1(B_76,u1_struct_0(A_75))
      | ~ l1_orders_2(A_75)
      | ~ v3_orders_2(A_75)
      | v2_struct_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_145,plain,(
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
    inference(resolution,[status(thm)],[c_62,c_143])).

tff(c_148,plain,(
    ! [A_37,B_41,C_43] :
      ( r1_orders_2(k2_yellow_1(A_37),B_41,C_43)
      | v2_struct_0(k2_yellow_1(A_37))
      | ~ r1_tarski(B_41,C_43)
      | ~ m1_subset_1(C_43,A_37)
      | ~ m1_subset_1(B_41,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34,c_48,c_48,c_145])).

tff(c_214,plain,(
    ! [A_111,B_112,C_113] :
      ( ~ r1_orders_2(A_111,B_112,'#skF_1'(A_111,B_112,C_113))
      | k1_yellow_0(A_111,C_113) = B_112
      | ~ r2_lattice3(A_111,C_113,B_112)
      | ~ m1_subset_1(B_112,u1_struct_0(A_111))
      | ~ l1_orders_2(A_111)
      | ~ v5_orders_2(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_218,plain,(
    ! [A_37,C_113,B_41] :
      ( k1_yellow_0(k2_yellow_1(A_37),C_113) = B_41
      | ~ r2_lattice3(k2_yellow_1(A_37),C_113,B_41)
      | ~ m1_subset_1(B_41,u1_struct_0(k2_yellow_1(A_37)))
      | ~ l1_orders_2(k2_yellow_1(A_37))
      | ~ v5_orders_2(k2_yellow_1(A_37))
      | v2_struct_0(k2_yellow_1(A_37))
      | ~ r1_tarski(B_41,'#skF_1'(k2_yellow_1(A_37),B_41,C_113))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_37),B_41,C_113),A_37)
      | ~ m1_subset_1(B_41,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_148,c_214])).

tff(c_401,plain,(
    ! [A_183,C_184,B_185] :
      ( k1_yellow_0(k2_yellow_1(A_183),C_184) = B_185
      | ~ r2_lattice3(k2_yellow_1(A_183),C_184,B_185)
      | v2_struct_0(k2_yellow_1(A_183))
      | ~ r1_tarski(B_185,'#skF_1'(k2_yellow_1(A_183),B_185,C_184))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_183),B_185,C_184),A_183)
      | ~ m1_subset_1(B_185,A_183)
      | v1_xboole_0(A_183) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_34,c_48,c_218])).

tff(c_406,plain,(
    ! [A_186,C_187] :
      ( k1_yellow_0(k2_yellow_1(A_186),C_187) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_186),C_187,k1_xboole_0)
      | v2_struct_0(k2_yellow_1(A_186))
      | ~ m1_subset_1('#skF_1'(k2_yellow_1(A_186),k1_xboole_0,C_187),A_186)
      | ~ m1_subset_1(k1_xboole_0,A_186)
      | v1_xboole_0(A_186) ) ),
    inference(resolution,[status(thm)],[c_2,c_401])).

tff(c_417,plain,(
    ! [A_188,C_189] :
      ( v2_struct_0(k2_yellow_1(A_188))
      | v1_xboole_0(A_188)
      | k1_yellow_0(k2_yellow_1(A_188),C_189) = k1_xboole_0
      | ~ r2_lattice3(k2_yellow_1(A_188),C_189,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,A_188) ) ),
    inference(resolution,[status(thm)],[c_238,c_406])).

tff(c_421,plain,(
    ! [A_36] :
      ( v2_struct_0(k2_yellow_1(A_36))
      | v1_xboole_0(A_36)
      | k1_yellow_0(k2_yellow_1(A_36),k1_xboole_0) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_36) ) ),
    inference(resolution,[status(thm)],[c_105,c_417])).

tff(c_440,plain,(
    ! [A_194] :
      ( v2_struct_0(k2_yellow_1(A_194))
      | v1_xboole_0(A_194)
      | k3_yellow_0(k2_yellow_1(A_194)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_194) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_421])).

tff(c_46,plain,(
    ! [A_35] :
      ( ~ v2_struct_0(k2_yellow_1(A_35))
      | v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_445,plain,(
    ! [A_195] :
      ( v1_xboole_0(A_195)
      | k3_yellow_0(k2_yellow_1(A_195)) = k1_xboole_0
      | ~ m1_subset_1(k1_xboole_0,A_195) ) ),
    inference(resolution,[status(thm)],[c_440,c_46])).

tff(c_56,plain,(
    k3_yellow_0(k2_yellow_1('#skF_2')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_456,plain,
    ( v1_xboole_0('#skF_2')
    | ~ m1_subset_1(k1_xboole_0,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_445,c_56])).

tff(c_463,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_456])).

tff(c_465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_463])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:26:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  
% 3.20/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.52  %$ r3_orders_2 > r2_lattice3 > r1_orders_2 > r1_lattice3 > r2_hidden > r1_yellow_0 > r1_tarski > m1_subset_1 > v5_orders_2 > v4_orders_2 > v3_orders_2 > v2_struct_0 > v1_xboole_0 > v1_orders_2 > l1_orders_2 > k1_yellow_0 > #nlpp > u1_struct_0 > u1_orders_2 > k3_yellow_0 > k2_yellow_1 > k1_yellow_1 > k1_xboole_0 > #skF_1 > #skF_2
% 3.20/1.52  
% 3.20/1.52  %Foreground sorts:
% 3.20/1.52  
% 3.20/1.52  
% 3.20/1.52  %Background operators:
% 3.20/1.52  
% 3.20/1.52  
% 3.20/1.52  %Foreground operators:
% 3.20/1.52  tff(v1_orders_2, type, v1_orders_2: $i > $o).
% 3.20/1.52  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.20/1.52  tff(r3_orders_2, type, r3_orders_2: ($i * $i * $i) > $o).
% 3.20/1.52  tff(k1_yellow_0, type, k1_yellow_0: ($i * $i) > $i).
% 3.20/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.20/1.52  tff(v3_orders_2, type, v3_orders_2: $i > $o).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.52  tff(r1_orders_2, type, r1_orders_2: ($i * $i * $i) > $o).
% 3.20/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.20/1.52  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 3.20/1.52  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 3.20/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.52  tff(r2_lattice3, type, r2_lattice3: ($i * $i * $i) > $o).
% 3.20/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.52  tff(r1_lattice3, type, r1_lattice3: ($i * $i * $i) > $o).
% 3.20/1.52  tff(v4_orders_2, type, v4_orders_2: $i > $o).
% 3.20/1.52  tff(r1_yellow_0, type, r1_yellow_0: ($i * $i) > $o).
% 3.20/1.52  tff(v5_orders_2, type, v5_orders_2: $i > $o).
% 3.20/1.52  tff(l1_orders_2, type, l1_orders_2: $i > $o).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.52  tff(k1_yellow_1, type, k1_yellow_1: $i > $i).
% 3.20/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.52  tff(u1_orders_2, type, u1_orders_2: $i > $i).
% 3.20/1.52  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.20/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.20/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.52  
% 3.20/1.54  tff(f_138, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_yellow_1)).
% 3.20/1.54  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.20/1.54  tff(f_97, axiom, (![A]: (v1_orders_2(k2_yellow_1(A)) & l1_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_yellow_1)).
% 3.20/1.54  tff(f_50, axiom, (![A]: (l1_orders_2(A) => (k3_yellow_0(A) = k1_yellow_0(A, k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d11_yellow_0)).
% 3.20/1.54  tff(f_117, axiom, (![A]: ((u1_struct_0(k2_yellow_1(A)) = A) & (u1_orders_2(k2_yellow_1(A)) = k1_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_yellow_1)).
% 3.20/1.54  tff(f_93, axiom, (![A]: (l1_orders_2(A) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (r2_lattice3(A, k1_xboole_0, B) & r1_lattice3(A, k1_xboole_0, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_yellow_0)).
% 3.20/1.54  tff(f_105, axiom, (![A]: (((v1_orders_2(k2_yellow_1(A)) & v3_orders_2(k2_yellow_1(A))) & v4_orders_2(k2_yellow_1(A))) & v5_orders_2(k2_yellow_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_yellow_1)).
% 3.20/1.54  tff(f_84, axiom, (![A]: ((v5_orders_2(A) & l1_orders_2(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: ((((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C)) => (r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D)))))) & ((r2_lattice3(A, C, B) & (![D]: (m1_subset_1(D, u1_struct_0(A)) => (r2_lattice3(A, C, D) => r1_orders_2(A, B, D))))) => ((B = k1_yellow_0(A, C)) & r1_yellow_0(A, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_yellow_0)).
% 3.20/1.54  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.20/1.54  tff(f_130, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, u1_struct_0(k2_yellow_1(A))) => (![C]: (m1_subset_1(C, u1_struct_0(k2_yellow_1(A))) => (r3_orders_2(k2_yellow_1(A), B, C) <=> r1_tarski(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_yellow_1)).
% 3.20/1.54  tff(f_46, axiom, (![A, B, C]: (((((~v2_struct_0(A) & v3_orders_2(A)) & l1_orders_2(A)) & m1_subset_1(B, u1_struct_0(A))) & m1_subset_1(C, u1_struct_0(A))) => (r3_orders_2(A, B, C) <=> r1_orders_2(A, B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r3_orders_2)).
% 3.20/1.54  tff(f_113, axiom, (![A]: (~v1_xboole_0(A) => (~v2_struct_0(k2_yellow_1(A)) & v1_orders_2(k2_yellow_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_yellow_1)).
% 3.20/1.54  tff(c_60, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.20/1.54  tff(c_58, plain, (r2_hidden(k1_xboole_0, '#skF_2')), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.20/1.54  tff(c_90, plain, (![A_53, B_54]: (m1_subset_1(A_53, B_54) | ~r2_hidden(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.20/1.54  tff(c_94, plain, (m1_subset_1(k1_xboole_0, '#skF_2')), inference(resolution, [status(thm)], [c_58, c_90])).
% 3.20/1.54  tff(c_34, plain, (![A_33]: (l1_orders_2(k2_yellow_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.20/1.54  tff(c_95, plain, (![A_55]: (k1_yellow_0(A_55, k1_xboole_0)=k3_yellow_0(A_55) | ~l1_orders_2(A_55))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.20/1.54  tff(c_99, plain, (![A_33]: (k1_yellow_0(k2_yellow_1(A_33), k1_xboole_0)=k3_yellow_0(k2_yellow_1(A_33)))), inference(resolution, [status(thm)], [c_34, c_95])).
% 3.20/1.54  tff(c_48, plain, (![A_36]: (u1_struct_0(k2_yellow_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_117])).
% 3.20/1.54  tff(c_100, plain, (![A_56, B_57]: (r2_lattice3(A_56, k1_xboole_0, B_57) | ~m1_subset_1(B_57, u1_struct_0(A_56)) | ~l1_orders_2(A_56))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.20/1.54  tff(c_103, plain, (![A_36, B_57]: (r2_lattice3(k2_yellow_1(A_36), k1_xboole_0, B_57) | ~m1_subset_1(B_57, A_36) | ~l1_orders_2(k2_yellow_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_100])).
% 3.20/1.54  tff(c_105, plain, (![A_36, B_57]: (r2_lattice3(k2_yellow_1(A_36), k1_xboole_0, B_57) | ~m1_subset_1(B_57, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_103])).
% 3.20/1.54  tff(c_42, plain, (![A_34]: (v5_orders_2(k2_yellow_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.20/1.54  tff(c_222, plain, (![A_114, B_115, C_116]: (m1_subset_1('#skF_1'(A_114, B_115, C_116), u1_struct_0(A_114)) | k1_yellow_0(A_114, C_116)=B_115 | ~r2_lattice3(A_114, C_116, B_115) | ~m1_subset_1(B_115, u1_struct_0(A_114)) | ~l1_orders_2(A_114) | ~v5_orders_2(A_114))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.54  tff(c_233, plain, (![A_36, B_115, C_116]: (m1_subset_1('#skF_1'(k2_yellow_1(A_36), B_115, C_116), A_36) | k1_yellow_0(k2_yellow_1(A_36), C_116)=B_115 | ~r2_lattice3(k2_yellow_1(A_36), C_116, B_115) | ~m1_subset_1(B_115, u1_struct_0(k2_yellow_1(A_36))) | ~l1_orders_2(k2_yellow_1(A_36)) | ~v5_orders_2(k2_yellow_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_222])).
% 3.20/1.54  tff(c_238, plain, (![A_36, B_115, C_116]: (m1_subset_1('#skF_1'(k2_yellow_1(A_36), B_115, C_116), A_36) | k1_yellow_0(k2_yellow_1(A_36), C_116)=B_115 | ~r2_lattice3(k2_yellow_1(A_36), C_116, B_115) | ~m1_subset_1(B_115, A_36))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_48, c_233])).
% 3.20/1.54  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.20/1.54  tff(c_38, plain, (![A_34]: (v3_orders_2(k2_yellow_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.20/1.54  tff(c_52, plain, (![A_37, B_41, C_43]: (r3_orders_2(k2_yellow_1(A_37), B_41, C_43) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, u1_struct_0(k2_yellow_1(A_37))) | ~m1_subset_1(B_41, u1_struct_0(k2_yellow_1(A_37))) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.20/1.54  tff(c_62, plain, (![A_37, B_41, C_43]: (r3_orders_2(k2_yellow_1(A_37), B_41, C_43) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, A_37) | ~m1_subset_1(B_41, A_37) | v1_xboole_0(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_52])).
% 3.20/1.54  tff(c_143, plain, (![A_75, B_76, C_77]: (r1_orders_2(A_75, B_76, C_77) | ~r3_orders_2(A_75, B_76, C_77) | ~m1_subset_1(C_77, u1_struct_0(A_75)) | ~m1_subset_1(B_76, u1_struct_0(A_75)) | ~l1_orders_2(A_75) | ~v3_orders_2(A_75) | v2_struct_0(A_75))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.54  tff(c_145, plain, (![A_37, B_41, C_43]: (r1_orders_2(k2_yellow_1(A_37), B_41, C_43) | ~m1_subset_1(C_43, u1_struct_0(k2_yellow_1(A_37))) | ~m1_subset_1(B_41, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)) | ~v3_orders_2(k2_yellow_1(A_37)) | v2_struct_0(k2_yellow_1(A_37)) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, A_37) | ~m1_subset_1(B_41, A_37) | v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_62, c_143])).
% 3.20/1.54  tff(c_148, plain, (![A_37, B_41, C_43]: (r1_orders_2(k2_yellow_1(A_37), B_41, C_43) | v2_struct_0(k2_yellow_1(A_37)) | ~r1_tarski(B_41, C_43) | ~m1_subset_1(C_43, A_37) | ~m1_subset_1(B_41, A_37) | v1_xboole_0(A_37))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34, c_48, c_48, c_145])).
% 3.20/1.54  tff(c_214, plain, (![A_111, B_112, C_113]: (~r1_orders_2(A_111, B_112, '#skF_1'(A_111, B_112, C_113)) | k1_yellow_0(A_111, C_113)=B_112 | ~r2_lattice3(A_111, C_113, B_112) | ~m1_subset_1(B_112, u1_struct_0(A_111)) | ~l1_orders_2(A_111) | ~v5_orders_2(A_111))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.20/1.54  tff(c_218, plain, (![A_37, C_113, B_41]: (k1_yellow_0(k2_yellow_1(A_37), C_113)=B_41 | ~r2_lattice3(k2_yellow_1(A_37), C_113, B_41) | ~m1_subset_1(B_41, u1_struct_0(k2_yellow_1(A_37))) | ~l1_orders_2(k2_yellow_1(A_37)) | ~v5_orders_2(k2_yellow_1(A_37)) | v2_struct_0(k2_yellow_1(A_37)) | ~r1_tarski(B_41, '#skF_1'(k2_yellow_1(A_37), B_41, C_113)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_37), B_41, C_113), A_37) | ~m1_subset_1(B_41, A_37) | v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_148, c_214])).
% 3.20/1.54  tff(c_401, plain, (![A_183, C_184, B_185]: (k1_yellow_0(k2_yellow_1(A_183), C_184)=B_185 | ~r2_lattice3(k2_yellow_1(A_183), C_184, B_185) | v2_struct_0(k2_yellow_1(A_183)) | ~r1_tarski(B_185, '#skF_1'(k2_yellow_1(A_183), B_185, C_184)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_183), B_185, C_184), A_183) | ~m1_subset_1(B_185, A_183) | v1_xboole_0(A_183))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_34, c_48, c_218])).
% 3.20/1.54  tff(c_406, plain, (![A_186, C_187]: (k1_yellow_0(k2_yellow_1(A_186), C_187)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_186), C_187, k1_xboole_0) | v2_struct_0(k2_yellow_1(A_186)) | ~m1_subset_1('#skF_1'(k2_yellow_1(A_186), k1_xboole_0, C_187), A_186) | ~m1_subset_1(k1_xboole_0, A_186) | v1_xboole_0(A_186))), inference(resolution, [status(thm)], [c_2, c_401])).
% 3.20/1.54  tff(c_417, plain, (![A_188, C_189]: (v2_struct_0(k2_yellow_1(A_188)) | v1_xboole_0(A_188) | k1_yellow_0(k2_yellow_1(A_188), C_189)=k1_xboole_0 | ~r2_lattice3(k2_yellow_1(A_188), C_189, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, A_188))), inference(resolution, [status(thm)], [c_238, c_406])).
% 3.20/1.54  tff(c_421, plain, (![A_36]: (v2_struct_0(k2_yellow_1(A_36)) | v1_xboole_0(A_36) | k1_yellow_0(k2_yellow_1(A_36), k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_36))), inference(resolution, [status(thm)], [c_105, c_417])).
% 3.20/1.54  tff(c_440, plain, (![A_194]: (v2_struct_0(k2_yellow_1(A_194)) | v1_xboole_0(A_194) | k3_yellow_0(k2_yellow_1(A_194))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_194))), inference(demodulation, [status(thm), theory('equality')], [c_99, c_421])).
% 3.20/1.54  tff(c_46, plain, (![A_35]: (~v2_struct_0(k2_yellow_1(A_35)) | v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_113])).
% 3.20/1.54  tff(c_445, plain, (![A_195]: (v1_xboole_0(A_195) | k3_yellow_0(k2_yellow_1(A_195))=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, A_195))), inference(resolution, [status(thm)], [c_440, c_46])).
% 3.20/1.54  tff(c_56, plain, (k3_yellow_0(k2_yellow_1('#skF_2'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.20/1.54  tff(c_456, plain, (v1_xboole_0('#skF_2') | ~m1_subset_1(k1_xboole_0, '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_445, c_56])).
% 3.20/1.54  tff(c_463, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_94, c_456])).
% 3.20/1.54  tff(c_465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_463])).
% 3.20/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.54  
% 3.20/1.54  Inference rules
% 3.20/1.54  ----------------------
% 3.20/1.54  #Ref     : 0
% 3.20/1.54  #Sup     : 73
% 3.20/1.54  #Fact    : 0
% 3.20/1.54  #Define  : 0
% 3.20/1.54  #Split   : 0
% 3.20/1.54  #Chain   : 0
% 3.20/1.54  #Close   : 0
% 3.20/1.54  
% 3.20/1.54  Ordering : KBO
% 3.20/1.54  
% 3.20/1.54  Simplification rules
% 3.20/1.54  ----------------------
% 3.20/1.54  #Subsume      : 13
% 3.20/1.54  #Demod        : 120
% 3.20/1.54  #Tautology    : 16
% 3.20/1.54  #SimpNegUnit  : 1
% 3.20/1.54  #BackRed      : 0
% 3.20/1.54  
% 3.20/1.54  #Partial instantiations: 0
% 3.20/1.54  #Strategies tried      : 1
% 3.20/1.54  
% 3.20/1.54  Timing (in seconds)
% 3.20/1.54  ----------------------
% 3.20/1.54  Preprocessing        : 0.33
% 3.20/1.54  Parsing              : 0.17
% 3.20/1.54  CNF conversion       : 0.02
% 3.20/1.54  Main loop            : 0.35
% 3.20/1.54  Inferencing          : 0.15
% 3.20/1.54  Reduction            : 0.10
% 3.20/1.54  Demodulation         : 0.07
% 3.20/1.54  BG Simplification    : 0.02
% 3.20/1.54  Subsumption          : 0.06
% 3.20/1.54  Abstraction          : 0.02
% 3.20/1.54  MUC search           : 0.00
% 3.20/1.54  Cooper               : 0.00
% 3.20/1.54  Total                : 0.72
% 3.20/1.54  Index Insertion      : 0.00
% 3.20/1.54  Index Deletion       : 0.00
% 3.20/1.54  Index Matching       : 0.00
% 3.20/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
