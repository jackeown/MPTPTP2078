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
% DateTime   : Thu Dec  3 10:28:39 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   69 (  86 expanded)
%              Number of leaves         :   35 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 131 expanded)
%              Number of equality atoms :   24 (  28 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_118,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_106,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F,G] :
      ( G = k4_enumset1(A,B,C,D,E,F)
    <=> ! [H] :
          ( r2_hidden(H,G)
        <=> ~ ( H != A
              & H != B
              & H != C
              & H != D
              & H != E
              & H != F ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_enumset1)).

tff(f_78,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_68,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_72,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_138,plain,(
    ! [A_101,B_102] :
      ( k6_domain_1(A_101,B_102) = k1_tarski(B_102)
      | ~ m1_subset_1(B_102,A_101)
      | v1_xboole_0(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_141,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_72,c_138])).

tff(c_144,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_141])).

tff(c_70,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_145,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_70])).

tff(c_153,plain,(
    ! [A_121,B_122] :
      ( m1_subset_1(k6_domain_1(A_121,B_122),k1_zfmisc_1(A_121))
      | ~ m1_subset_1(B_122,A_121)
      | v1_xboole_0(A_121) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_162,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_153])).

tff(c_166,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_162])).

tff(c_167,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_166])).

tff(c_529,plain,(
    ! [B_199,A_200] :
      ( ~ v1_subset_1(B_199,A_200)
      | v1_xboole_0(B_199)
      | ~ m1_subset_1(B_199,k1_zfmisc_1(A_200))
      | ~ v1_zfmisc_1(A_200)
      | v1_xboole_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_535,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_167,c_529])).

tff(c_542,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_145,c_535])).

tff(c_543,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_542])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_548,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_543,c_2])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4,B_5] : k1_enumset1(A_4,A_4,B_5) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k2_enumset1(A_6,A_6,B_7,C_8) = k1_enumset1(A_6,B_7,C_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] : k3_enumset1(A_9,A_9,B_10,C_11,D_12) = k2_enumset1(A_9,B_10,C_11,D_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_424,plain,(
    ! [B_180,D_179,E_181,A_182,C_183] : k4_enumset1(A_182,A_182,B_180,C_183,D_179,E_181) = k3_enumset1(A_182,B_180,C_183,D_179,E_181) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [E_22,D_21,H_27,F_23,C_20,B_19] : r2_hidden(H_27,k4_enumset1(H_27,B_19,C_20,D_21,E_22,F_23)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_469,plain,(
    ! [E_188,C_185,D_187,A_186,B_184] : r2_hidden(A_186,k3_enumset1(A_186,B_184,C_185,D_187,E_188)) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_28])).

tff(c_477,plain,(
    ! [A_189,B_190,C_191,D_192] : r2_hidden(A_189,k2_enumset1(A_189,B_190,C_191,D_192)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_469])).

tff(c_485,plain,(
    ! [A_193,B_194,C_195] : r2_hidden(A_193,k1_enumset1(A_193,B_194,C_195)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_477])).

tff(c_516,plain,(
    ! [A_196,B_197] : r2_hidden(A_196,k2_tarski(A_196,B_197)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_485])).

tff(c_522,plain,(
    ! [A_3] : r2_hidden(A_3,k1_tarski(A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_516])).

tff(c_558,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_548,c_522])).

tff(c_60,plain,(
    ! [B_32,A_31] :
      ( ~ r1_tarski(B_32,A_31)
      | ~ r2_hidden(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_583,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_558,c_60])).

tff(c_587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_583])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:05:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.38  
% 2.86/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.38  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.86/1.38  
% 2.86/1.38  %Foreground sorts:
% 2.86/1.38  
% 2.86/1.38  
% 2.86/1.38  %Background operators:
% 2.86/1.38  
% 2.86/1.38  
% 2.86/1.38  %Foreground operators:
% 2.86/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.86/1.38  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.86/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.86/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.86/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.86/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.86/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.86/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.86/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.86/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.86/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.86/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.86/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.86/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.39  
% 2.86/1.40  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.86/1.40  tff(f_118, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.86/1.40  tff(f_92, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.86/1.40  tff(f_85, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.86/1.40  tff(f_106, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.86/1.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.86/1.40  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.86/1.40  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.86/1.40  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.86/1.40  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.86/1.40  tff(f_41, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.86/1.40  tff(f_65, axiom, (![A, B, C, D, E, F, G]: ((G = k4_enumset1(A, B, C, D, E, F)) <=> (![H]: (r2_hidden(H, G) <=> ~(((((~(H = A) & ~(H = B)) & ~(H = C)) & ~(H = D)) & ~(H = E)) & ~(H = F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_enumset1)).
% 2.86/1.40  tff(f_78, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.86/1.40  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.86/1.40  tff(c_74, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.86/1.40  tff(c_68, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.86/1.40  tff(c_72, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.86/1.40  tff(c_138, plain, (![A_101, B_102]: (k6_domain_1(A_101, B_102)=k1_tarski(B_102) | ~m1_subset_1(B_102, A_101) | v1_xboole_0(A_101))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.86/1.40  tff(c_141, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_72, c_138])).
% 2.86/1.40  tff(c_144, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_74, c_141])).
% 2.86/1.40  tff(c_70, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.86/1.40  tff(c_145, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_70])).
% 2.86/1.40  tff(c_153, plain, (![A_121, B_122]: (m1_subset_1(k6_domain_1(A_121, B_122), k1_zfmisc_1(A_121)) | ~m1_subset_1(B_122, A_121) | v1_xboole_0(A_121))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.86/1.40  tff(c_162, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_144, c_153])).
% 2.86/1.40  tff(c_166, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_162])).
% 2.86/1.40  tff(c_167, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_74, c_166])).
% 2.86/1.40  tff(c_529, plain, (![B_199, A_200]: (~v1_subset_1(B_199, A_200) | v1_xboole_0(B_199) | ~m1_subset_1(B_199, k1_zfmisc_1(A_200)) | ~v1_zfmisc_1(A_200) | v1_xboole_0(A_200))), inference(cnfTransformation, [status(thm)], [f_106])).
% 2.86/1.40  tff(c_535, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_167, c_529])).
% 2.86/1.40  tff(c_542, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_145, c_535])).
% 2.86/1.40  tff(c_543, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_74, c_542])).
% 2.86/1.40  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.86/1.40  tff(c_548, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_543, c_2])).
% 2.86/1.40  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.40  tff(c_8, plain, (![A_4, B_5]: (k1_enumset1(A_4, A_4, B_5)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.86/1.40  tff(c_10, plain, (![A_6, B_7, C_8]: (k2_enumset1(A_6, A_6, B_7, C_8)=k1_enumset1(A_6, B_7, C_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.40  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (k3_enumset1(A_9, A_9, B_10, C_11, D_12)=k2_enumset1(A_9, B_10, C_11, D_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.40  tff(c_424, plain, (![B_180, D_179, E_181, A_182, C_183]: (k4_enumset1(A_182, A_182, B_180, C_183, D_179, E_181)=k3_enumset1(A_182, B_180, C_183, D_179, E_181))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.40  tff(c_28, plain, (![E_22, D_21, H_27, F_23, C_20, B_19]: (r2_hidden(H_27, k4_enumset1(H_27, B_19, C_20, D_21, E_22, F_23)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.86/1.40  tff(c_469, plain, (![E_188, C_185, D_187, A_186, B_184]: (r2_hidden(A_186, k3_enumset1(A_186, B_184, C_185, D_187, E_188)))), inference(superposition, [status(thm), theory('equality')], [c_424, c_28])).
% 2.86/1.40  tff(c_477, plain, (![A_189, B_190, C_191, D_192]: (r2_hidden(A_189, k2_enumset1(A_189, B_190, C_191, D_192)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_469])).
% 2.86/1.40  tff(c_485, plain, (![A_193, B_194, C_195]: (r2_hidden(A_193, k1_enumset1(A_193, B_194, C_195)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_477])).
% 2.86/1.40  tff(c_516, plain, (![A_196, B_197]: (r2_hidden(A_196, k2_tarski(A_196, B_197)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_485])).
% 2.86/1.40  tff(c_522, plain, (![A_3]: (r2_hidden(A_3, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_516])).
% 2.86/1.40  tff(c_558, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_548, c_522])).
% 2.86/1.40  tff(c_60, plain, (![B_32, A_31]: (~r1_tarski(B_32, A_31) | ~r2_hidden(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.40  tff(c_583, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_558, c_60])).
% 2.86/1.40  tff(c_587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_583])).
% 2.86/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  Inference rules
% 2.86/1.40  ----------------------
% 2.86/1.40  #Ref     : 0
% 2.86/1.40  #Sup     : 119
% 2.86/1.40  #Fact    : 0
% 2.86/1.40  #Define  : 0
% 2.86/1.40  #Split   : 2
% 2.86/1.40  #Chain   : 0
% 2.86/1.40  #Close   : 0
% 2.86/1.40  
% 2.86/1.40  Ordering : KBO
% 2.86/1.40  
% 2.86/1.40  Simplification rules
% 2.86/1.40  ----------------------
% 2.86/1.40  #Subsume      : 8
% 2.86/1.40  #Demod        : 35
% 2.86/1.40  #Tautology    : 39
% 2.86/1.40  #SimpNegUnit  : 10
% 2.86/1.40  #BackRed      : 14
% 2.86/1.40  
% 2.86/1.40  #Partial instantiations: 0
% 2.86/1.40  #Strategies tried      : 1
% 2.86/1.40  
% 2.86/1.40  Timing (in seconds)
% 2.86/1.40  ----------------------
% 2.86/1.40  Preprocessing        : 0.34
% 2.86/1.40  Parsing              : 0.17
% 2.86/1.40  CNF conversion       : 0.03
% 2.86/1.40  Main loop            : 0.30
% 2.86/1.40  Inferencing          : 0.10
% 2.86/1.40  Reduction            : 0.09
% 2.86/1.40  Demodulation         : 0.06
% 2.86/1.40  BG Simplification    : 0.02
% 2.86/1.40  Subsumption          : 0.08
% 2.86/1.40  Abstraction          : 0.02
% 2.86/1.40  MUC search           : 0.00
% 2.86/1.40  Cooper               : 0.00
% 2.86/1.40  Total                : 0.68
% 2.86/1.40  Index Insertion      : 0.00
% 2.86/1.40  Index Deletion       : 0.00
% 2.86/1.40  Index Matching       : 0.00
% 2.86/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
