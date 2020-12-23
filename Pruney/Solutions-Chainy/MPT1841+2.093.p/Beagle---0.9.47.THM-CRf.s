%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:40 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   62 (  79 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 119 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_32,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_43,axiom,(
    ! [A,B,C,D,E,F] : ~ v1_xboole_0(k4_enumset1(A,B,C,D,E,F)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_subset_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_26,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_30,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_68,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_71,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_74,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_71])).

tff(c_28,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_75,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_28])).

tff(c_89,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k6_domain_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,A_55)
      | v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_89])).

tff(c_102,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_98])).

tff(c_103,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_102])).

tff(c_213,plain,(
    ! [B_81,A_82] :
      ( ~ v1_subset_1(B_81,A_82)
      | v1_xboole_0(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_zfmisc_1(A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_219,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_103,c_213])).

tff(c_228,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_75,c_219])).

tff(c_229,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_228])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_234,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_229,c_4])).

tff(c_6,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_3,B_4] : k1_enumset1(A_3,A_3,B_4) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] : k2_enumset1(A_5,A_5,B_6,C_7) = k1_enumset1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_12,plain,(
    ! [A_8,B_9,C_10,D_11] : k3_enumset1(A_8,A_8,B_9,C_10,D_11) = k2_enumset1(A_8,B_9,C_10,D_11) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_235,plain,(
    ! [B_83,D_86,E_85,C_87,A_84] : k4_enumset1(A_84,A_84,B_83,C_87,D_86,E_85) = k3_enumset1(A_84,B_83,C_87,D_86,E_85) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] : ~ v1_xboole_0(k4_enumset1(A_17,B_18,C_19,D_20,E_21,F_22)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_312,plain,(
    ! [C_92,A_88,D_91,B_90,E_89] : ~ v1_xboole_0(k3_enumset1(A_88,B_90,C_92,D_91,E_89)) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_16])).

tff(c_328,plain,(
    ! [A_95,B_96,C_97,D_98] : ~ v1_xboole_0(k2_enumset1(A_95,B_96,C_97,D_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_312])).

tff(c_331,plain,(
    ! [A_99,B_100,C_101] : ~ v1_xboole_0(k1_enumset1(A_99,B_100,C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_328])).

tff(c_334,plain,(
    ! [A_102,B_103] : ~ v1_xboole_0(k2_tarski(A_102,B_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_331])).

tff(c_338,plain,(
    ! [A_104] : ~ v1_xboole_0(k1_tarski(A_104)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_334])).

tff(c_340,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_338])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.34  
% 2.36/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.34  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.36/1.34  
% 2.36/1.34  %Foreground sorts:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Background operators:
% 2.36/1.34  
% 2.36/1.34  
% 2.36/1.34  %Foreground operators:
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.34  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.36/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.36/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.36/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.34  
% 2.36/1.36  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.36/1.36  tff(f_91, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.36/1.36  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.36/1.36  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.36/1.36  tff(f_79, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.36/1.36  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.36/1.36  tff(f_32, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.36/1.36  tff(f_34, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.36/1.36  tff(f_36, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.36/1.36  tff(f_38, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.36/1.36  tff(f_40, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 2.36/1.36  tff(f_43, axiom, (![A, B, C, D, E, F]: ~v1_xboole_0(k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_subset_1)).
% 2.36/1.36  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.36/1.36  tff(c_32, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.36  tff(c_26, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.36  tff(c_30, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.36  tff(c_68, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.36/1.36  tff(c_71, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_68])).
% 2.36/1.36  tff(c_74, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_71])).
% 2.36/1.36  tff(c_28, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.36/1.36  tff(c_75, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_28])).
% 2.36/1.36  tff(c_89, plain, (![A_55, B_56]: (m1_subset_1(k6_domain_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, A_55) | v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.36/1.36  tff(c_98, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_74, c_89])).
% 2.36/1.36  tff(c_102, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_98])).
% 2.36/1.36  tff(c_103, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_32, c_102])).
% 2.36/1.36  tff(c_213, plain, (![B_81, A_82]: (~v1_subset_1(B_81, A_82) | v1_xboole_0(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_zfmisc_1(A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.36/1.36  tff(c_219, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_103, c_213])).
% 2.36/1.36  tff(c_228, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_75, c_219])).
% 2.36/1.36  tff(c_229, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_228])).
% 2.36/1.36  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.36/1.36  tff(c_234, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_229, c_4])).
% 2.36/1.36  tff(c_6, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.36/1.36  tff(c_8, plain, (![A_3, B_4]: (k1_enumset1(A_3, A_3, B_4)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.36/1.36  tff(c_10, plain, (![A_5, B_6, C_7]: (k2_enumset1(A_5, A_5, B_6, C_7)=k1_enumset1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.36/1.36  tff(c_12, plain, (![A_8, B_9, C_10, D_11]: (k3_enumset1(A_8, A_8, B_9, C_10, D_11)=k2_enumset1(A_8, B_9, C_10, D_11))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.36/1.36  tff(c_235, plain, (![B_83, D_86, E_85, C_87, A_84]: (k4_enumset1(A_84, A_84, B_83, C_87, D_86, E_85)=k3_enumset1(A_84, B_83, C_87, D_86, E_85))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.36/1.36  tff(c_16, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (~v1_xboole_0(k4_enumset1(A_17, B_18, C_19, D_20, E_21, F_22)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.36  tff(c_312, plain, (![C_92, A_88, D_91, B_90, E_89]: (~v1_xboole_0(k3_enumset1(A_88, B_90, C_92, D_91, E_89)))), inference(superposition, [status(thm), theory('equality')], [c_235, c_16])).
% 2.36/1.36  tff(c_328, plain, (![A_95, B_96, C_97, D_98]: (~v1_xboole_0(k2_enumset1(A_95, B_96, C_97, D_98)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_312])).
% 2.36/1.36  tff(c_331, plain, (![A_99, B_100, C_101]: (~v1_xboole_0(k1_enumset1(A_99, B_100, C_101)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_328])).
% 2.36/1.36  tff(c_334, plain, (![A_102, B_103]: (~v1_xboole_0(k2_tarski(A_102, B_103)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_331])).
% 2.36/1.36  tff(c_338, plain, (![A_104]: (~v1_xboole_0(k1_tarski(A_104)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_334])).
% 2.36/1.36  tff(c_340, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_234, c_338])).
% 2.36/1.36  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_340])).
% 2.36/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.36  
% 2.36/1.36  Inference rules
% 2.36/1.36  ----------------------
% 2.36/1.36  #Ref     : 0
% 2.36/1.36  #Sup     : 68
% 2.36/1.36  #Fact    : 0
% 2.36/1.36  #Define  : 0
% 2.36/1.36  #Split   : 2
% 2.36/1.36  #Chain   : 0
% 2.36/1.36  #Close   : 0
% 2.36/1.36  
% 2.36/1.36  Ordering : KBO
% 2.36/1.36  
% 2.36/1.36  Simplification rules
% 2.36/1.36  ----------------------
% 2.36/1.36  #Subsume      : 5
% 2.36/1.36  #Demod        : 40
% 2.36/1.36  #Tautology    : 36
% 2.36/1.36  #SimpNegUnit  : 15
% 2.36/1.36  #BackRed      : 9
% 2.36/1.36  
% 2.36/1.36  #Partial instantiations: 0
% 2.36/1.36  #Strategies tried      : 1
% 2.36/1.36  
% 2.36/1.36  Timing (in seconds)
% 2.36/1.36  ----------------------
% 2.36/1.36  Preprocessing        : 0.33
% 2.36/1.36  Parsing              : 0.18
% 2.36/1.36  CNF conversion       : 0.02
% 2.36/1.36  Main loop            : 0.23
% 2.36/1.36  Inferencing          : 0.09
% 2.36/1.36  Reduction            : 0.07
% 2.36/1.36  Demodulation         : 0.05
% 2.36/1.36  BG Simplification    : 0.02
% 2.36/1.36  Subsumption          : 0.04
% 2.36/1.36  Abstraction          : 0.02
% 2.36/1.36  MUC search           : 0.00
% 2.36/1.36  Cooper               : 0.00
% 2.36/1.36  Total                : 0.59
% 2.36/1.36  Index Insertion      : 0.00
% 2.36/1.36  Index Deletion       : 0.00
% 2.36/1.36  Index Matching       : 0.00
% 2.36/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
