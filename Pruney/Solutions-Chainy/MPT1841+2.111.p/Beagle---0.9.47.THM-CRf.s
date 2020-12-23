%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:42 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   57 (  76 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   68 ( 116 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_78,axiom,(
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

tff(c_6,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_309,plain,(
    ! [A_63,B_64,C_65,D_66] : k2_xboole_0(k2_tarski(A_63,B_64),k2_tarski(C_65,D_66)) = k2_enumset1(A_63,B_64,C_65,D_66) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_326,plain,(
    ! [A_6,C_65,D_66] : k2_xboole_0(k1_tarski(A_6),k2_tarski(C_65,D_66)) = k2_enumset1(A_6,A_6,C_65,D_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_309])).

tff(c_333,plain,(
    ! [A_67,C_68,D_69] : k2_xboole_0(k1_tarski(A_67),k2_tarski(C_68,D_69)) = k1_enumset1(A_67,C_68,D_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_326])).

tff(c_14,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),B_15) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_347,plain,(
    ! [A_70,C_71,D_72] : k1_enumset1(A_70,C_71,D_72) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_14])).

tff(c_398,plain,(
    ! [A_75,B_76] : k2_tarski(A_75,B_76) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_347])).

tff(c_400,plain,(
    ! [A_6] : k1_tarski(A_6) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_398])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_95,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_98,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_95])).

tff(c_101,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_98])).

tff(c_26,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_102,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_26])).

tff(c_107,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k6_domain_1(A_44,B_45),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_116,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_107])).

tff(c_120,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_116])).

tff(c_121,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_120])).

tff(c_350,plain,(
    ! [B_73,A_74] :
      ( ~ v1_subset_1(B_73,A_74)
      | v1_xboole_0(B_73)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74))
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_356,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_121,c_350])).

tff(c_365,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_102,c_356])).

tff(c_366,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_365])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_371,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_366,c_2])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_400,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:28:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.32  
% 2.28/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.32  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.28/1.32  
% 2.28/1.32  %Foreground sorts:
% 2.28/1.32  
% 2.28/1.32  
% 2.28/1.32  %Background operators:
% 2.28/1.32  
% 2.28/1.32  
% 2.28/1.32  %Foreground operators:
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.28/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.32  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.28/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.28/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.32  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.28/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.32  
% 2.62/1.33  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.62/1.33  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.62/1.33  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.62/1.33  tff(f_31, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 2.62/1.33  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.62/1.33  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.62/1.33  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.62/1.33  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.62/1.33  tff(f_78, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.62/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.33  tff(c_6, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.33  tff(c_8, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.33  tff(c_10, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.33  tff(c_309, plain, (![A_63, B_64, C_65, D_66]: (k2_xboole_0(k2_tarski(A_63, B_64), k2_tarski(C_65, D_66))=k2_enumset1(A_63, B_64, C_65, D_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.33  tff(c_326, plain, (![A_6, C_65, D_66]: (k2_xboole_0(k1_tarski(A_6), k2_tarski(C_65, D_66))=k2_enumset1(A_6, A_6, C_65, D_66))), inference(superposition, [status(thm), theory('equality')], [c_6, c_309])).
% 2.62/1.33  tff(c_333, plain, (![A_67, C_68, D_69]: (k2_xboole_0(k1_tarski(A_67), k2_tarski(C_68, D_69))=k1_enumset1(A_67, C_68, D_69))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_326])).
% 2.62/1.33  tff(c_14, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.62/1.33  tff(c_347, plain, (![A_70, C_71, D_72]: (k1_enumset1(A_70, C_71, D_72)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_333, c_14])).
% 2.62/1.33  tff(c_398, plain, (![A_75, B_76]: (k2_tarski(A_75, B_76)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_347])).
% 2.62/1.33  tff(c_400, plain, (![A_6]: (k1_tarski(A_6)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_398])).
% 2.62/1.33  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.62/1.33  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.62/1.33  tff(c_28, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.62/1.33  tff(c_95, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.62/1.33  tff(c_98, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_95])).
% 2.62/1.33  tff(c_101, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_98])).
% 2.62/1.33  tff(c_26, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.62/1.33  tff(c_102, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_26])).
% 2.62/1.33  tff(c_107, plain, (![A_44, B_45]: (m1_subset_1(k6_domain_1(A_44, B_45), k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.33  tff(c_116, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_107])).
% 2.62/1.33  tff(c_120, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_116])).
% 2.62/1.33  tff(c_121, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_30, c_120])).
% 2.62/1.33  tff(c_350, plain, (![B_73, A_74]: (~v1_subset_1(B_73, A_74) | v1_xboole_0(B_73) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)) | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.62/1.33  tff(c_356, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_121, c_350])).
% 2.62/1.33  tff(c_365, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_102, c_356])).
% 2.62/1.33  tff(c_366, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_365])).
% 2.62/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.33  tff(c_371, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_366, c_2])).
% 2.62/1.33  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_400, c_371])).
% 2.62/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.33  
% 2.62/1.33  Inference rules
% 2.62/1.33  ----------------------
% 2.62/1.33  #Ref     : 0
% 2.62/1.33  #Sup     : 89
% 2.62/1.33  #Fact    : 0
% 2.62/1.33  #Define  : 0
% 2.62/1.33  #Split   : 1
% 2.62/1.33  #Chain   : 0
% 2.62/1.33  #Close   : 0
% 2.62/1.33  
% 2.62/1.33  Ordering : KBO
% 2.62/1.33  
% 2.62/1.33  Simplification rules
% 2.62/1.33  ----------------------
% 2.62/1.33  #Subsume      : 4
% 2.62/1.33  #Demod        : 37
% 2.62/1.33  #Tautology    : 45
% 2.62/1.33  #SimpNegUnit  : 10
% 2.62/1.33  #BackRed      : 15
% 2.62/1.33  
% 2.62/1.33  #Partial instantiations: 0
% 2.62/1.33  #Strategies tried      : 1
% 2.62/1.33  
% 2.62/1.33  Timing (in seconds)
% 2.62/1.33  ----------------------
% 2.62/1.34  Preprocessing        : 0.30
% 2.62/1.34  Parsing              : 0.16
% 2.62/1.34  CNF conversion       : 0.02
% 2.62/1.34  Main loop            : 0.28
% 2.62/1.34  Inferencing          : 0.12
% 2.62/1.34  Reduction            : 0.09
% 2.62/1.34  Demodulation         : 0.06
% 2.62/1.34  BG Simplification    : 0.02
% 2.62/1.34  Subsumption          : 0.04
% 2.62/1.34  Abstraction          : 0.02
% 2.62/1.34  MUC search           : 0.00
% 2.62/1.34  Cooper               : 0.00
% 2.62/1.34  Total                : 0.62
% 2.62/1.34  Index Insertion      : 0.00
% 2.62/1.34  Index Deletion       : 0.00
% 2.62/1.34  Index Matching       : 0.00
% 2.62/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
