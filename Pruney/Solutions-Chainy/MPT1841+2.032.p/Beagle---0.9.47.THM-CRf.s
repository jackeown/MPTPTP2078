%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:32 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   59 (  76 expanded)
%              Number of leaves         :   33 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 111 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_90,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_subset_1(B,A)
           => v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_103,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_112,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_103])).

tff(c_115,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_24,plain,(
    ! [B_36] : k4_xboole_0(k1_tarski(B_36),k1_tarski(B_36)) != k1_tarski(B_36) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    ! [B_36] : k1_tarski(B_36) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_24])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_157,plain,(
    ! [A_71,B_72] :
      ( k6_domain_1(A_71,B_72) = k1_tarski(B_72)
      | ~ m1_subset_1(B_72,A_71)
      | v1_xboole_0(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_160,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_157])).

tff(c_163,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_160])).

tff(c_40,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_164,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_40])).

tff(c_169,plain,(
    ! [A_73,B_74] :
      ( m1_subset_1(k6_domain_1(A_73,B_74),k1_zfmisc_1(A_73))
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_178,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_169])).

tff(c_182,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_178])).

tff(c_183,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_182])).

tff(c_204,plain,(
    ! [B_79,A_80] :
      ( v1_xboole_0(B_79)
      | ~ v1_subset_1(B_79,A_80)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_zfmisc_1(A_80)
      | v1_xboole_0(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_207,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_183,c_204])).

tff(c_213,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_164,c_207])).

tff(c_214,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_213])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_214,c_4])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  
% 2.10/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.29  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.10/1.29  
% 2.10/1.29  %Foreground sorts:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Background operators:
% 2.10/1.29  
% 2.10/1.29  
% 2.10/1.29  %Foreground operators:
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.10/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.10/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.10/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.10/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.10/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.10/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.10/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.29  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.10/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.10/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.10/1.29  
% 2.10/1.30  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.10/1.30  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.10/1.30  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.10/1.30  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.10/1.30  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.10/1.30  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.10/1.30  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.10/1.30  tff(f_90, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) => v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_tex_2)).
% 2.10/1.30  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.10/1.30  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.30  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.30  tff(c_103, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.10/1.30  tff(c_112, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_103])).
% 2.10/1.30  tff(c_115, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_112])).
% 2.10/1.30  tff(c_24, plain, (![B_36]: (k4_xboole_0(k1_tarski(B_36), k1_tarski(B_36))!=k1_tarski(B_36))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.10/1.30  tff(c_116, plain, (![B_36]: (k1_tarski(B_36)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_115, c_24])).
% 2.10/1.30  tff(c_44, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.10/1.30  tff(c_38, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.10/1.30  tff(c_42, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.10/1.30  tff(c_157, plain, (![A_71, B_72]: (k6_domain_1(A_71, B_72)=k1_tarski(B_72) | ~m1_subset_1(B_72, A_71) | v1_xboole_0(A_71))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.10/1.30  tff(c_160, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_157])).
% 2.10/1.30  tff(c_163, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_44, c_160])).
% 2.10/1.30  tff(c_40, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.10/1.30  tff(c_164, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_40])).
% 2.10/1.30  tff(c_169, plain, (![A_73, B_74]: (m1_subset_1(k6_domain_1(A_73, B_74), k1_zfmisc_1(A_73)) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.10/1.30  tff(c_178, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_163, c_169])).
% 2.10/1.30  tff(c_182, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_178])).
% 2.10/1.30  tff(c_183, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_44, c_182])).
% 2.10/1.30  tff(c_204, plain, (![B_79, A_80]: (v1_xboole_0(B_79) | ~v1_subset_1(B_79, A_80) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_zfmisc_1(A_80) | v1_xboole_0(A_80))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.10/1.30  tff(c_207, plain, (v1_xboole_0(k1_tarski('#skF_2')) | ~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_183, c_204])).
% 2.10/1.30  tff(c_213, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_164, c_207])).
% 2.10/1.30  tff(c_214, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_44, c_213])).
% 2.10/1.30  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.30  tff(c_218, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_214, c_4])).
% 2.10/1.30  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_218])).
% 2.10/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.30  
% 2.10/1.30  Inference rules
% 2.10/1.30  ----------------------
% 2.10/1.30  #Ref     : 0
% 2.10/1.30  #Sup     : 37
% 2.10/1.30  #Fact    : 0
% 2.10/1.30  #Define  : 0
% 2.10/1.31  #Split   : 1
% 2.10/1.31  #Chain   : 0
% 2.10/1.31  #Close   : 0
% 2.10/1.31  
% 2.10/1.31  Ordering : KBO
% 2.10/1.31  
% 2.10/1.31  Simplification rules
% 2.10/1.31  ----------------------
% 2.10/1.31  #Subsume      : 1
% 2.10/1.31  #Demod        : 8
% 2.10/1.31  #Tautology    : 27
% 2.10/1.31  #SimpNegUnit  : 6
% 2.10/1.31  #BackRed      : 2
% 2.10/1.31  
% 2.10/1.31  #Partial instantiations: 0
% 2.10/1.31  #Strategies tried      : 1
% 2.10/1.31  
% 2.10/1.31  Timing (in seconds)
% 2.10/1.31  ----------------------
% 2.10/1.31  Preprocessing        : 0.31
% 2.10/1.31  Parsing              : 0.16
% 2.10/1.31  CNF conversion       : 0.02
% 2.10/1.31  Main loop            : 0.15
% 2.10/1.31  Inferencing          : 0.06
% 2.10/1.31  Reduction            : 0.05
% 2.10/1.31  Demodulation         : 0.03
% 2.10/1.31  BG Simplification    : 0.01
% 2.10/1.31  Subsumption          : 0.02
% 2.10/1.31  Abstraction          : 0.01
% 2.10/1.31  MUC search           : 0.00
% 2.10/1.31  Cooper               : 0.00
% 2.10/1.31  Total                : 0.49
% 2.10/1.31  Index Insertion      : 0.00
% 2.10/1.31  Index Deletion       : 0.00
% 2.10/1.31  Index Matching       : 0.00
% 2.10/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
