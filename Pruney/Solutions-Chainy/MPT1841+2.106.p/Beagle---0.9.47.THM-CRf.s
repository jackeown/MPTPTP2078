%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:42 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   69 ( 117 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_100,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_88,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_10,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k2_xboole_0(A_8,B_9)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_6,B_7] : k3_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_167,plain,(
    ! [A_51,B_52] : k5_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k5_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_167])).

tff(c_186,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_179])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_182,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_167])).

tff(c_204,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_182])).

tff(c_20,plain,(
    ! [B_19] : k4_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) != k1_tarski(B_19) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_205,plain,(
    ! [B_19] : k1_tarski(B_19) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_20])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_38,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_237,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_240,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_237])).

tff(c_243,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_240])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_244,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_243,c_36])).

tff(c_249,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k6_domain_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_258,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_249])).

tff(c_262,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_258])).

tff(c_263,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_262])).

tff(c_358,plain,(
    ! [B_71,A_72] :
      ( ~ v1_subset_1(B_71,A_72)
      | v1_xboole_0(B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_72))
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_364,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_263,c_358])).

tff(c_373,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_244,c_364])).

tff(c_374,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_373])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_378,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_374,c_4])).

tff(c_382,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_205,c_378])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  
% 2.16/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.28  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.16/1.28  
% 2.16/1.28  %Foreground sorts:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Background operators:
% 2.16/1.28  
% 2.16/1.28  
% 2.16/1.28  %Foreground operators:
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.16/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.16/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.16/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.16/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.16/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.16/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.16/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.16/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.16/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.16/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.16/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.16/1.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.16/1.28  
% 2.16/1.29  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.16/1.29  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 2.16/1.29  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.16/1.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.16/1.29  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.16/1.29  tff(f_100, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.16/1.29  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.16/1.29  tff(f_67, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.16/1.29  tff(f_88, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.16/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.16/1.29  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k2_xboole_0(A_8, B_9))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.16/1.29  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, k2_xboole_0(A_6, B_7))=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.16/1.29  tff(c_167, plain, (![A_51, B_52]: (k5_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.16/1.29  tff(c_179, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k5_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_167])).
% 2.16/1.29  tff(c_186, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_179])).
% 2.16/1.29  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.16/1.29  tff(c_182, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_167])).
% 2.16/1.29  tff(c_204, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_182])).
% 2.16/1.29  tff(c_20, plain, (![B_19]: (k4_xboole_0(k1_tarski(B_19), k1_tarski(B_19))!=k1_tarski(B_19))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.16/1.29  tff(c_205, plain, (![B_19]: (k1_tarski(B_19)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_204, c_20])).
% 2.16/1.29  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.16/1.29  tff(c_34, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.16/1.29  tff(c_38, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.16/1.29  tff(c_237, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.16/1.29  tff(c_240, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_237])).
% 2.16/1.29  tff(c_243, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_240])).
% 2.16/1.29  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.16/1.29  tff(c_244, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_243, c_36])).
% 2.16/1.29  tff(c_249, plain, (![A_65, B_66]: (m1_subset_1(k6_domain_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.16/1.29  tff(c_258, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_243, c_249])).
% 2.16/1.29  tff(c_262, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_258])).
% 2.16/1.29  tff(c_263, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_262])).
% 2.16/1.29  tff(c_358, plain, (![B_71, A_72]: (~v1_subset_1(B_71, A_72) | v1_xboole_0(B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_72)) | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.16/1.29  tff(c_364, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_263, c_358])).
% 2.16/1.29  tff(c_373, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_244, c_364])).
% 2.16/1.29  tff(c_374, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_373])).
% 2.16/1.29  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.16/1.29  tff(c_378, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_374, c_4])).
% 2.16/1.29  tff(c_382, plain, $false, inference(negUnitSimplification, [status(thm)], [c_205, c_378])).
% 2.16/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  Inference rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Ref     : 0
% 2.16/1.29  #Sup     : 75
% 2.16/1.29  #Fact    : 0
% 2.16/1.29  #Define  : 0
% 2.16/1.29  #Split   : 1
% 2.16/1.29  #Chain   : 0
% 2.16/1.29  #Close   : 0
% 2.16/1.29  
% 2.16/1.29  Ordering : KBO
% 2.16/1.29  
% 2.16/1.29  Simplification rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Subsume      : 3
% 2.16/1.29  #Demod        : 22
% 2.16/1.29  #Tautology    : 50
% 2.16/1.30  #SimpNegUnit  : 11
% 2.16/1.30  #BackRed      : 4
% 2.16/1.30  
% 2.16/1.30  #Partial instantiations: 0
% 2.16/1.30  #Strategies tried      : 1
% 2.16/1.30  
% 2.16/1.30  Timing (in seconds)
% 2.16/1.30  ----------------------
% 2.16/1.30  Preprocessing        : 0.31
% 2.16/1.30  Parsing              : 0.17
% 2.16/1.30  CNF conversion       : 0.02
% 2.16/1.30  Main loop            : 0.21
% 2.16/1.30  Inferencing          : 0.08
% 2.16/1.30  Reduction            : 0.06
% 2.16/1.30  Demodulation         : 0.05
% 2.16/1.30  BG Simplification    : 0.01
% 2.16/1.30  Subsumption          : 0.03
% 2.16/1.30  Abstraction          : 0.01
% 2.16/1.30  MUC search           : 0.00
% 2.16/1.30  Cooper               : 0.00
% 2.16/1.30  Total                : 0.55
% 2.16/1.30  Index Insertion      : 0.00
% 2.16/1.30  Index Deletion       : 0.00
% 2.16/1.30  Index Matching       : 0.00
% 2.16/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
