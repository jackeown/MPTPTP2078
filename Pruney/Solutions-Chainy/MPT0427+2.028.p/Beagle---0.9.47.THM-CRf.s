%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:00 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 215 expanded)
%              Number of leaves         :   22 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 440 expanded)
%              Number of equality atoms :   38 ( 183 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_133,plain,(
    ! [A_38,B_39] :
      ( k6_setfam_1(A_38,B_39) = k1_setfam_1(B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_149,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_133])).

tff(c_239,plain,(
    ! [A_58,B_59] :
      ( k8_setfam_1(A_58,B_59) = k6_setfam_1(A_58,B_59)
      | k1_xboole_0 = B_59
      | ~ m1_subset_1(B_59,k1_zfmisc_1(k1_zfmisc_1(A_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_254,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_239])).

tff(c_267,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_254])).

tff(c_273,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_267])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_150,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_133])).

tff(c_257,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_30,c_239])).

tff(c_269,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_257])).

tff(c_348,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_269])).

tff(c_349,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_348])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_66,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_85,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_360,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_85])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_360])).

tff(c_364,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_348])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_4] :
      ( k8_setfam_1(A_4,k1_xboole_0) = A_4
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    ! [A_4] : k8_setfam_1(A_4,k1_xboole_0) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10])).

tff(c_281,plain,(
    ! [A_4] : k8_setfam_1(A_4,'#skF_2') = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_34])).

tff(c_26,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_297,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_281,c_26])).

tff(c_366,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_297])).

tff(c_14,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k8_setfam_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_370,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_14])).

tff(c_374,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_370])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_382,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_374,c_18])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_366,c_382])).

tff(c_389,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_setfam_1(B_16),k1_setfam_1(A_15))
      | k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_390,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_47,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_59,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_397,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_59])).

tff(c_407,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_85])).

tff(c_408,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_388,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_267])).

tff(c_410,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_26])).

tff(c_446,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_410])).

tff(c_449,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_446])).

tff(c_452,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_449])).

tff(c_454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_389,c_452])).

tff(c_455,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_457,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_455,c_26])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  %$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.40  
% 2.72/1.40  %Foreground sorts:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Background operators:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Foreground operators:
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.40  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.72/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.40  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.40  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.72/1.40  
% 2.72/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.72/1.41  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.72/1.41  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.72/1.41  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.72/1.41  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.72/1.41  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.72/1.41  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.72/1.41  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.72/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.41  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.72/1.41  tff(c_133, plain, (![A_38, B_39]: (k6_setfam_1(A_38, B_39)=k1_setfam_1(B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.72/1.41  tff(c_149, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_133])).
% 2.72/1.41  tff(c_239, plain, (![A_58, B_59]: (k8_setfam_1(A_58, B_59)=k6_setfam_1(A_58, B_59) | k1_xboole_0=B_59 | ~m1_subset_1(B_59, k1_zfmisc_1(k1_zfmisc_1(A_58))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.41  tff(c_254, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_32, c_239])).
% 2.72/1.41  tff(c_267, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_254])).
% 2.72/1.41  tff(c_273, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_267])).
% 2.72/1.41  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.72/1.41  tff(c_150, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_133])).
% 2.72/1.41  tff(c_257, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_30, c_239])).
% 2.72/1.41  tff(c_269, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_257])).
% 2.72/1.41  tff(c_348, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_273, c_269])).
% 2.72/1.41  tff(c_349, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_348])).
% 2.72/1.41  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.72/1.41  tff(c_66, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.41  tff(c_84, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_66])).
% 2.72/1.41  tff(c_85, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_84])).
% 2.72/1.41  tff(c_360, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_85])).
% 2.72/1.41  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_360])).
% 2.72/1.41  tff(c_364, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_348])).
% 2.72/1.41  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.41  tff(c_10, plain, (![A_4]: (k8_setfam_1(A_4, k1_xboole_0)=A_4 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_4))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.72/1.41  tff(c_34, plain, (![A_4]: (k8_setfam_1(A_4, k1_xboole_0)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_10])).
% 2.72/1.41  tff(c_281, plain, (![A_4]: (k8_setfam_1(A_4, '#skF_2')=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_273, c_34])).
% 2.72/1.41  tff(c_26, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.72/1.41  tff(c_297, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_281, c_26])).
% 2.72/1.41  tff(c_366, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_364, c_297])).
% 2.72/1.41  tff(c_14, plain, (![A_6, B_7]: (m1_subset_1(k8_setfam_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.72/1.41  tff(c_370, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_364, c_14])).
% 2.72/1.41  tff(c_374, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_370])).
% 2.72/1.41  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.41  tff(c_382, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_374, c_18])).
% 2.72/1.41  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_366, c_382])).
% 2.72/1.41  tff(c_389, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_267])).
% 2.72/1.41  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k1_setfam_1(B_16), k1_setfam_1(A_15)) | k1_xboole_0=A_15 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.72/1.41  tff(c_390, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_269])).
% 2.72/1.41  tff(c_47, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.72/1.41  tff(c_59, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(resolution, [status(thm)], [c_8, c_47])).
% 2.72/1.41  tff(c_397, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_390, c_59])).
% 2.72/1.41  tff(c_407, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_397, c_85])).
% 2.72/1.41  tff(c_408, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_269])).
% 2.72/1.41  tff(c_388, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_267])).
% 2.72/1.41  tff(c_410, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_388, c_26])).
% 2.72/1.41  tff(c_446, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_408, c_410])).
% 2.72/1.41  tff(c_449, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_446])).
% 2.72/1.41  tff(c_452, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_449])).
% 2.72/1.41  tff(c_454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_389, c_452])).
% 2.72/1.41  tff(c_455, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_84])).
% 2.72/1.41  tff(c_457, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_455, c_26])).
% 2.72/1.41  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_457])).
% 2.72/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.41  
% 2.72/1.41  Inference rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Ref     : 0
% 2.72/1.41  #Sup     : 84
% 2.72/1.41  #Fact    : 0
% 2.72/1.41  #Define  : 0
% 2.72/1.41  #Split   : 6
% 2.72/1.41  #Chain   : 0
% 2.72/1.41  #Close   : 0
% 2.72/1.41  
% 2.72/1.41  Ordering : KBO
% 2.72/1.41  
% 2.72/1.41  Simplification rules
% 2.72/1.41  ----------------------
% 2.72/1.41  #Subsume      : 6
% 2.72/1.41  #Demod        : 73
% 2.72/1.41  #Tautology    : 46
% 2.72/1.41  #SimpNegUnit  : 2
% 2.72/1.41  #BackRed      : 36
% 2.72/1.41  
% 2.72/1.41  #Partial instantiations: 0
% 2.72/1.41  #Strategies tried      : 1
% 2.72/1.41  
% 2.72/1.41  Timing (in seconds)
% 2.72/1.41  ----------------------
% 2.72/1.42  Preprocessing        : 0.32
% 2.72/1.42  Parsing              : 0.17
% 2.72/1.42  CNF conversion       : 0.02
% 2.72/1.42  Main loop            : 0.27
% 2.72/1.42  Inferencing          : 0.10
% 2.72/1.42  Reduction            : 0.09
% 2.72/1.42  Demodulation         : 0.06
% 2.72/1.42  BG Simplification    : 0.01
% 2.72/1.42  Subsumption          : 0.05
% 2.72/1.42  Abstraction          : 0.02
% 2.72/1.42  MUC search           : 0.00
% 2.72/1.42  Cooper               : 0.00
% 2.72/1.42  Total                : 0.63
% 2.72/1.42  Index Insertion      : 0.00
% 2.72/1.42  Index Deletion       : 0.00
% 2.72/1.42  Index Matching       : 0.00
% 2.72/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
