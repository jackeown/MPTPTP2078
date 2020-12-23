%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:06 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   75 ( 111 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(m1_setfam_1,type,(
    m1_setfam_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_341,plain,(
    ! [A_76,B_77] :
      ( k5_setfam_1(A_76,B_77) = k3_tarski(B_77)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(k1_zfmisc_1(A_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_354,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_341])).

tff(c_30,plain,
    ( k5_setfam_1('#skF_1','#skF_2') != '#skF_1'
    | ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_60,plain,(
    ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,
    ( m1_setfam_1('#skF_2','#skF_1')
    | k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_61,plain,(
    k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_36])).

tff(c_185,plain,(
    ! [A_49,B_50] :
      ( k5_setfam_1(A_49,B_50) = k3_tarski(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(k1_zfmisc_1(A_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_192,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_185])).

tff(c_199,plain,(
    k3_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_192])).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_37,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_79,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(resolution,[status(thm)],[c_37,c_79])).

tff(c_20,plain,(
    ! [B_11,A_10] :
      ( m1_setfam_1(B_11,A_10)
      | ~ r1_tarski(A_10,k3_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,(
    ! [B_11] : m1_setfam_1(B_11,k3_tarski(B_11)) ),
    inference(resolution,[status(thm)],[c_92,c_20])).

tff(c_208,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_97])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_208])).

tff(c_225,plain,(
    k5_setfam_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_357,plain,(
    k3_tarski('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_225])).

tff(c_226,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_234,plain,(
    ! [A_55,B_56] :
      ( r1_tarski(A_55,B_56)
      | ~ m1_subset_1(A_55,k1_zfmisc_1(B_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_245,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_234])).

tff(c_12,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_278,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(k3_tarski(A_64),k3_tarski(B_65))
      | ~ r1_tarski(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_287,plain,(
    ! [A_64,A_7] :
      ( r1_tarski(k3_tarski(A_64),A_7)
      | ~ r1_tarski(A_64,k1_zfmisc_1(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_278])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,k3_tarski(B_11))
      | ~ m1_setfam_1(B_11,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_315,plain,(
    ! [A_72,B_73] :
      ( r2_xboole_0(A_72,B_73)
      | B_73 = A_72
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_371,plain,(
    ! [B_79,A_80] :
      ( ~ r1_tarski(B_79,A_80)
      | B_79 = A_80
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(resolution,[status(thm)],[c_315,c_8])).

tff(c_491,plain,(
    ! [B_97,A_98] :
      ( k3_tarski(B_97) = A_98
      | ~ r1_tarski(k3_tarski(B_97),A_98)
      | ~ m1_setfam_1(B_97,A_98) ) ),
    inference(resolution,[status(thm)],[c_18,c_371])).

tff(c_546,plain,(
    ! [A_101,A_102] :
      ( k3_tarski(A_101) = A_102
      | ~ m1_setfam_1(A_101,A_102)
      | ~ r1_tarski(A_101,k1_zfmisc_1(A_102)) ) ),
    inference(resolution,[status(thm)],[c_287,c_491])).

tff(c_553,plain,
    ( k3_tarski('#skF_2') = '#skF_1'
    | ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_245,c_546])).

tff(c_561,plain,(
    k3_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_553])).

tff(c_563,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_357,c_561])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:34:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.40  
% 2.25/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.40  %$ r2_xboole_0 > r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.25/1.40  
% 2.25/1.40  %Foreground sorts:
% 2.25/1.40  
% 2.25/1.40  
% 2.25/1.40  %Background operators:
% 2.25/1.40  
% 2.25/1.40  
% 2.25/1.40  %Foreground operators:
% 2.25/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.40  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.25/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.40  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.25/1.40  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.25/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.25/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.40  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.25/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.40  
% 2.25/1.42  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.25/1.42  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.25/1.42  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.25/1.42  tff(f_47, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.25/1.42  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.25/1.42  tff(f_51, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.25/1.42  tff(f_43, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.25/1.42  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.25/1.42  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.25/1.42  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.25/1.42  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.42  tff(c_341, plain, (![A_76, B_77]: (k5_setfam_1(A_76, B_77)=k3_tarski(B_77) | ~m1_subset_1(B_77, k1_zfmisc_1(k1_zfmisc_1(A_76))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.42  tff(c_354, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_28, c_341])).
% 2.25/1.42  tff(c_30, plain, (k5_setfam_1('#skF_1', '#skF_2')!='#skF_1' | ~m1_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.42  tff(c_60, plain, (~m1_setfam_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_30])).
% 2.25/1.42  tff(c_36, plain, (m1_setfam_1('#skF_2', '#skF_1') | k5_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.42  tff(c_61, plain, (k5_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_60, c_36])).
% 2.25/1.42  tff(c_185, plain, (![A_49, B_50]: (k5_setfam_1(A_49, B_50)=k3_tarski(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(k1_zfmisc_1(A_49))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.25/1.42  tff(c_192, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_28, c_185])).
% 2.25/1.42  tff(c_199, plain, (k3_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_61, c_192])).
% 2.25/1.42  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.25/1.42  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.25/1.42  tff(c_37, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 2.25/1.42  tff(c_79, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.42  tff(c_92, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(resolution, [status(thm)], [c_37, c_79])).
% 2.25/1.42  tff(c_20, plain, (![B_11, A_10]: (m1_setfam_1(B_11, A_10) | ~r1_tarski(A_10, k3_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.25/1.42  tff(c_97, plain, (![B_11]: (m1_setfam_1(B_11, k3_tarski(B_11)))), inference(resolution, [status(thm)], [c_92, c_20])).
% 2.25/1.42  tff(c_208, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_199, c_97])).
% 2.25/1.42  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_208])).
% 2.25/1.42  tff(c_225, plain, (k5_setfam_1('#skF_1', '#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 2.25/1.42  tff(c_357, plain, (k3_tarski('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_225])).
% 2.25/1.42  tff(c_226, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_30])).
% 2.25/1.42  tff(c_234, plain, (![A_55, B_56]: (r1_tarski(A_55, B_56) | ~m1_subset_1(A_55, k1_zfmisc_1(B_56)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.42  tff(c_245, plain, (r1_tarski('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_234])).
% 2.25/1.42  tff(c_12, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.25/1.42  tff(c_278, plain, (![A_64, B_65]: (r1_tarski(k3_tarski(A_64), k3_tarski(B_65)) | ~r1_tarski(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.42  tff(c_287, plain, (![A_64, A_7]: (r1_tarski(k3_tarski(A_64), A_7) | ~r1_tarski(A_64, k1_zfmisc_1(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_278])).
% 2.25/1.42  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, k3_tarski(B_11)) | ~m1_setfam_1(B_11, A_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.25/1.42  tff(c_315, plain, (![A_72, B_73]: (r2_xboole_0(A_72, B_73) | B_73=A_72 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.25/1.42  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.25/1.42  tff(c_371, plain, (![B_79, A_80]: (~r1_tarski(B_79, A_80) | B_79=A_80 | ~r1_tarski(A_80, B_79))), inference(resolution, [status(thm)], [c_315, c_8])).
% 2.25/1.42  tff(c_491, plain, (![B_97, A_98]: (k3_tarski(B_97)=A_98 | ~r1_tarski(k3_tarski(B_97), A_98) | ~m1_setfam_1(B_97, A_98))), inference(resolution, [status(thm)], [c_18, c_371])).
% 2.25/1.42  tff(c_546, plain, (![A_101, A_102]: (k3_tarski(A_101)=A_102 | ~m1_setfam_1(A_101, A_102) | ~r1_tarski(A_101, k1_zfmisc_1(A_102)))), inference(resolution, [status(thm)], [c_287, c_491])).
% 2.25/1.42  tff(c_553, plain, (k3_tarski('#skF_2')='#skF_1' | ~m1_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_245, c_546])).
% 2.25/1.42  tff(c_561, plain, (k3_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_553])).
% 2.25/1.42  tff(c_563, plain, $false, inference(negUnitSimplification, [status(thm)], [c_357, c_561])).
% 2.25/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.42  
% 2.25/1.42  Inference rules
% 2.25/1.42  ----------------------
% 2.25/1.42  #Ref     : 0
% 2.25/1.42  #Sup     : 109
% 2.25/1.42  #Fact    : 0
% 2.25/1.42  #Define  : 0
% 2.25/1.42  #Split   : 2
% 2.25/1.42  #Chain   : 0
% 2.25/1.42  #Close   : 0
% 2.25/1.42  
% 2.25/1.42  Ordering : KBO
% 2.25/1.42  
% 2.25/1.42  Simplification rules
% 2.25/1.42  ----------------------
% 2.25/1.42  #Subsume      : 6
% 2.25/1.42  #Demod        : 36
% 2.25/1.42  #Tautology    : 42
% 2.25/1.42  #SimpNegUnit  : 4
% 2.25/1.42  #BackRed      : 1
% 2.25/1.42  
% 2.25/1.42  #Partial instantiations: 0
% 2.25/1.42  #Strategies tried      : 1
% 2.25/1.42  
% 2.25/1.42  Timing (in seconds)
% 2.25/1.42  ----------------------
% 2.25/1.42  Preprocessing        : 0.33
% 2.25/1.42  Parsing              : 0.17
% 2.25/1.42  CNF conversion       : 0.02
% 2.25/1.42  Main loop            : 0.25
% 2.25/1.42  Inferencing          : 0.10
% 2.25/1.42  Reduction            : 0.07
% 2.25/1.42  Demodulation         : 0.05
% 2.25/1.42  BG Simplification    : 0.01
% 2.25/1.42  Subsumption          : 0.05
% 2.25/1.42  Abstraction          : 0.01
% 2.25/1.42  MUC search           : 0.00
% 2.25/1.42  Cooper               : 0.00
% 2.25/1.42  Total                : 0.61
% 2.25/1.42  Index Insertion      : 0.00
% 2.25/1.42  Index Deletion       : 0.00
% 2.25/1.42  Index Matching       : 0.00
% 2.25/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
