%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:05 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :   48 (  64 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  98 expanded)
%              Number of equality atoms :   20 (  32 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_258,plain,(
    ! [A_56,B_57] :
      ( k5_setfam_1(A_56,B_57) = k3_tarski(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_267,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_258])).

tff(c_24,plain,
    ( k5_setfam_1('#skF_1','#skF_2') != '#skF_1'
    | ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_42,plain,(
    ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( m1_setfam_1('#skF_2','#skF_1')
    | k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47,plain,(
    k5_setfam_1('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_30])).

tff(c_125,plain,(
    ! [A_32,B_33] :
      ( k5_setfam_1(A_32,B_33) = k3_tarski(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(k1_zfmisc_1(A_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    k5_setfam_1('#skF_1','#skF_2') = k3_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_125])).

tff(c_135,plain,(
    k3_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_132])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [B_18,A_19] :
      ( m1_setfam_1(B_18,A_19)
      | ~ r1_tarski(A_19,k3_tarski(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_69,plain,(
    ! [B_18] : m1_setfam_1(B_18,k3_tarski(B_18)) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_145,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_69])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_145])).

tff(c_156,plain,(
    k5_setfam_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_268,plain,(
    k3_tarski('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_267,c_156])).

tff(c_157,plain,(
    m1_setfam_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_158,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | ~ m1_subset_1(A_34,k1_zfmisc_1(B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_162,plain,(
    r1_tarski('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_22,c_158])).

tff(c_10,plain,(
    ! [A_5] : k3_tarski(k1_zfmisc_1(A_5)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_223,plain,(
    ! [A_50,B_51] :
      ( r1_tarski(k3_tarski(A_50),k3_tarski(B_51))
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_234,plain,(
    ! [A_50,A_5] :
      ( r1_tarski(k3_tarski(A_50),A_5)
      | ~ r1_tarski(A_50,k1_zfmisc_1(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_223])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,k3_tarski(B_7))
      | ~ m1_setfam_1(B_7,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_187,plain,(
    ! [B_42,A_43] :
      ( B_42 = A_43
      | ~ r1_tarski(B_42,A_43)
      | ~ r1_tarski(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_394,plain,(
    ! [B_77,A_78] :
      ( k3_tarski(B_77) = A_78
      | ~ r1_tarski(k3_tarski(B_77),A_78)
      | ~ m1_setfam_1(B_77,A_78) ) ),
    inference(resolution,[status(thm)],[c_12,c_187])).

tff(c_485,plain,(
    ! [A_83,A_84] :
      ( k3_tarski(A_83) = A_84
      | ~ m1_setfam_1(A_83,A_84)
      | ~ r1_tarski(A_83,k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_234,c_394])).

tff(c_492,plain,
    ( k3_tarski('#skF_2') = '#skF_1'
    | ~ m1_setfam_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_162,c_485])).

tff(c_500,plain,(
    k3_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_492])).

tff(c_502,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:20:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.33  
% 2.01/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.33  %$ r1_tarski > m1_subset_1 > m1_setfam_1 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.01/1.33  
% 2.01/1.33  %Foreground sorts:
% 2.01/1.33  
% 2.01/1.33  
% 2.01/1.33  %Background operators:
% 2.01/1.33  
% 2.01/1.33  
% 2.01/1.33  %Foreground operators:
% 2.01/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.33  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.01/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.33  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.01/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.33  
% 2.35/1.34  tff(f_56, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.35/1.34  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.35/1.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.35/1.34  tff(f_41, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.35/1.34  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.35/1.34  tff(f_37, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.35/1.34  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.35/1.34  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.34  tff(c_258, plain, (![A_56, B_57]: (k5_setfam_1(A_56, B_57)=k3_tarski(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.34  tff(c_267, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_22, c_258])).
% 2.35/1.34  tff(c_24, plain, (k5_setfam_1('#skF_1', '#skF_2')!='#skF_1' | ~m1_setfam_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.34  tff(c_42, plain, (~m1_setfam_1('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_24])).
% 2.35/1.34  tff(c_30, plain, (m1_setfam_1('#skF_2', '#skF_1') | k5_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.35/1.34  tff(c_47, plain, (k5_setfam_1('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_42, c_30])).
% 2.35/1.34  tff(c_125, plain, (![A_32, B_33]: (k5_setfam_1(A_32, B_33)=k3_tarski(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(k1_zfmisc_1(A_32))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.35/1.34  tff(c_132, plain, (k5_setfam_1('#skF_1', '#skF_2')=k3_tarski('#skF_2')), inference(resolution, [status(thm)], [c_22, c_125])).
% 2.35/1.34  tff(c_135, plain, (k3_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47, c_132])).
% 2.35/1.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.34  tff(c_57, plain, (![B_18, A_19]: (m1_setfam_1(B_18, A_19) | ~r1_tarski(A_19, k3_tarski(B_18)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.34  tff(c_69, plain, (![B_18]: (m1_setfam_1(B_18, k3_tarski(B_18)))), inference(resolution, [status(thm)], [c_6, c_57])).
% 2.35/1.34  tff(c_145, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_135, c_69])).
% 2.35/1.34  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_145])).
% 2.35/1.34  tff(c_156, plain, (k5_setfam_1('#skF_1', '#skF_2')!='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 2.35/1.34  tff(c_268, plain, (k3_tarski('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_267, c_156])).
% 2.35/1.34  tff(c_157, plain, (m1_setfam_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_24])).
% 2.35/1.34  tff(c_158, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | ~m1_subset_1(A_34, k1_zfmisc_1(B_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.35/1.34  tff(c_162, plain, (r1_tarski('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_22, c_158])).
% 2.35/1.34  tff(c_10, plain, (![A_5]: (k3_tarski(k1_zfmisc_1(A_5))=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.35/1.34  tff(c_223, plain, (![A_50, B_51]: (r1_tarski(k3_tarski(A_50), k3_tarski(B_51)) | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.35/1.34  tff(c_234, plain, (![A_50, A_5]: (r1_tarski(k3_tarski(A_50), A_5) | ~r1_tarski(A_50, k1_zfmisc_1(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_223])).
% 2.35/1.34  tff(c_12, plain, (![A_6, B_7]: (r1_tarski(A_6, k3_tarski(B_7)) | ~m1_setfam_1(B_7, A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.35/1.34  tff(c_187, plain, (![B_42, A_43]: (B_42=A_43 | ~r1_tarski(B_42, A_43) | ~r1_tarski(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.35/1.34  tff(c_394, plain, (![B_77, A_78]: (k3_tarski(B_77)=A_78 | ~r1_tarski(k3_tarski(B_77), A_78) | ~m1_setfam_1(B_77, A_78))), inference(resolution, [status(thm)], [c_12, c_187])).
% 2.35/1.34  tff(c_485, plain, (![A_83, A_84]: (k3_tarski(A_83)=A_84 | ~m1_setfam_1(A_83, A_84) | ~r1_tarski(A_83, k1_zfmisc_1(A_84)))), inference(resolution, [status(thm)], [c_234, c_394])).
% 2.35/1.34  tff(c_492, plain, (k3_tarski('#skF_2')='#skF_1' | ~m1_setfam_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_162, c_485])).
% 2.35/1.34  tff(c_500, plain, (k3_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_492])).
% 2.35/1.34  tff(c_502, plain, $false, inference(negUnitSimplification, [status(thm)], [c_268, c_500])).
% 2.35/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.35/1.34  
% 2.35/1.34  Inference rules
% 2.35/1.34  ----------------------
% 2.35/1.34  #Ref     : 0
% 2.35/1.34  #Sup     : 99
% 2.35/1.34  #Fact    : 0
% 2.35/1.34  #Define  : 0
% 2.35/1.34  #Split   : 3
% 2.35/1.34  #Chain   : 0
% 2.35/1.34  #Close   : 0
% 2.35/1.34  
% 2.35/1.34  Ordering : KBO
% 2.35/1.34  
% 2.35/1.34  Simplification rules
% 2.35/1.34  ----------------------
% 2.35/1.34  #Subsume      : 6
% 2.35/1.34  #Demod        : 33
% 2.35/1.34  #Tautology    : 36
% 2.35/1.34  #SimpNegUnit  : 4
% 2.35/1.34  #BackRed      : 1
% 2.35/1.34  
% 2.35/1.34  #Partial instantiations: 0
% 2.35/1.34  #Strategies tried      : 1
% 2.35/1.34  
% 2.35/1.34  Timing (in seconds)
% 2.35/1.34  ----------------------
% 2.35/1.34  Preprocessing        : 0.29
% 2.35/1.34  Parsing              : 0.16
% 2.35/1.34  CNF conversion       : 0.02
% 2.35/1.34  Main loop            : 0.25
% 2.35/1.34  Inferencing          : 0.10
% 2.35/1.34  Reduction            : 0.07
% 2.35/1.34  Demodulation         : 0.05
% 2.35/1.34  BG Simplification    : 0.01
% 2.35/1.34  Subsumption          : 0.05
% 2.35/1.34  Abstraction          : 0.01
% 2.35/1.34  MUC search           : 0.00
% 2.35/1.34  Cooper               : 0.00
% 2.35/1.34  Total                : 0.57
% 2.35/1.34  Index Insertion      : 0.00
% 2.35/1.34  Index Deletion       : 0.00
% 2.35/1.34  Index Matching       : 0.00
% 2.35/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
