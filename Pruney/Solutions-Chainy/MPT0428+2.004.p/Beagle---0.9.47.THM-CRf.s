%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:05 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   71 ( 117 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k5_setfam_1(A,B) = k3_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_41,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,(
    ! [A_47,B_48] :
      ( k5_setfam_1(A_47,B_48) = k3_tarski(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(k1_zfmisc_1(A_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_161,plain,(
    k5_setfam_1('#skF_3','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_157])).

tff(c_34,plain,
    ( k5_setfam_1('#skF_3','#skF_4') != '#skF_3'
    | ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_50,plain,(
    ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( m1_setfam_1('#skF_4','#skF_3')
    | k5_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_51,plain,(
    k5_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40])).

tff(c_94,plain,(
    ! [A_34,B_35] :
      ( k5_setfam_1(A_34,B_35) = k3_tarski(B_35)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(k1_zfmisc_1(A_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_97,plain,(
    k5_setfam_1('#skF_3','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_99,plain,(
    k3_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_97])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_57,plain,(
    ! [B_25,A_26] :
      ( m1_setfam_1(B_25,A_26)
      | ~ r1_tarski(A_26,k3_tarski(B_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    ! [B_25] : m1_setfam_1(B_25,k3_tarski(B_25)) ),
    inference(resolution,[status(thm)],[c_6,c_57])).

tff(c_103,plain,(
    m1_setfam_1('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_66])).

tff(c_113,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_103])).

tff(c_114,plain,(
    k5_setfam_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_162,plain,(
    k3_tarski('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_114])).

tff(c_115,plain,(
    m1_setfam_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_181,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k5_setfam_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_191,plain,
    ( m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_181])).

tff(c_195,plain,(
    m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_191])).

tff(c_20,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_130,plain,(
    ! [A_41,B_42] :
      ( r2_hidden(A_41,B_42)
      | v1_xboole_0(B_42)
      | ~ m1_subset_1(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_134,plain,(
    ! [A_41,A_3] :
      ( r1_tarski(A_41,A_3)
      | v1_xboole_0(k1_zfmisc_1(A_3))
      | ~ m1_subset_1(A_41,k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_137,plain,(
    ! [A_41,A_3] :
      ( r1_tarski(A_41,A_3)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_134])).

tff(c_199,plain,(
    r1_tarski(k3_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_195,c_137])).

tff(c_22,plain,(
    ! [A_9,B_10] :
      ( r1_tarski(A_9,k3_tarski(B_10))
      | ~ m1_setfam_1(B_10,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(B_45,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_148,plain,(
    ! [B_10,A_9] :
      ( k3_tarski(B_10) = A_9
      | ~ r1_tarski(k3_tarski(B_10),A_9)
      | ~ m1_setfam_1(B_10,A_9) ) ),
    inference(resolution,[status(thm)],[c_22,c_143])).

tff(c_211,plain,
    ( k3_tarski('#skF_4') = '#skF_3'
    | ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_199,c_148])).

tff(c_216,plain,(
    k3_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_211])).

tff(c_218,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:46:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.22  
% 1.90/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.22  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.90/1.22  
% 1.90/1.22  %Foreground sorts:
% 1.90/1.22  
% 1.90/1.22  
% 1.90/1.22  %Background operators:
% 1.90/1.22  
% 1.90/1.22  
% 1.90/1.22  %Foreground operators:
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.22  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 1.90/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.90/1.22  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.90/1.22  
% 2.09/1.23  tff(f_66, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.09/1.23  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.09/1.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.23  tff(f_45, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.09/1.23  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.09/1.23  tff(f_41, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.09/1.23  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.09/1.23  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.09/1.23  tff(c_32, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.23  tff(c_157, plain, (![A_47, B_48]: (k5_setfam_1(A_47, B_48)=k3_tarski(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(k1_zfmisc_1(A_47))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.23  tff(c_161, plain, (k5_setfam_1('#skF_3', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_32, c_157])).
% 2.09/1.23  tff(c_34, plain, (k5_setfam_1('#skF_3', '#skF_4')!='#skF_3' | ~m1_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.23  tff(c_50, plain, (~m1_setfam_1('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_34])).
% 2.09/1.24  tff(c_40, plain, (m1_setfam_1('#skF_4', '#skF_3') | k5_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.09/1.24  tff(c_51, plain, (k5_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_50, c_40])).
% 2.09/1.24  tff(c_94, plain, (![A_34, B_35]: (k5_setfam_1(A_34, B_35)=k3_tarski(B_35) | ~m1_subset_1(B_35, k1_zfmisc_1(k1_zfmisc_1(A_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.24  tff(c_97, plain, (k5_setfam_1('#skF_3', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_32, c_94])).
% 2.09/1.24  tff(c_99, plain, (k3_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_97])).
% 2.09/1.24  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.24  tff(c_57, plain, (![B_25, A_26]: (m1_setfam_1(B_25, A_26) | ~r1_tarski(A_26, k3_tarski(B_25)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.24  tff(c_66, plain, (![B_25]: (m1_setfam_1(B_25, k3_tarski(B_25)))), inference(resolution, [status(thm)], [c_6, c_57])).
% 2.09/1.24  tff(c_103, plain, (m1_setfam_1('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_99, c_66])).
% 2.09/1.24  tff(c_113, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_103])).
% 2.09/1.24  tff(c_114, plain, (k5_setfam_1('#skF_3', '#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.09/1.24  tff(c_162, plain, (k3_tarski('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_114])).
% 2.09/1.24  tff(c_115, plain, (m1_setfam_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 2.09/1.24  tff(c_181, plain, (![A_51, B_52]: (m1_subset_1(k5_setfam_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.09/1.24  tff(c_191, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_161, c_181])).
% 2.09/1.24  tff(c_195, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_191])).
% 2.09/1.24  tff(c_20, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.24  tff(c_130, plain, (![A_41, B_42]: (r2_hidden(A_41, B_42) | v1_xboole_0(B_42) | ~m1_subset_1(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.09/1.24  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.09/1.24  tff(c_134, plain, (![A_41, A_3]: (r1_tarski(A_41, A_3) | v1_xboole_0(k1_zfmisc_1(A_3)) | ~m1_subset_1(A_41, k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_130, c_8])).
% 2.09/1.24  tff(c_137, plain, (![A_41, A_3]: (r1_tarski(A_41, A_3) | ~m1_subset_1(A_41, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_20, c_134])).
% 2.09/1.24  tff(c_199, plain, (r1_tarski(k3_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_195, c_137])).
% 2.09/1.24  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, k3_tarski(B_10)) | ~m1_setfam_1(B_10, A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.09/1.24  tff(c_143, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(B_45, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.09/1.24  tff(c_148, plain, (![B_10, A_9]: (k3_tarski(B_10)=A_9 | ~r1_tarski(k3_tarski(B_10), A_9) | ~m1_setfam_1(B_10, A_9))), inference(resolution, [status(thm)], [c_22, c_143])).
% 2.09/1.24  tff(c_211, plain, (k3_tarski('#skF_4')='#skF_3' | ~m1_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_199, c_148])).
% 2.09/1.24  tff(c_216, plain, (k3_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_211])).
% 2.09/1.24  tff(c_218, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_216])).
% 2.09/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  Inference rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Ref     : 0
% 2.09/1.24  #Sup     : 36
% 2.09/1.24  #Fact    : 0
% 2.09/1.24  #Define  : 0
% 2.09/1.24  #Split   : 2
% 2.09/1.24  #Chain   : 0
% 2.09/1.24  #Close   : 0
% 2.09/1.24  
% 2.09/1.24  Ordering : KBO
% 2.09/1.24  
% 2.09/1.24  Simplification rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Subsume      : 0
% 2.09/1.24  #Demod        : 9
% 2.09/1.24  #Tautology    : 15
% 2.09/1.24  #SimpNegUnit  : 6
% 2.09/1.24  #BackRed      : 1
% 2.09/1.24  
% 2.09/1.24  #Partial instantiations: 0
% 2.09/1.24  #Strategies tried      : 1
% 2.09/1.24  
% 2.09/1.24  Timing (in seconds)
% 2.09/1.24  ----------------------
% 2.09/1.24  Preprocessing        : 0.31
% 2.09/1.24  Parsing              : 0.16
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.17
% 2.09/1.24  Inferencing          : 0.06
% 2.09/1.24  Reduction            : 0.05
% 2.09/1.24  Demodulation         : 0.04
% 2.09/1.24  BG Simplification    : 0.01
% 2.09/1.24  Subsumption          : 0.03
% 2.09/1.24  Abstraction          : 0.01
% 2.09/1.24  MUC search           : 0.00
% 2.09/1.24  Cooper               : 0.00
% 2.09/1.24  Total                : 0.51
% 2.09/1.24  Index Insertion      : 0.00
% 2.09/1.24  Index Deletion       : 0.00
% 2.09/1.24  Index Matching       : 0.00
% 2.09/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
