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
% DateTime   : Thu Dec  3 09:58:04 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   56 (  77 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 118 expanded)
%              Number of equality atoms :   16 (  33 expanded)
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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( m1_setfam_1(B,A)
        <=> k5_setfam_1(A,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

tff(f_66,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_setfam_1(B,A)
    <=> r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_54,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(c_46,plain,
    ( m1_setfam_1('#skF_4','#skF_3')
    | k5_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_73,plain,(
    k5_setfam_1('#skF_3','#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_40,plain,
    ( k5_setfam_1('#skF_3','#skF_4') != '#skF_3'
    | ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_84,plain,(
    ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_40])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_137,plain,(
    ! [A_42,B_43] :
      ( k5_setfam_1(A_42,B_43) = k3_tarski(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_148,plain,(
    k5_setfam_1('#skF_3','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_137])).

tff(c_152,plain,(
    k3_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_148])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [B_27,A_28] :
      ( m1_setfam_1(B_27,A_28)
      | ~ r1_tarski(A_28,k3_tarski(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_71,plain,(
    ! [B_27] : m1_setfam_1(B_27,k3_tarski(B_27)) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_156,plain,(
    m1_setfam_1('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_71])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_156])).

tff(c_167,plain,(
    m1_setfam_1('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k3_tarski(B_12))
      | ~ m1_setfam_1(B_12,A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_228,plain,(
    ! [A_56,B_57] :
      ( k5_setfam_1(A_56,B_57) = k3_tarski(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_242,plain,(
    k5_setfam_1('#skF_3','#skF_4') = k3_tarski('#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_228])).

tff(c_168,plain,(
    k5_setfam_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_243,plain,(
    k3_tarski('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_168])).

tff(c_259,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k5_setfam_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_272,plain,
    ( m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_259])).

tff(c_277,plain,(
    m1_subset_1(k3_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_272])).

tff(c_28,plain,(
    ! [A_10] : ~ v1_xboole_0(k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_198,plain,(
    ! [B_52,A_53] :
      ( r2_hidden(B_52,A_53)
      | ~ m1_subset_1(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_205,plain,(
    ! [B_52,A_3] :
      ( r1_tarski(B_52,A_3)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_3))
      | v1_xboole_0(k1_zfmisc_1(A_3)) ) ),
    inference(resolution,[status(thm)],[c_198,c_8])).

tff(c_209,plain,(
    ! [B_52,A_3] :
      ( r1_tarski(B_52,A_3)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_3)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_205])).

tff(c_284,plain,(
    r1_tarski(k3_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_277,c_209])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_287,plain,
    ( k3_tarski('#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k3_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_284,c_2])).

tff(c_290,plain,(
    ~ r1_tarski('#skF_3',k3_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_243,c_287])).

tff(c_293,plain,(
    ~ m1_setfam_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_290])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.66  
% 2.51/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.51/1.66  %$ r2_hidden > r1_tarski > m1_subset_1 > m1_setfam_1 > v1_xboole_0 > k5_setfam_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.51/1.66  
% 2.51/1.66  %Foreground sorts:
% 2.51/1.66  
% 2.51/1.66  
% 2.51/1.66  %Background operators:
% 2.51/1.66  
% 2.51/1.66  
% 2.51/1.66  %Foreground operators:
% 2.51/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.51/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.66  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.66  tff(m1_setfam_1, type, m1_setfam_1: ($i * $i) > $o).
% 2.51/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.51/1.66  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 2.51/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.51/1.66  tff('#skF_4', type, '#skF_4': $i).
% 2.51/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.66  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.51/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.51/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.66  
% 2.67/1.68  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (m1_setfam_1(B, A) <=> (k5_setfam_1(A, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_setfam_1)).
% 2.67/1.68  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k5_setfam_1(A, B) = k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_setfam_1)).
% 2.67/1.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.67/1.68  tff(f_58, axiom, (![A, B]: (m1_setfam_1(B, A) <=> r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_setfam_1)).
% 2.67/1.68  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 2.67/1.68  tff(f_54, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.67/1.68  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.67/1.68  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.67/1.68  tff(c_46, plain, (m1_setfam_1('#skF_4', '#skF_3') | k5_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.68  tff(c_73, plain, (k5_setfam_1('#skF_3', '#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_46])).
% 2.67/1.68  tff(c_40, plain, (k5_setfam_1('#skF_3', '#skF_4')!='#skF_3' | ~m1_setfam_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.68  tff(c_84, plain, (~m1_setfam_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_40])).
% 2.67/1.68  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.68  tff(c_137, plain, (![A_42, B_43]: (k5_setfam_1(A_42, B_43)=k3_tarski(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.67/1.68  tff(c_148, plain, (k5_setfam_1('#skF_3', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_38, c_137])).
% 2.67/1.68  tff(c_152, plain, (k3_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_73, c_148])).
% 2.67/1.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.68  tff(c_62, plain, (![B_27, A_28]: (m1_setfam_1(B_27, A_28) | ~r1_tarski(A_28, k3_tarski(B_27)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.68  tff(c_71, plain, (![B_27]: (m1_setfam_1(B_27, k3_tarski(B_27)))), inference(resolution, [status(thm)], [c_6, c_62])).
% 2.67/1.68  tff(c_156, plain, (m1_setfam_1('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_152, c_71])).
% 2.67/1.68  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_156])).
% 2.67/1.68  tff(c_167, plain, (m1_setfam_1('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_46])).
% 2.67/1.68  tff(c_30, plain, (![A_11, B_12]: (r1_tarski(A_11, k3_tarski(B_12)) | ~m1_setfam_1(B_12, A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.67/1.68  tff(c_228, plain, (![A_56, B_57]: (k5_setfam_1(A_56, B_57)=k3_tarski(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.67/1.68  tff(c_242, plain, (k5_setfam_1('#skF_3', '#skF_4')=k3_tarski('#skF_4')), inference(resolution, [status(thm)], [c_38, c_228])).
% 2.67/1.68  tff(c_168, plain, (k5_setfam_1('#skF_3', '#skF_4')!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 2.67/1.68  tff(c_243, plain, (k3_tarski('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_242, c_168])).
% 2.67/1.68  tff(c_259, plain, (![A_60, B_61]: (m1_subset_1(k5_setfam_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.67/1.68  tff(c_272, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_242, c_259])).
% 2.67/1.68  tff(c_277, plain, (m1_subset_1(k3_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_272])).
% 2.67/1.68  tff(c_28, plain, (![A_10]: (~v1_xboole_0(k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.67/1.68  tff(c_198, plain, (![B_52, A_53]: (r2_hidden(B_52, A_53) | ~m1_subset_1(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.67/1.68  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.68  tff(c_205, plain, (![B_52, A_3]: (r1_tarski(B_52, A_3) | ~m1_subset_1(B_52, k1_zfmisc_1(A_3)) | v1_xboole_0(k1_zfmisc_1(A_3)))), inference(resolution, [status(thm)], [c_198, c_8])).
% 2.67/1.68  tff(c_209, plain, (![B_52, A_3]: (r1_tarski(B_52, A_3) | ~m1_subset_1(B_52, k1_zfmisc_1(A_3)))), inference(negUnitSimplification, [status(thm)], [c_28, c_205])).
% 2.67/1.68  tff(c_284, plain, (r1_tarski(k3_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_277, c_209])).
% 2.67/1.68  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.68  tff(c_287, plain, (k3_tarski('#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k3_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_284, c_2])).
% 2.67/1.68  tff(c_290, plain, (~r1_tarski('#skF_3', k3_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_243, c_287])).
% 2.67/1.68  tff(c_293, plain, (~m1_setfam_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_290])).
% 2.67/1.68  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_167, c_293])).
% 2.67/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.68  
% 2.67/1.68  Inference rules
% 2.67/1.68  ----------------------
% 2.67/1.68  #Ref     : 0
% 2.67/1.68  #Sup     : 51
% 2.67/1.68  #Fact    : 0
% 2.67/1.68  #Define  : 0
% 2.67/1.68  #Split   : 3
% 2.67/1.68  #Chain   : 0
% 2.67/1.68  #Close   : 0
% 2.67/1.68  
% 2.67/1.68  Ordering : KBO
% 2.67/1.68  
% 2.67/1.68  Simplification rules
% 2.67/1.68  ----------------------
% 2.67/1.68  #Subsume      : 10
% 2.67/1.68  #Demod        : 10
% 2.67/1.68  #Tautology    : 19
% 2.67/1.68  #SimpNegUnit  : 6
% 2.67/1.68  #BackRed      : 1
% 2.67/1.68  
% 2.67/1.68  #Partial instantiations: 0
% 2.67/1.68  #Strategies tried      : 1
% 2.67/1.68  
% 2.67/1.68  Timing (in seconds)
% 2.67/1.68  ----------------------
% 2.67/1.69  Preprocessing        : 0.49
% 2.67/1.69  Parsing              : 0.25
% 2.67/1.69  CNF conversion       : 0.03
% 2.67/1.69  Main loop            : 0.32
% 2.67/1.69  Inferencing          : 0.11
% 2.67/1.69  Reduction            : 0.09
% 2.67/1.69  Demodulation         : 0.06
% 2.67/1.69  BG Simplification    : 0.02
% 2.67/1.69  Subsumption          : 0.06
% 2.67/1.69  Abstraction          : 0.02
% 2.67/1.69  MUC search           : 0.00
% 2.67/1.69  Cooper               : 0.00
% 2.67/1.69  Total                : 0.85
% 2.67/1.69  Index Insertion      : 0.00
% 2.67/1.69  Index Deletion       : 0.00
% 2.67/1.69  Index Matching       : 0.00
% 2.67/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
