%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:49 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 133 expanded)
%              Number of leaves         :   21 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 250 expanded)
%              Number of equality atoms :   17 ( 100 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_24,B_25] : ~ r2_hidden(A_24,k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_67,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_93,plain,(
    ! [A_33,B_34] :
      ( k7_setfam_1(A_33,k7_setfam_1(A_33,B_34)) = B_34
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_98,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_101,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_98])).

tff(c_185,plain,(
    ! [A_56,D_57,B_58] :
      ( r2_hidden(k3_subset_1(A_56,D_57),B_58)
      | ~ r2_hidden(D_57,k7_setfam_1(A_56,B_58))
      | ~ m1_subset_1(D_57,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(k7_setfam_1(A_56,B_58),k1_zfmisc_1(k1_zfmisc_1(A_56)))
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_189,plain,(
    ! [D_57] :
      ( r2_hidden(k3_subset_1('#skF_2',D_57),k1_xboole_0)
      | ~ r2_hidden(D_57,k7_setfam_1('#skF_2',k1_xboole_0))
      | ~ m1_subset_1(D_57,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2')))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_185])).

tff(c_197,plain,(
    ! [D_57] :
      ( r2_hidden(k3_subset_1('#skF_2',D_57),k1_xboole_0)
      | ~ r2_hidden(D_57,'#skF_3')
      | ~ m1_subset_1(D_57,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_101,c_189])).

tff(c_198,plain,(
    ! [D_57] :
      ( ~ r2_hidden(D_57,'#skF_3')
      | ~ m1_subset_1(D_57,k1_zfmisc_1('#skF_2'))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_197])).

tff(c_202,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_205,plain,(
    ~ r1_tarski(k1_xboole_0,k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_202])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_205])).

tff(c_211,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_269,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_1'(A_65,B_66,C_67),C_67)
      | r2_hidden(k3_subset_1(A_65,'#skF_1'(A_65,B_66,C_67)),B_66)
      | k7_setfam_1(A_65,B_66) = C_67
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k1_zfmisc_1(A_65)))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(k1_zfmisc_1(A_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_288,plain,(
    ! [A_69,C_70] :
      ( r2_hidden('#skF_1'(A_69,k1_xboole_0,C_70),C_70)
      | k7_setfam_1(A_69,k1_xboole_0) = C_70
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k1_zfmisc_1(A_69)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_69))) ) ),
    inference(resolution,[status(thm)],[c_269,c_67])).

tff(c_290,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k7_setfam_1('#skF_2',k1_xboole_0) = k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_211,c_288])).

tff(c_301,plain,
    ( r2_hidden('#skF_1'('#skF_2',k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_101,c_290])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_67,c_301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.27  
% 2.18/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > k7_setfam_1 > k3_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.18/1.28  
% 2.18/1.28  %Foreground sorts:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Background operators:
% 2.18/1.28  
% 2.18/1.28  
% 2.18/1.28  %Foreground operators:
% 2.18/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.18/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.28  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.18/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.18/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.18/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.18/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.28  
% 2.18/1.29  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.18/1.29  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.18/1.29  tff(f_36, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.18/1.29  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.18/1.29  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.18/1.29  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.18/1.29  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.18/1.29  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.29  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.18/1.29  tff(c_64, plain, (![A_24, B_25]: (~r2_hidden(A_24, k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.18/1.29  tff(c_67, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_64])).
% 2.18/1.29  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.18/1.29  tff(c_30, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.18/1.29  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.29  tff(c_32, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.18/1.29  tff(c_93, plain, (![A_33, B_34]: (k7_setfam_1(A_33, k7_setfam_1(A_33, B_34))=B_34 | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.18/1.29  tff(c_98, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_36, c_93])).
% 2.18/1.29  tff(c_101, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_98])).
% 2.18/1.29  tff(c_185, plain, (![A_56, D_57, B_58]: (r2_hidden(k3_subset_1(A_56, D_57), B_58) | ~r2_hidden(D_57, k7_setfam_1(A_56, B_58)) | ~m1_subset_1(D_57, k1_zfmisc_1(A_56)) | ~m1_subset_1(k7_setfam_1(A_56, B_58), k1_zfmisc_1(k1_zfmisc_1(A_56))) | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_56))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.29  tff(c_189, plain, (![D_57]: (r2_hidden(k3_subset_1('#skF_2', D_57), k1_xboole_0) | ~r2_hidden(D_57, k7_setfam_1('#skF_2', k1_xboole_0)) | ~m1_subset_1(D_57, k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_101, c_185])).
% 2.18/1.29  tff(c_197, plain, (![D_57]: (r2_hidden(k3_subset_1('#skF_2', D_57), k1_xboole_0) | ~r2_hidden(D_57, '#skF_3') | ~m1_subset_1(D_57, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_101, c_189])).
% 2.18/1.29  tff(c_198, plain, (![D_57]: (~r2_hidden(D_57, '#skF_3') | ~m1_subset_1(D_57, k1_zfmisc_1('#skF_2')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2'))))), inference(negUnitSimplification, [status(thm)], [c_67, c_197])).
% 2.18/1.29  tff(c_202, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_198])).
% 2.18/1.29  tff(c_205, plain, (~r1_tarski(k1_xboole_0, k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_202])).
% 2.18/1.29  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_205])).
% 2.18/1.29  tff(c_211, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(splitRight, [status(thm)], [c_198])).
% 2.18/1.29  tff(c_269, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_1'(A_65, B_66, C_67), C_67) | r2_hidden(k3_subset_1(A_65, '#skF_1'(A_65, B_66, C_67)), B_66) | k7_setfam_1(A_65, B_66)=C_67 | ~m1_subset_1(C_67, k1_zfmisc_1(k1_zfmisc_1(A_65))) | ~m1_subset_1(B_66, k1_zfmisc_1(k1_zfmisc_1(A_65))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.18/1.29  tff(c_288, plain, (![A_69, C_70]: (r2_hidden('#skF_1'(A_69, k1_xboole_0, C_70), C_70) | k7_setfam_1(A_69, k1_xboole_0)=C_70 | ~m1_subset_1(C_70, k1_zfmisc_1(k1_zfmisc_1(A_69))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_69))))), inference(resolution, [status(thm)], [c_269, c_67])).
% 2.18/1.29  tff(c_290, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1('#skF_2', k1_xboole_0)=k1_xboole_0 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(resolution, [status(thm)], [c_211, c_288])).
% 2.18/1.29  tff(c_301, plain, (r2_hidden('#skF_1'('#skF_2', k1_xboole_0, k1_xboole_0), k1_xboole_0) | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_211, c_101, c_290])).
% 2.18/1.29  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_67, c_301])).
% 2.18/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.29  
% 2.18/1.29  Inference rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Ref     : 0
% 2.18/1.29  #Sup     : 58
% 2.18/1.29  #Fact    : 0
% 2.18/1.29  #Define  : 0
% 2.18/1.29  #Split   : 1
% 2.18/1.29  #Chain   : 0
% 2.18/1.29  #Close   : 0
% 2.18/1.29  
% 2.18/1.29  Ordering : KBO
% 2.18/1.29  
% 2.18/1.29  Simplification rules
% 2.18/1.29  ----------------------
% 2.18/1.29  #Subsume      : 3
% 2.18/1.29  #Demod        : 20
% 2.18/1.29  #Tautology    : 23
% 2.18/1.29  #SimpNegUnit  : 4
% 2.18/1.29  #BackRed      : 0
% 2.18/1.29  
% 2.18/1.29  #Partial instantiations: 0
% 2.18/1.29  #Strategies tried      : 1
% 2.18/1.29  
% 2.18/1.29  Timing (in seconds)
% 2.18/1.29  ----------------------
% 2.18/1.29  Preprocessing        : 0.29
% 2.18/1.29  Parsing              : 0.15
% 2.18/1.29  CNF conversion       : 0.02
% 2.18/1.29  Main loop            : 0.23
% 2.18/1.29  Inferencing          : 0.09
% 2.18/1.29  Reduction            : 0.06
% 2.18/1.29  Demodulation         : 0.04
% 2.18/1.29  BG Simplification    : 0.01
% 2.18/1.29  Subsumption          : 0.05
% 2.18/1.29  Abstraction          : 0.01
% 2.18/1.29  MUC search           : 0.00
% 2.18/1.29  Cooper               : 0.00
% 2.18/1.29  Total                : 0.55
% 2.18/1.29  Index Insertion      : 0.00
% 2.18/1.29  Index Deletion       : 0.00
% 2.18/1.29  Index Matching       : 0.00
% 2.18/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
