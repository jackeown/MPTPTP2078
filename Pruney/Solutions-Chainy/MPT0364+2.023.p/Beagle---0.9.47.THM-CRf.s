%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:42 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   50 (  74 expanded)
%              Number of leaves         :   19 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 137 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_20,plain,
    ( ~ r1_tarski('#skF_2','#skF_3')
    | ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_33,plain,(
    ~ r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_26,plain,
    ( r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_26])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k3_subset_1(A_28,B_29)
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_39])).

tff(c_6,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_xboole_0(A_5,k4_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_93,plain,(
    ! [A_36] :
      ( r1_xboole_0(A_36,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_tarski(A_36,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_6])).

tff(c_96,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_93,c_33])).

tff(c_102,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_96])).

tff(c_103,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_121,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_121])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_139,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_4])).

tff(c_105,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_105])).

tff(c_107,plain,(
    r1_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_107,c_2])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_129,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_121])).

tff(c_164,plain,(
    ! [A_44,B_45,C_46] :
      ( r1_tarski(A_44,k4_xboole_0(B_45,C_46))
      | ~ r1_xboole_0(A_44,C_46)
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [A_44] :
      ( r1_tarski(A_44,k3_subset_1('#skF_1','#skF_2'))
      | ~ r1_xboole_0(A_44,'#skF_2')
      | ~ r1_tarski(A_44,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_164])).

tff(c_181,plain,(
    ! [B_51,C_52,A_53] :
      ( r1_tarski(B_51,C_52)
      | ~ r1_tarski(k3_subset_1(A_53,C_52),k3_subset_1(A_53,B_51))
      | ~ m1_subset_1(C_52,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_185,plain,(
    ! [C_52] :
      ( r1_tarski('#skF_2',C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
      | ~ r1_xboole_0(k3_subset_1('#skF_1',C_52),'#skF_2')
      | ~ r1_tarski(k3_subset_1('#skF_1',C_52),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_167,c_181])).

tff(c_196,plain,(
    ! [C_54] :
      ( r1_tarski('#skF_2',C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1('#skF_1'))
      | ~ r1_xboole_0(k3_subset_1('#skF_1',C_54),'#skF_2')
      | ~ r1_tarski(k3_subset_1('#skF_1',C_54),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_185])).

tff(c_207,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_111,c_196])).

tff(c_217,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_16,c_207])).

tff(c_219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:39:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  
% 1.95/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.21  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 1.95/1.21  
% 1.95/1.21  %Foreground sorts:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Background operators:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Foreground operators:
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.95/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.95/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.21  
% 2.05/1.22  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 2.05/1.22  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.05/1.22  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 2.05/1.22  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.05/1.22  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.05/1.22  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.05/1.22  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.05/1.22  tff(c_20, plain, (~r1_tarski('#skF_2', '#skF_3') | ~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.05/1.22  tff(c_33, plain, (~r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_20])).
% 2.05/1.22  tff(c_26, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.05/1.22  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_33, c_26])).
% 2.05/1.22  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.05/1.22  tff(c_39, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k3_subset_1(A_28, B_29) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.05/1.22  tff(c_46, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_39])).
% 2.05/1.22  tff(c_6, plain, (![A_5, C_7, B_6]: (r1_xboole_0(A_5, k4_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.22  tff(c_93, plain, (![A_36]: (r1_xboole_0(A_36, k3_subset_1('#skF_1', '#skF_3')) | ~r1_tarski(A_36, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_6])).
% 2.05/1.22  tff(c_96, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_93, c_33])).
% 2.05/1.22  tff(c_102, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_96])).
% 2.05/1.22  tff(c_103, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.05/1.22  tff(c_121, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.05/1.22  tff(c_128, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_121])).
% 2.05/1.22  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.05/1.22  tff(c_139, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_128, c_4])).
% 2.05/1.22  tff(c_105, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_26])).
% 2.05/1.22  tff(c_106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_105])).
% 2.05/1.22  tff(c_107, plain, (r1_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 2.05/1.22  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.22  tff(c_111, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_107, c_2])).
% 2.05/1.22  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.05/1.22  tff(c_129, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_121])).
% 2.05/1.22  tff(c_164, plain, (![A_44, B_45, C_46]: (r1_tarski(A_44, k4_xboole_0(B_45, C_46)) | ~r1_xboole_0(A_44, C_46) | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.05/1.22  tff(c_167, plain, (![A_44]: (r1_tarski(A_44, k3_subset_1('#skF_1', '#skF_2')) | ~r1_xboole_0(A_44, '#skF_2') | ~r1_tarski(A_44, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_164])).
% 2.05/1.22  tff(c_181, plain, (![B_51, C_52, A_53]: (r1_tarski(B_51, C_52) | ~r1_tarski(k3_subset_1(A_53, C_52), k3_subset_1(A_53, B_51)) | ~m1_subset_1(C_52, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.05/1.22  tff(c_185, plain, (![C_52]: (r1_tarski('#skF_2', C_52) | ~m1_subset_1(C_52, k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~r1_xboole_0(k3_subset_1('#skF_1', C_52), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', C_52), '#skF_1'))), inference(resolution, [status(thm)], [c_167, c_181])).
% 2.05/1.22  tff(c_196, plain, (![C_54]: (r1_tarski('#skF_2', C_54) | ~m1_subset_1(C_54, k1_zfmisc_1('#skF_1')) | ~r1_xboole_0(k3_subset_1('#skF_1', C_54), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', C_54), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_185])).
% 2.05/1.22  tff(c_207, plain, (r1_tarski('#skF_2', '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_111, c_196])).
% 2.05/1.22  tff(c_217, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_16, c_207])).
% 2.05/1.22  tff(c_219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_217])).
% 2.05/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.22  
% 2.05/1.22  Inference rules
% 2.05/1.22  ----------------------
% 2.05/1.22  #Ref     : 0
% 2.05/1.22  #Sup     : 47
% 2.05/1.22  #Fact    : 0
% 2.05/1.22  #Define  : 0
% 2.05/1.22  #Split   : 2
% 2.05/1.22  #Chain   : 0
% 2.05/1.22  #Close   : 0
% 2.05/1.22  
% 2.05/1.22  Ordering : KBO
% 2.05/1.22  
% 2.05/1.22  Simplification rules
% 2.05/1.22  ----------------------
% 2.05/1.22  #Subsume      : 9
% 2.05/1.22  #Demod        : 11
% 2.05/1.22  #Tautology    : 13
% 2.05/1.22  #SimpNegUnit  : 4
% 2.05/1.22  #BackRed      : 0
% 2.05/1.22  
% 2.05/1.22  #Partial instantiations: 0
% 2.05/1.22  #Strategies tried      : 1
% 2.05/1.22  
% 2.05/1.22  Timing (in seconds)
% 2.05/1.22  ----------------------
% 2.05/1.23  Preprocessing        : 0.29
% 2.05/1.23  Parsing              : 0.16
% 2.05/1.23  CNF conversion       : 0.02
% 2.05/1.23  Main loop            : 0.18
% 2.05/1.23  Inferencing          : 0.07
% 2.05/1.23  Reduction            : 0.05
% 2.05/1.23  Demodulation         : 0.03
% 2.05/1.23  BG Simplification    : 0.01
% 2.05/1.23  Subsumption          : 0.03
% 2.05/1.23  Abstraction          : 0.01
% 2.05/1.23  MUC search           : 0.00
% 2.05/1.23  Cooper               : 0.00
% 2.05/1.23  Total                : 0.51
% 2.05/1.23  Index Insertion      : 0.00
% 2.05/1.23  Index Deletion       : 0.00
% 2.05/1.23  Index Matching       : 0.00
% 2.05/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
