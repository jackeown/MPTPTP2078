%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:57 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  82 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,k3_subset_1(A,C))
             => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_68,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_63,plain,(
    ! [B_31,A_32] :
      ( r2_hidden(B_31,A_32)
      | ~ m1_subset_1(B_31,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_67,plain,(
    ! [B_31,A_9] :
      ( r1_tarski(B_31,A_9)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_63,c_10])).

tff(c_71,plain,(
    ! [B_33,A_34] :
      ( r1_tarski(B_33,A_34)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_67])).

tff(c_83,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_71])).

tff(c_36,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_107,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_123,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_107])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_47] :
      ( r1_xboole_0(A_47,'#skF_5')
      | ~ r1_tarski(A_47,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_4])).

tff(c_149,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_145])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_152,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_149,c_2])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_124,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_107])).

tff(c_158,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(A_49,k4_xboole_0(B_50,C_51))
      | ~ r1_xboole_0(A_49,C_51)
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_226,plain,(
    ! [A_58] :
      ( r1_tarski(A_58,k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_xboole_0(A_58,'#skF_4')
      | ~ r1_tarski(A_58,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_158])).

tff(c_34,plain,(
    ~ r1_tarski('#skF_5',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_238,plain,
    ( ~ r1_xboole_0('#skF_5','#skF_4')
    | ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_226,c_34])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_152,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:30:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.87/1.23  
% 1.87/1.23  %Foreground sorts:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Background operators:
% 1.87/1.23  
% 1.87/1.23  
% 1.87/1.23  %Foreground operators:
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.87/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.23  
% 2.13/1.24  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 2.13/1.24  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.13/1.24  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.13/1.24  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.13/1.24  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.13/1.24  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.13/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.13/1.24  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.13/1.24  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.24  tff(c_32, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.13/1.24  tff(c_63, plain, (![B_31, A_32]: (r2_hidden(B_31, A_32) | ~m1_subset_1(B_31, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.24  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.24  tff(c_67, plain, (![B_31, A_9]: (r1_tarski(B_31, A_9) | ~m1_subset_1(B_31, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_63, c_10])).
% 2.13/1.24  tff(c_71, plain, (![B_33, A_34]: (r1_tarski(B_33, A_34) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)))), inference(negUnitSimplification, [status(thm)], [c_32, c_67])).
% 2.13/1.24  tff(c_83, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_71])).
% 2.13/1.24  tff(c_36, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.24  tff(c_107, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.13/1.24  tff(c_123, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_107])).
% 2.13/1.24  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.24  tff(c_145, plain, (![A_47]: (r1_xboole_0(A_47, '#skF_5') | ~r1_tarski(A_47, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_123, c_4])).
% 2.13/1.24  tff(c_149, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_145])).
% 2.13/1.24  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.13/1.24  tff(c_152, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_149, c_2])).
% 2.13/1.24  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.24  tff(c_124, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_107])).
% 2.13/1.24  tff(c_158, plain, (![A_49, B_50, C_51]: (r1_tarski(A_49, k4_xboole_0(B_50, C_51)) | ~r1_xboole_0(A_49, C_51) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.24  tff(c_226, plain, (![A_58]: (r1_tarski(A_58, k3_subset_1('#skF_3', '#skF_4')) | ~r1_xboole_0(A_58, '#skF_4') | ~r1_tarski(A_58, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_158])).
% 2.13/1.24  tff(c_34, plain, (~r1_tarski('#skF_5', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.24  tff(c_238, plain, (~r1_xboole_0('#skF_5', '#skF_4') | ~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_226, c_34])).
% 2.13/1.24  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_152, c_238])).
% 2.13/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.24  
% 2.13/1.24  Inference rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Ref     : 0
% 2.13/1.24  #Sup     : 48
% 2.13/1.24  #Fact    : 0
% 2.13/1.24  #Define  : 0
% 2.13/1.24  #Split   : 0
% 2.13/1.24  #Chain   : 0
% 2.13/1.24  #Close   : 0
% 2.13/1.24  
% 2.13/1.24  Ordering : KBO
% 2.13/1.24  
% 2.13/1.24  Simplification rules
% 2.13/1.24  ----------------------
% 2.13/1.24  #Subsume      : 5
% 2.13/1.24  #Demod        : 6
% 2.13/1.24  #Tautology    : 20
% 2.13/1.24  #SimpNegUnit  : 2
% 2.13/1.24  #BackRed      : 0
% 2.13/1.24  
% 2.13/1.24  #Partial instantiations: 0
% 2.13/1.24  #Strategies tried      : 1
% 2.13/1.24  
% 2.13/1.24  Timing (in seconds)
% 2.13/1.24  ----------------------
% 2.13/1.24  Preprocessing        : 0.30
% 2.13/1.24  Parsing              : 0.16
% 2.13/1.24  CNF conversion       : 0.02
% 2.13/1.24  Main loop            : 0.18
% 2.13/1.24  Inferencing          : 0.07
% 2.13/1.24  Reduction            : 0.05
% 2.13/1.24  Demodulation         : 0.03
% 2.13/1.24  BG Simplification    : 0.01
% 2.13/1.24  Subsumption          : 0.04
% 2.13/1.24  Abstraction          : 0.01
% 2.13/1.24  MUC search           : 0.00
% 2.13/1.24  Cooper               : 0.00
% 2.13/1.24  Total                : 0.51
% 2.13/1.24  Index Insertion      : 0.00
% 2.13/1.24  Index Deletion       : 0.00
% 2.13/1.24  Index Matching       : 0.00
% 2.13/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
