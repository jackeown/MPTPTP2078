%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:45 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  55 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  80 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_30,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_39,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_36])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    ! [A_13] : ~ v1_xboole_0(k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_94,plain,(
    ! [B_35,A_36] :
      ( r2_hidden(B_35,A_36)
      | ~ m1_subset_1(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_9,A_5] :
      ( r1_tarski(C_9,A_5)
      | ~ r2_hidden(C_9,k1_zfmisc_1(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_101,plain,(
    ! [B_35,A_5] :
      ( r1_tarski(B_35,A_5)
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5)) ) ),
    inference(resolution,[status(thm)],[c_94,c_10])).

tff(c_106,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(B_37,A_38)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_38)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_101])).

tff(c_119,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_106])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_133,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_119,c_8])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [C_9,A_5] :
      ( r2_hidden(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_82,plain,(
    ! [B_31,A_32] :
      ( m1_subset_1(B_31,A_32)
      | ~ r2_hidden(B_31,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_85,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | v1_xboole_0(k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(resolution,[status(thm)],[c_12,c_82])).

tff(c_88,plain,(
    ! [C_9,A_5] :
      ( m1_subset_1(C_9,k1_zfmisc_1(A_5))
      | ~ r1_tarski(C_9,A_5) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_85])).

tff(c_195,plain,(
    ! [A_51,B_52,C_53] :
      ( k4_subset_1(A_51,B_52,C_53) = k2_xboole_0(B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_243,plain,(
    ! [A_56,B_57,C_58] :
      ( k4_subset_1(A_56,B_57,C_58) = k2_xboole_0(B_57,C_58)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56))
      | ~ r1_tarski(C_58,A_56) ) ),
    inference(resolution,[status(thm)],[c_88,c_195])).

tff(c_254,plain,(
    ! [C_59] :
      ( k4_subset_1('#skF_3','#skF_4',C_59) = k2_xboole_0('#skF_4',C_59)
      | ~ r1_tarski(C_59,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_38,c_243])).

tff(c_263,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_254])).

tff(c_267,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_263])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:50:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.34  
% 2.22/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.34  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.22/1.34  
% 2.22/1.34  %Foreground sorts:
% 2.22/1.34  
% 2.22/1.34  
% 2.22/1.34  %Background operators:
% 2.22/1.34  
% 2.22/1.34  
% 2.22/1.34  %Foreground operators:
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.34  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.22/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.22/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.34  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.22/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.22/1.34  
% 2.22/1.36  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.22/1.36  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.22/1.36  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.22/1.36  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.22/1.36  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.22/1.36  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.22/1.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.22/1.36  tff(f_66, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.22/1.36  tff(c_30, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.36  tff(c_36, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.36  tff(c_39, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_36])).
% 2.22/1.36  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.22/1.36  tff(c_32, plain, (![A_13]: (~v1_xboole_0(k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.22/1.36  tff(c_94, plain, (![B_35, A_36]: (r2_hidden(B_35, A_36) | ~m1_subset_1(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.36  tff(c_10, plain, (![C_9, A_5]: (r1_tarski(C_9, A_5) | ~r2_hidden(C_9, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.36  tff(c_101, plain, (![B_35, A_5]: (r1_tarski(B_35, A_5) | ~m1_subset_1(B_35, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)))), inference(resolution, [status(thm)], [c_94, c_10])).
% 2.22/1.36  tff(c_106, plain, (![B_37, A_38]: (r1_tarski(B_37, A_38) | ~m1_subset_1(B_37, k1_zfmisc_1(A_38)))), inference(negUnitSimplification, [status(thm)], [c_32, c_101])).
% 2.22/1.36  tff(c_119, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_106])).
% 2.22/1.36  tff(c_8, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.22/1.36  tff(c_133, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_119, c_8])).
% 2.22/1.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.22/1.36  tff(c_12, plain, (![C_9, A_5]: (r2_hidden(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.22/1.36  tff(c_82, plain, (![B_31, A_32]: (m1_subset_1(B_31, A_32) | ~r2_hidden(B_31, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.36  tff(c_85, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | v1_xboole_0(k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(resolution, [status(thm)], [c_12, c_82])).
% 2.22/1.36  tff(c_88, plain, (![C_9, A_5]: (m1_subset_1(C_9, k1_zfmisc_1(A_5)) | ~r1_tarski(C_9, A_5))), inference(negUnitSimplification, [status(thm)], [c_32, c_85])).
% 2.22/1.36  tff(c_195, plain, (![A_51, B_52, C_53]: (k4_subset_1(A_51, B_52, C_53)=k2_xboole_0(B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, k1_zfmisc_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.22/1.36  tff(c_243, plain, (![A_56, B_57, C_58]: (k4_subset_1(A_56, B_57, C_58)=k2_xboole_0(B_57, C_58) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)) | ~r1_tarski(C_58, A_56))), inference(resolution, [status(thm)], [c_88, c_195])).
% 2.22/1.36  tff(c_254, plain, (![C_59]: (k4_subset_1('#skF_3', '#skF_4', C_59)=k2_xboole_0('#skF_4', C_59) | ~r1_tarski(C_59, '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_243])).
% 2.22/1.36  tff(c_263, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_254])).
% 2.22/1.36  tff(c_267, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_263])).
% 2.22/1.36  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39, c_267])).
% 2.22/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.36  
% 2.22/1.36  Inference rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Ref     : 0
% 2.22/1.36  #Sup     : 49
% 2.22/1.36  #Fact    : 0
% 2.22/1.36  #Define  : 0
% 2.22/1.36  #Split   : 1
% 2.22/1.36  #Chain   : 0
% 2.22/1.36  #Close   : 0
% 2.22/1.36  
% 2.22/1.36  Ordering : KBO
% 2.22/1.36  
% 2.22/1.36  Simplification rules
% 2.22/1.36  ----------------------
% 2.22/1.36  #Subsume      : 6
% 2.22/1.36  #Demod        : 10
% 2.22/1.36  #Tautology    : 20
% 2.22/1.36  #SimpNegUnit  : 3
% 2.22/1.36  #BackRed      : 0
% 2.22/1.36  
% 2.22/1.36  #Partial instantiations: 0
% 2.22/1.36  #Strategies tried      : 1
% 2.22/1.36  
% 2.22/1.36  Timing (in seconds)
% 2.22/1.36  ----------------------
% 2.22/1.36  Preprocessing        : 0.32
% 2.22/1.36  Parsing              : 0.17
% 2.22/1.36  CNF conversion       : 0.02
% 2.22/1.36  Main loop            : 0.19
% 2.22/1.36  Inferencing          : 0.07
% 2.22/1.36  Reduction            : 0.05
% 2.22/1.36  Demodulation         : 0.04
% 2.22/1.36  BG Simplification    : 0.01
% 2.22/1.36  Subsumption          : 0.05
% 2.22/1.36  Abstraction          : 0.01
% 2.22/1.36  MUC search           : 0.00
% 2.22/1.36  Cooper               : 0.00
% 2.22/1.36  Total                : 0.55
% 2.22/1.36  Index Insertion      : 0.00
% 2.22/1.36  Index Deletion       : 0.00
% 2.22/1.36  Index Matching       : 0.00
% 2.22/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
