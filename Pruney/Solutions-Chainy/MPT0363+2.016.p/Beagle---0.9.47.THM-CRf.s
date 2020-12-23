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
% DateTime   : Thu Dec  3 09:56:38 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :    5
%              Number of atoms          :   70 ( 108 expanded)
%              Number of equality atoms :    6 (   7 expanded)
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

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_30,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_65,plain,(
    ! [B_31,A_32] :
      ( r2_hidden(B_31,A_32)
      | ~ m1_subset_1(B_31,A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [B_31,A_9] :
      ( r1_tarski(B_31,A_9)
      | ~ m1_subset_1(B_31,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_65,c_8])).

tff(c_168,plain,(
    ! [B_48,A_49] :
      ( r1_tarski(B_48,A_49)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_69])).

tff(c_181,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_168])).

tff(c_36,plain,
    ( ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_73,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_42,plain,
    ( r1_xboole_0('#skF_4','#skF_5')
    | r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_99,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_42])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_114,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_130,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_114])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_xboole_0(k4_xboole_0(A_4,B_5),B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_109,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_xboole_0(A_39,C_40)
      | ~ r1_xboole_0(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_39,B_5,A_4] :
      ( r1_xboole_0(A_39,B_5)
      | ~ r1_tarski(A_39,k4_xboole_0(A_4,B_5)) ) ),
    inference(resolution,[status(thm)],[c_4,c_109])).

tff(c_158,plain,(
    ! [A_47] :
      ( r1_xboole_0(A_47,'#skF_5')
      | ~ r1_tarski(A_47,k3_subset_1('#skF_3','#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_112])).

tff(c_161,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_99,c_158])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_161])).

tff(c_167,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_215,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_231,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_215])).

tff(c_262,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(A_65,k4_xboole_0(B_66,C_67))
      | ~ r1_xboole_0(A_65,C_67)
      | ~ r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_285,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_xboole_0(A_70,'#skF_5')
      | ~ r1_tarski(A_70,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_262])).

tff(c_166,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_293,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_285,c_166])).

tff(c_299,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_167,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.34  
% 2.24/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.24/1.34  
% 2.24/1.34  %Foreground sorts:
% 2.24/1.34  
% 2.24/1.34  
% 2.24/1.34  %Background operators:
% 2.24/1.34  
% 2.24/1.34  
% 2.24/1.34  %Foreground operators:
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.34  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.24/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.24/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.24/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.24/1.34  
% 2.24/1.35  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 2.24/1.35  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.24/1.35  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.24/1.35  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.24/1.35  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.24/1.35  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.24/1.35  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.24/1.35  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.24/1.35  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.35  tff(c_30, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.35  tff(c_65, plain, (![B_31, A_32]: (r2_hidden(B_31, A_32) | ~m1_subset_1(B_31, A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.35  tff(c_8, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.24/1.35  tff(c_69, plain, (![B_31, A_9]: (r1_tarski(B_31, A_9) | ~m1_subset_1(B_31, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_65, c_8])).
% 2.24/1.35  tff(c_168, plain, (![B_48, A_49]: (r1_tarski(B_48, A_49) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)))), inference(negUnitSimplification, [status(thm)], [c_30, c_69])).
% 2.24/1.35  tff(c_181, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_168])).
% 2.24/1.35  tff(c_36, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.35  tff(c_73, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_36])).
% 2.24/1.35  tff(c_42, plain, (r1_xboole_0('#skF_4', '#skF_5') | r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.35  tff(c_99, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_73, c_42])).
% 2.24/1.35  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.24/1.35  tff(c_114, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.35  tff(c_130, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_114])).
% 2.24/1.35  tff(c_4, plain, (![A_4, B_5]: (r1_xboole_0(k4_xboole_0(A_4, B_5), B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.35  tff(c_109, plain, (![A_39, C_40, B_41]: (r1_xboole_0(A_39, C_40) | ~r1_xboole_0(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.24/1.35  tff(c_112, plain, (![A_39, B_5, A_4]: (r1_xboole_0(A_39, B_5) | ~r1_tarski(A_39, k4_xboole_0(A_4, B_5)))), inference(resolution, [status(thm)], [c_4, c_109])).
% 2.24/1.35  tff(c_158, plain, (![A_47]: (r1_xboole_0(A_47, '#skF_5') | ~r1_tarski(A_47, k3_subset_1('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_130, c_112])).
% 2.24/1.35  tff(c_161, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_99, c_158])).
% 2.24/1.35  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_161])).
% 2.24/1.35  tff(c_167, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_36])).
% 2.24/1.35  tff(c_215, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.24/1.35  tff(c_231, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_32, c_215])).
% 2.24/1.35  tff(c_262, plain, (![A_65, B_66, C_67]: (r1_tarski(A_65, k4_xboole_0(B_66, C_67)) | ~r1_xboole_0(A_65, C_67) | ~r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.24/1.35  tff(c_285, plain, (![A_70]: (r1_tarski(A_70, k3_subset_1('#skF_3', '#skF_5')) | ~r1_xboole_0(A_70, '#skF_5') | ~r1_tarski(A_70, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_231, c_262])).
% 2.24/1.35  tff(c_166, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_36])).
% 2.24/1.35  tff(c_293, plain, (~r1_xboole_0('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_285, c_166])).
% 2.24/1.35  tff(c_299, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_181, c_167, c_293])).
% 2.24/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.35  
% 2.24/1.35  Inference rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Ref     : 0
% 2.24/1.35  #Sup     : 61
% 2.24/1.35  #Fact    : 0
% 2.24/1.35  #Define  : 0
% 2.24/1.35  #Split   : 2
% 2.24/1.35  #Chain   : 0
% 2.24/1.35  #Close   : 0
% 2.24/1.35  
% 2.24/1.35  Ordering : KBO
% 2.24/1.35  
% 2.24/1.35  Simplification rules
% 2.24/1.35  ----------------------
% 2.24/1.35  #Subsume      : 10
% 2.24/1.35  #Demod        : 4
% 2.24/1.35  #Tautology    : 21
% 2.24/1.35  #SimpNegUnit  : 6
% 2.24/1.35  #BackRed      : 0
% 2.24/1.35  
% 2.24/1.35  #Partial instantiations: 0
% 2.24/1.35  #Strategies tried      : 1
% 2.24/1.35  
% 2.24/1.35  Timing (in seconds)
% 2.24/1.35  ----------------------
% 2.24/1.36  Preprocessing        : 0.33
% 2.24/1.36  Parsing              : 0.17
% 2.24/1.36  CNF conversion       : 0.03
% 2.24/1.36  Main loop            : 0.20
% 2.24/1.36  Inferencing          : 0.08
% 2.24/1.36  Reduction            : 0.06
% 2.24/1.36  Demodulation         : 0.03
% 2.24/1.36  BG Simplification    : 0.02
% 2.24/1.36  Subsumption          : 0.04
% 2.24/1.36  Abstraction          : 0.01
% 2.24/1.36  MUC search           : 0.00
% 2.24/1.36  Cooper               : 0.00
% 2.24/1.36  Total                : 0.56
% 2.24/1.36  Index Insertion      : 0.00
% 2.24/1.36  Index Deletion       : 0.00
% 2.24/1.36  Index Matching       : 0.00
% 2.24/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
