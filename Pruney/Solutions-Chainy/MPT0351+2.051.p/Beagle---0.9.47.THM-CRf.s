%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:43 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   61 (  95 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 116 expanded)
%              Number of equality atoms :   28 (  49 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_72,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_38,plain,(
    ! [A_25] : m1_subset_1(k2_subset_1(A_25),k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_48,plain,(
    ! [A_25] : m1_subset_1(A_25,k1_zfmisc_1(A_25)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_38])).

tff(c_310,plain,(
    ! [A_75,B_76,C_77] :
      ( k4_subset_1(A_75,B_76,C_77) = k2_xboole_0(B_76,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_324,plain,(
    ! [A_78,B_79] :
      ( k4_subset_1(A_78,B_79,A_78) = k2_xboole_0(B_79,A_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_48,c_310])).

tff(c_338,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_324])).

tff(c_44,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_47,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_36,c_44])).

tff(c_362,plain,(
    k2_xboole_0('#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_47])).

tff(c_40,plain,(
    ! [A_26] : ~ v1_xboole_0(k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_187,plain,(
    ! [B_57,A_58] :
      ( r2_hidden(B_57,A_58)
      | ~ m1_subset_1(B_57,A_58)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_12,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_194,plain,(
    ! [B_57,A_12] :
      ( r1_tarski(B_57,A_12)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_187,c_12])).

tff(c_208,plain,(
    ! [B_62,A_63] :
      ( r1_tarski(B_62,A_63)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_63)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_194])).

tff(c_225,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_208])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_234,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_225,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_93,plain,(
    ! [A_35,B_36] : k2_xboole_0(A_35,k3_xboole_0(A_35,B_36)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_102,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_93])).

tff(c_253,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_102])).

tff(c_367,plain,(
    ! [B_84] :
      ( k4_subset_1('#skF_3',B_84,'#skF_4') = k2_xboole_0(B_84,'#skF_4')
      | ~ m1_subset_1(B_84,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_310])).

tff(c_379,plain,(
    k4_subset_1('#skF_3','#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_367])).

tff(c_386,plain,(
    k4_subset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_379])).

tff(c_339,plain,(
    ! [A_80,C_81,B_82] :
      ( k4_subset_1(A_80,C_81,B_82) = k4_subset_1(A_80,B_82,C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(A_80))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_423,plain,(
    ! [A_88,B_89] :
      ( k4_subset_1(A_88,B_89,A_88) = k4_subset_1(A_88,A_88,B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_48,c_339])).

tff(c_432,plain,(
    k4_subset_1('#skF_3','#skF_3','#skF_4') = k4_subset_1('#skF_3','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_423])).

tff(c_438,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_338,c_432])).

tff(c_440,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_438])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:58:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.32  
% 2.38/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.32  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.38/1.32  
% 2.38/1.32  %Foreground sorts:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Background operators:
% 2.38/1.32  
% 2.38/1.32  
% 2.38/1.32  %Foreground operators:
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.32  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.38/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.38/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.38/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.38/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.38/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.38/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.38/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.38/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.32  
% 2.38/1.34  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.38/1.34  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.38/1.34  tff(f_69, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.38/1.34  tff(f_78, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.38/1.34  tff(f_72, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.38/1.34  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.38/1.34  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.38/1.34  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.38/1.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.38/1.34  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.38/1.34  tff(f_52, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.38/1.34  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.38/1.34  tff(c_36, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.38/1.34  tff(c_38, plain, (![A_25]: (m1_subset_1(k2_subset_1(A_25), k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.38/1.34  tff(c_48, plain, (![A_25]: (m1_subset_1(A_25, k1_zfmisc_1(A_25)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_38])).
% 2.38/1.34  tff(c_310, plain, (![A_75, B_76, C_77]: (k4_subset_1(A_75, B_76, C_77)=k2_xboole_0(B_76, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.38/1.34  tff(c_324, plain, (![A_78, B_79]: (k4_subset_1(A_78, B_79, A_78)=k2_xboole_0(B_79, A_78) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(resolution, [status(thm)], [c_48, c_310])).
% 2.38/1.34  tff(c_338, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_324])).
% 2.38/1.34  tff(c_44, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.38/1.34  tff(c_47, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_36, c_44])).
% 2.38/1.34  tff(c_362, plain, (k2_xboole_0('#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_47])).
% 2.38/1.34  tff(c_40, plain, (![A_26]: (~v1_xboole_0(k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.38/1.34  tff(c_187, plain, (![B_57, A_58]: (r2_hidden(B_57, A_58) | ~m1_subset_1(B_57, A_58) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.38/1.34  tff(c_12, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.34  tff(c_194, plain, (![B_57, A_12]: (r1_tarski(B_57, A_12) | ~m1_subset_1(B_57, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_187, c_12])).
% 2.38/1.34  tff(c_208, plain, (![B_62, A_63]: (r1_tarski(B_62, A_63) | ~m1_subset_1(B_62, k1_zfmisc_1(A_63)))), inference(negUnitSimplification, [status(thm)], [c_40, c_194])).
% 2.38/1.34  tff(c_225, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_208])).
% 2.38/1.34  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.34  tff(c_234, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_225, c_6])).
% 2.38/1.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.38/1.34  tff(c_93, plain, (![A_35, B_36]: (k2_xboole_0(A_35, k3_xboole_0(A_35, B_36))=A_35)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.34  tff(c_102, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_93])).
% 2.38/1.34  tff(c_253, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_234, c_102])).
% 2.38/1.34  tff(c_367, plain, (![B_84]: (k4_subset_1('#skF_3', B_84, '#skF_4')=k2_xboole_0(B_84, '#skF_4') | ~m1_subset_1(B_84, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_310])).
% 2.38/1.34  tff(c_379, plain, (k4_subset_1('#skF_3', '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_48, c_367])).
% 2.38/1.34  tff(c_386, plain, (k4_subset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_253, c_379])).
% 2.38/1.34  tff(c_339, plain, (![A_80, C_81, B_82]: (k4_subset_1(A_80, C_81, B_82)=k4_subset_1(A_80, B_82, C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(A_80)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.38/1.34  tff(c_423, plain, (![A_88, B_89]: (k4_subset_1(A_88, B_89, A_88)=k4_subset_1(A_88, A_88, B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_48, c_339])).
% 2.38/1.34  tff(c_432, plain, (k4_subset_1('#skF_3', '#skF_3', '#skF_4')=k4_subset_1('#skF_3', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_423])).
% 2.38/1.34  tff(c_438, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_386, c_338, c_432])).
% 2.38/1.34  tff(c_440, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_438])).
% 2.38/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  Inference rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Ref     : 0
% 2.38/1.34  #Sup     : 92
% 2.38/1.34  #Fact    : 0
% 2.38/1.34  #Define  : 0
% 2.38/1.34  #Split   : 0
% 2.38/1.34  #Chain   : 0
% 2.38/1.34  #Close   : 0
% 2.38/1.34  
% 2.38/1.34  Ordering : KBO
% 2.38/1.34  
% 2.38/1.34  Simplification rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Subsume      : 9
% 2.38/1.34  #Demod        : 24
% 2.38/1.34  #Tautology    : 52
% 2.38/1.34  #SimpNegUnit  : 3
% 2.38/1.34  #BackRed      : 1
% 2.38/1.34  
% 2.38/1.34  #Partial instantiations: 0
% 2.38/1.34  #Strategies tried      : 1
% 2.38/1.34  
% 2.38/1.34  Timing (in seconds)
% 2.38/1.34  ----------------------
% 2.38/1.34  Preprocessing        : 0.32
% 2.38/1.34  Parsing              : 0.17
% 2.38/1.34  CNF conversion       : 0.02
% 2.38/1.34  Main loop            : 0.23
% 2.38/1.34  Inferencing          : 0.09
% 2.38/1.34  Reduction            : 0.07
% 2.38/1.34  Demodulation         : 0.05
% 2.38/1.34  BG Simplification    : 0.02
% 2.38/1.34  Subsumption          : 0.04
% 2.38/1.34  Abstraction          : 0.01
% 2.38/1.34  MUC search           : 0.00
% 2.38/1.34  Cooper               : 0.00
% 2.38/1.34  Total                : 0.58
% 2.38/1.34  Index Insertion      : 0.00
% 2.38/1.34  Index Deletion       : 0.00
% 2.38/1.34  Index Matching       : 0.00
% 2.38/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
