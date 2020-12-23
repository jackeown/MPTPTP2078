%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:33 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   55 (  65 expanded)
%              Number of leaves         :   26 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   72 (  95 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_58,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_30,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_135,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    ! [B_47,A_10] :
      ( r1_tarski(B_47,A_10)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_135,c_10])).

tff(c_147,plain,(
    ! [B_49,A_50] :
      ( r1_tarski(B_49,A_50)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_142])).

tff(c_164,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_147])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_172,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_164,c_8])).

tff(c_228,plain,(
    ! [A_51,B_52,C_53] : k3_xboole_0(k3_xboole_0(A_51,B_52),C_53) = k3_xboole_0(A_51,k3_xboole_0(B_52,C_53)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_45,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_29,A_30] : r1_tarski(k3_xboole_0(B_29,A_30),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_6])).

tff(c_343,plain,(
    ! [A_55,B_56,C_57] : r1_tarski(k3_xboole_0(A_55,k3_xboole_0(B_56,C_57)),C_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_60])).

tff(c_371,plain,(
    ! [A_55] : r1_tarski(k3_xboole_0(A_55,'#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_343])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_123,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_126,plain,(
    ! [C_14,A_10] :
      ( m1_subset_1(C_14,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_123])).

tff(c_129,plain,(
    ! [C_14,A_10] :
      ( m1_subset_1(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_126])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1864,plain,(
    ! [A_107,C_108,B_109] :
      ( r1_tarski(k3_subset_1(A_107,C_108),k3_subset_1(A_107,B_109))
      | ~ r1_tarski(B_109,C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_463,plain,(
    ! [A_61,B_62,C_63] :
      ( k9_subset_1(A_61,B_62,C_63) = k3_xboole_0(B_62,C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_476,plain,(
    ! [B_62] : k9_subset_1('#skF_3',B_62,'#skF_5') = k3_xboole_0(B_62,'#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_463])).

tff(c_38,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_509,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_38])).

tff(c_1870,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1864,c_509])).

tff(c_1877,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_1870])).

tff(c_1881,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_1877])).

tff(c_1888,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_1881])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.52  
% 3.47/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.52  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.47/1.52  
% 3.47/1.52  %Foreground sorts:
% 3.47/1.52  
% 3.47/1.52  
% 3.47/1.52  %Background operators:
% 3.47/1.52  
% 3.47/1.52  
% 3.47/1.52  %Foreground operators:
% 3.47/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.47/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.52  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.52  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.47/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.47/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.47/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.52  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.47/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.53  
% 3.47/1.54  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 3.47/1.54  tff(f_58, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.47/1.54  tff(f_55, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.47/1.54  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.47/1.54  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.47/1.54  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.47/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.47/1.54  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.47/1.54  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.47/1.54  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.47/1.54  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.47/1.54  tff(c_30, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.47/1.54  tff(c_135, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.47/1.54  tff(c_10, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.47/1.54  tff(c_142, plain, (![B_47, A_10]: (r1_tarski(B_47, A_10) | ~m1_subset_1(B_47, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_135, c_10])).
% 3.47/1.54  tff(c_147, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_30, c_142])).
% 3.47/1.54  tff(c_164, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_147])).
% 3.47/1.54  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.47/1.54  tff(c_172, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_164, c_8])).
% 3.47/1.54  tff(c_228, plain, (![A_51, B_52, C_53]: (k3_xboole_0(k3_xboole_0(A_51, B_52), C_53)=k3_xboole_0(A_51, k3_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.47/1.54  tff(c_45, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.47/1.54  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.47/1.54  tff(c_60, plain, (![B_29, A_30]: (r1_tarski(k3_xboole_0(B_29, A_30), A_30))), inference(superposition, [status(thm), theory('equality')], [c_45, c_6])).
% 3.47/1.54  tff(c_343, plain, (![A_55, B_56, C_57]: (r1_tarski(k3_xboole_0(A_55, k3_xboole_0(B_56, C_57)), C_57))), inference(superposition, [status(thm), theory('equality')], [c_228, c_60])).
% 3.47/1.54  tff(c_371, plain, (![A_55]: (r1_tarski(k3_xboole_0(A_55, '#skF_5'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_172, c_343])).
% 3.47/1.54  tff(c_12, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.47/1.54  tff(c_123, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.47/1.54  tff(c_126, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(resolution, [status(thm)], [c_12, c_123])).
% 3.47/1.54  tff(c_129, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(negUnitSimplification, [status(thm)], [c_30, c_126])).
% 3.47/1.54  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.47/1.54  tff(c_1864, plain, (![A_107, C_108, B_109]: (r1_tarski(k3_subset_1(A_107, C_108), k3_subset_1(A_107, B_109)) | ~r1_tarski(B_109, C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(A_107)) | ~m1_subset_1(B_109, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.47/1.54  tff(c_463, plain, (![A_61, B_62, C_63]: (k9_subset_1(A_61, B_62, C_63)=k3_xboole_0(B_62, C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.47/1.54  tff(c_476, plain, (![B_62]: (k9_subset_1('#skF_3', B_62, '#skF_5')=k3_xboole_0(B_62, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_463])).
% 3.47/1.54  tff(c_38, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.47/1.54  tff(c_509, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_476, c_38])).
% 3.47/1.54  tff(c_1870, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1864, c_509])).
% 3.47/1.54  tff(c_1877, plain, (~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_1870])).
% 3.47/1.54  tff(c_1881, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_129, c_1877])).
% 3.47/1.54  tff(c_1888, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_371, c_1881])).
% 3.47/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.54  
% 3.47/1.54  Inference rules
% 3.47/1.54  ----------------------
% 3.47/1.54  #Ref     : 0
% 3.47/1.54  #Sup     : 448
% 3.47/1.54  #Fact    : 0
% 3.47/1.54  #Define  : 0
% 3.47/1.54  #Split   : 0
% 3.47/1.54  #Chain   : 0
% 3.47/1.54  #Close   : 0
% 3.47/1.54  
% 3.47/1.54  Ordering : KBO
% 3.47/1.54  
% 3.47/1.54  Simplification rules
% 3.47/1.54  ----------------------
% 3.47/1.54  #Subsume      : 6
% 3.47/1.54  #Demod        : 331
% 3.47/1.54  #Tautology    : 271
% 3.47/1.54  #SimpNegUnit  : 2
% 3.47/1.54  #BackRed      : 1
% 3.47/1.54  
% 3.47/1.54  #Partial instantiations: 0
% 3.47/1.54  #Strategies tried      : 1
% 3.47/1.54  
% 3.47/1.54  Timing (in seconds)
% 3.47/1.54  ----------------------
% 3.47/1.54  Preprocessing        : 0.29
% 3.47/1.54  Parsing              : 0.15
% 3.47/1.54  CNF conversion       : 0.02
% 3.47/1.54  Main loop            : 0.49
% 3.47/1.54  Inferencing          : 0.15
% 3.47/1.54  Reduction            : 0.21
% 3.47/1.54  Demodulation         : 0.17
% 3.47/1.54  BG Simplification    : 0.02
% 3.47/1.54  Subsumption          : 0.07
% 3.47/1.54  Abstraction          : 0.02
% 3.47/1.54  MUC search           : 0.00
% 3.47/1.54  Cooper               : 0.00
% 3.47/1.54  Total                : 0.81
% 3.47/1.54  Index Insertion      : 0.00
% 3.47/1.54  Index Deletion       : 0.00
% 3.47/1.54  Index Matching       : 0.00
% 3.47/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
