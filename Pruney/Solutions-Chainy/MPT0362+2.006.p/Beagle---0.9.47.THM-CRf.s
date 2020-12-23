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
% DateTime   : Thu Dec  3 09:56:33 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   57 (  68 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 101 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_45,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [B_29,A_30] : r1_tarski(k3_xboole_0(B_29,A_30),A_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_135,plain,(
    ! [B_47,A_48] :
      ( r2_hidden(B_47,A_48)
      | ~ m1_subset_1(B_47,A_48)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

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
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_172,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_164,c_8])).

tff(c_207,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_172])).

tff(c_228,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(A_51,B_52)
      | ~ r1_tarski(A_51,k3_xboole_0(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_286,plain,(
    ! [A_54] :
      ( r1_tarski(A_54,'#skF_3')
      | ~ r1_tarski(A_54,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_228])).

tff(c_300,plain,(
    ! [B_29] : r1_tarski(k3_xboole_0(B_29,'#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_286])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_123,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

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
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1350,plain,(
    ! [A_111,C_112,B_113] :
      ( r1_tarski(k3_subset_1(A_111,C_112),k3_subset_1(A_111,B_113))
      | ~ r1_tarski(B_113,C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(A_111))
      | ~ m1_subset_1(B_113,k1_zfmisc_1(A_111)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_344,plain,(
    ! [A_57,B_58,C_59] :
      ( k9_subset_1(A_57,B_58,C_59) = k3_xboole_0(B_58,C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_357,plain,(
    ! [B_58] : k9_subset_1('#skF_3',B_58,'#skF_5') = k3_xboole_0(B_58,'#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_344])).

tff(c_38,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_416,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_357,c_38])).

tff(c_1356,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1350,c_416])).

tff(c_1363,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4,c_1356])).

tff(c_1367,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_1363])).

tff(c_1374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_1367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:10:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.55  
% 3.50/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.50/1.55  
% 3.50/1.55  %Foreground sorts:
% 3.50/1.55  
% 3.50/1.55  
% 3.50/1.55  %Background operators:
% 3.50/1.55  
% 3.50/1.55  
% 3.50/1.55  %Foreground operators:
% 3.50/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.50/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.50/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.50/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.50/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.50/1.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.50/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.55  
% 3.50/1.57  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.50/1.57  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.50/1.57  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 3.50/1.57  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.50/1.57  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.50/1.57  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.50/1.57  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.50/1.57  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.50/1.57  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.50/1.57  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.50/1.57  tff(c_45, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.50/1.57  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.50/1.57  tff(c_60, plain, (![B_29, A_30]: (r1_tarski(k3_xboole_0(B_29, A_30), A_30))), inference(superposition, [status(thm), theory('equality')], [c_45, c_4])).
% 3.50/1.57  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.50/1.57  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.57  tff(c_30, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.50/1.57  tff(c_135, plain, (![B_47, A_48]: (r2_hidden(B_47, A_48) | ~m1_subset_1(B_47, A_48) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.50/1.57  tff(c_10, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.50/1.57  tff(c_142, plain, (![B_47, A_10]: (r1_tarski(B_47, A_10) | ~m1_subset_1(B_47, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_135, c_10])).
% 3.50/1.57  tff(c_147, plain, (![B_49, A_50]: (r1_tarski(B_49, A_50) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)))), inference(negUnitSimplification, [status(thm)], [c_30, c_142])).
% 3.50/1.57  tff(c_164, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_147])).
% 3.50/1.57  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.50/1.57  tff(c_172, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_164, c_8])).
% 3.50/1.57  tff(c_207, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2, c_172])).
% 3.50/1.57  tff(c_228, plain, (![A_51, B_52, C_53]: (r1_tarski(A_51, B_52) | ~r1_tarski(A_51, k3_xboole_0(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.50/1.57  tff(c_286, plain, (![A_54]: (r1_tarski(A_54, '#skF_3') | ~r1_tarski(A_54, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_207, c_228])).
% 3.50/1.57  tff(c_300, plain, (![B_29]: (r1_tarski(k3_xboole_0(B_29, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_60, c_286])).
% 3.50/1.57  tff(c_12, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.50/1.57  tff(c_123, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.50/1.57  tff(c_126, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(resolution, [status(thm)], [c_12, c_123])).
% 3.50/1.57  tff(c_129, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(negUnitSimplification, [status(thm)], [c_30, c_126])).
% 3.50/1.57  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.57  tff(c_1350, plain, (![A_111, C_112, B_113]: (r1_tarski(k3_subset_1(A_111, C_112), k3_subset_1(A_111, B_113)) | ~r1_tarski(B_113, C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(A_111)) | ~m1_subset_1(B_113, k1_zfmisc_1(A_111)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.50/1.57  tff(c_344, plain, (![A_57, B_58, C_59]: (k9_subset_1(A_57, B_58, C_59)=k3_xboole_0(B_58, C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.50/1.57  tff(c_357, plain, (![B_58]: (k9_subset_1('#skF_3', B_58, '#skF_5')=k3_xboole_0(B_58, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_344])).
% 3.50/1.57  tff(c_38, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.57  tff(c_416, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_357, c_38])).
% 3.50/1.57  tff(c_1356, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1350, c_416])).
% 3.50/1.57  tff(c_1363, plain, (~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4, c_1356])).
% 3.50/1.57  tff(c_1367, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_129, c_1363])).
% 3.50/1.57  tff(c_1374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_300, c_1367])).
% 3.50/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/1.57  
% 3.50/1.57  Inference rules
% 3.50/1.57  ----------------------
% 3.50/1.57  #Ref     : 0
% 3.50/1.57  #Sup     : 313
% 3.50/1.57  #Fact    : 0
% 3.50/1.57  #Define  : 0
% 3.50/1.57  #Split   : 0
% 3.50/1.57  #Chain   : 0
% 3.50/1.57  #Close   : 0
% 3.50/1.57  
% 3.50/1.57  Ordering : KBO
% 3.50/1.57  
% 3.50/1.57  Simplification rules
% 3.50/1.57  ----------------------
% 3.50/1.57  #Subsume      : 5
% 3.50/1.57  #Demod        : 200
% 3.50/1.57  #Tautology    : 216
% 3.50/1.57  #SimpNegUnit  : 2
% 3.50/1.57  #BackRed      : 1
% 3.50/1.57  
% 3.50/1.57  #Partial instantiations: 0
% 3.50/1.57  #Strategies tried      : 1
% 3.50/1.57  
% 3.50/1.57  Timing (in seconds)
% 3.50/1.57  ----------------------
% 3.50/1.57  Preprocessing        : 0.32
% 3.50/1.57  Parsing              : 0.16
% 3.50/1.57  CNF conversion       : 0.02
% 3.50/1.57  Main loop            : 0.47
% 3.50/1.57  Inferencing          : 0.16
% 3.50/1.57  Reduction            : 0.18
% 3.50/1.57  Demodulation         : 0.14
% 3.50/1.57  BG Simplification    : 0.02
% 3.50/1.57  Subsumption          : 0.07
% 3.50/1.57  Abstraction          : 0.02
% 3.50/1.57  MUC search           : 0.00
% 3.50/1.57  Cooper               : 0.00
% 3.50/1.57  Total                : 0.82
% 3.50/1.57  Index Insertion      : 0.00
% 3.50/1.57  Index Deletion       : 0.00
% 3.50/1.57  Index Matching       : 0.00
% 3.50/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
