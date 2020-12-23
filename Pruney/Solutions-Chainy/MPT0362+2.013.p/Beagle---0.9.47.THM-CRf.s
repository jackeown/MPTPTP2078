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
% DateTime   : Thu Dec  3 09:56:34 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   54 (  64 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 (  95 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_32,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_112,plain,(
    ! [B_48,A_49] :
      ( r2_hidden(B_48,A_49)
      | ~ m1_subset_1(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_116,plain,(
    ! [B_48,A_12] :
      ( r1_tarski(B_48,A_12)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_112,c_12])).

tff(c_124,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_116])).

tff(c_136,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_124])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_53,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_10,c_53])).

tff(c_190,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(A_57,C_58)
      | ~ r1_tarski(k2_xboole_0(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_202,plain,(
    ! [A_10,B_11,C_58] :
      ( r1_tarski(k3_xboole_0(A_10,B_11),C_58)
      | ~ r1_tarski(A_10,C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_190])).

tff(c_14,plain,(
    ! [C_16,A_12] :
      ( r2_hidden(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_154,plain,(
    ! [B_52,A_53] :
      ( m1_subset_1(B_52,A_53)
      | ~ r2_hidden(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_160,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_154])).

tff(c_167,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_160])).

tff(c_738,plain,(
    ! [A_148,C_149,B_150] :
      ( r1_tarski(k3_subset_1(A_148,C_149),k3_subset_1(A_148,B_150))
      | ~ r1_tarski(B_150,C_149)
      | ~ m1_subset_1(C_149,k1_zfmisc_1(A_148))
      | ~ m1_subset_1(B_150,k1_zfmisc_1(A_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_203,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_222,plain,(
    ! [B_61] : k9_subset_1('#skF_4',B_61,'#skF_6') = k3_xboole_0(B_61,'#skF_6') ),
    inference(resolution,[status(thm)],[c_42,c_203])).

tff(c_40,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k9_subset_1('#skF_4','#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_242,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k3_xboole_0('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_40])).

tff(c_745,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_5')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_738,c_242])).

tff(c_753,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_5','#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_10,c_745])).

tff(c_761,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_167,c_753])).

tff(c_771,plain,(
    ~ r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_202,c_761])).

tff(c_777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_771])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:35:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.48  
% 2.63/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.48  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.63/1.48  
% 2.63/1.48  %Foreground sorts:
% 2.63/1.48  
% 2.63/1.48  
% 2.63/1.48  %Background operators:
% 2.63/1.48  
% 2.63/1.48  
% 2.63/1.48  %Foreground operators:
% 2.63/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.63/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.63/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.48  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.63/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.63/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.63/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.63/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.48  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.63/1.48  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.63/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.63/1.48  
% 2.81/1.49  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 2.81/1.49  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.81/1.49  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.81/1.49  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.81/1.49  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.81/1.49  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.81/1.49  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.81/1.49  tff(f_77, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.81/1.49  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.81/1.49  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.49  tff(c_32, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.81/1.49  tff(c_112, plain, (![B_48, A_49]: (r2_hidden(B_48, A_49) | ~m1_subset_1(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.49  tff(c_12, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.49  tff(c_116, plain, (![B_48, A_12]: (r1_tarski(B_48, A_12) | ~m1_subset_1(B_48, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_112, c_12])).
% 2.81/1.49  tff(c_124, plain, (![B_50, A_51]: (r1_tarski(B_50, A_51) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)))), inference(negUnitSimplification, [status(thm)], [c_32, c_116])).
% 2.81/1.49  tff(c_136, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_124])).
% 2.81/1.49  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.81/1.49  tff(c_53, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.81/1.49  tff(c_57, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_10, c_53])).
% 2.81/1.49  tff(c_190, plain, (![A_57, C_58, B_59]: (r1_tarski(A_57, C_58) | ~r1_tarski(k2_xboole_0(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.81/1.49  tff(c_202, plain, (![A_10, B_11, C_58]: (r1_tarski(k3_xboole_0(A_10, B_11), C_58) | ~r1_tarski(A_10, C_58))), inference(superposition, [status(thm), theory('equality')], [c_57, c_190])).
% 2.81/1.49  tff(c_14, plain, (![C_16, A_12]: (r2_hidden(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.81/1.49  tff(c_154, plain, (![B_52, A_53]: (m1_subset_1(B_52, A_53) | ~r2_hidden(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.81/1.49  tff(c_160, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(resolution, [status(thm)], [c_14, c_154])).
% 2.81/1.49  tff(c_167, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(negUnitSimplification, [status(thm)], [c_32, c_160])).
% 2.81/1.49  tff(c_738, plain, (![A_148, C_149, B_150]: (r1_tarski(k3_subset_1(A_148, C_149), k3_subset_1(A_148, B_150)) | ~r1_tarski(B_150, C_149) | ~m1_subset_1(C_149, k1_zfmisc_1(A_148)) | ~m1_subset_1(B_150, k1_zfmisc_1(A_148)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.81/1.49  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.49  tff(c_203, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.81/1.49  tff(c_222, plain, (![B_61]: (k9_subset_1('#skF_4', B_61, '#skF_6')=k3_xboole_0(B_61, '#skF_6'))), inference(resolution, [status(thm)], [c_42, c_203])).
% 2.81/1.49  tff(c_40, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k9_subset_1('#skF_4', '#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.81/1.49  tff(c_242, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k3_xboole_0('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_222, c_40])).
% 2.81/1.49  tff(c_745, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_5') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_738, c_242])).
% 2.81/1.49  tff(c_753, plain, (~m1_subset_1(k3_xboole_0('#skF_5', '#skF_6'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_10, c_745])).
% 2.81/1.49  tff(c_761, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_4')), inference(resolution, [status(thm)], [c_167, c_753])).
% 2.81/1.49  tff(c_771, plain, (~r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_202, c_761])).
% 2.81/1.49  tff(c_777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_136, c_771])).
% 2.81/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.49  
% 2.81/1.49  Inference rules
% 2.81/1.49  ----------------------
% 2.81/1.49  #Ref     : 0
% 2.81/1.49  #Sup     : 174
% 2.81/1.49  #Fact    : 0
% 2.81/1.49  #Define  : 0
% 2.81/1.49  #Split   : 0
% 2.81/1.49  #Chain   : 0
% 2.81/1.49  #Close   : 0
% 2.81/1.49  
% 2.81/1.49  Ordering : KBO
% 2.81/1.49  
% 2.81/1.49  Simplification rules
% 2.81/1.49  ----------------------
% 2.81/1.49  #Subsume      : 8
% 2.81/1.49  #Demod        : 8
% 2.81/1.49  #Tautology    : 51
% 2.81/1.49  #SimpNegUnit  : 5
% 2.81/1.49  #BackRed      : 1
% 2.81/1.49  
% 2.81/1.49  #Partial instantiations: 0
% 2.81/1.49  #Strategies tried      : 1
% 2.81/1.49  
% 2.81/1.49  Timing (in seconds)
% 2.81/1.49  ----------------------
% 2.81/1.50  Preprocessing        : 0.29
% 2.81/1.50  Parsing              : 0.15
% 2.81/1.50  CNF conversion       : 0.02
% 2.81/1.50  Main loop            : 0.34
% 2.81/1.50  Inferencing          : 0.14
% 2.81/1.50  Reduction            : 0.09
% 2.81/1.50  Demodulation         : 0.06
% 2.81/1.50  BG Simplification    : 0.02
% 2.81/1.50  Subsumption          : 0.06
% 2.81/1.50  Abstraction          : 0.02
% 2.81/1.50  MUC search           : 0.00
% 2.81/1.50  Cooper               : 0.00
% 2.81/1.50  Total                : 0.66
% 2.81/1.50  Index Insertion      : 0.00
% 2.81/1.50  Index Deletion       : 0.00
% 2.81/1.50  Index Matching       : 0.00
% 2.81/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
