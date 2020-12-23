%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:34 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   54 (  67 expanded)
%              Number of leaves         :   27 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 (  98 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

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

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

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

tff(c_107,plain,(
    ! [A_45,B_46] : k4_xboole_0(A_45,k4_xboole_0(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_116,plain,(
    ! [A_45,B_46] : r1_tarski(k3_xboole_0(A_45,B_46),A_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_6])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [A_17] : ~ v1_xboole_0(k1_zfmisc_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_74,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | ~ m1_subset_1(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_10,plain,(
    ! [C_14,A_10] :
      ( r1_tarski(C_14,A_10)
      | ~ r2_hidden(C_14,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_78,plain,(
    ! [B_39,A_10] :
      ( r1_tarski(B_39,A_10)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_74,c_10])).

tff(c_82,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_78])).

tff(c_94,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_82])).

tff(c_135,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(B_53,C_52)
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_146,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,'#skF_3')
      | ~ r1_tarski(A_51,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_94,c_135])).

tff(c_12,plain,(
    ! [C_14,A_10] :
      ( r2_hidden(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_96,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,(
    ! [C_14,A_10] :
      ( m1_subset_1(C_14,k1_zfmisc_1(A_10))
      | v1_xboole_0(k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_106,plain,(
    ! [C_14,A_10] :
      ( m1_subset_1(C_14,k1_zfmisc_1(A_10))
      | ~ r1_tarski(C_14,A_10) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_102])).

tff(c_1007,plain,(
    ! [A_166,C_167,B_168] :
      ( r1_tarski(k3_subset_1(A_166,C_167),k3_subset_1(A_166,B_168))
      | ~ r1_tarski(B_168,C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(A_166))
      | ~ m1_subset_1(B_168,k1_zfmisc_1(A_166)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_207,plain,(
    ! [A_64,B_65,C_66] :
      ( k9_subset_1(A_64,B_65,C_66) = k3_xboole_0(B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_220,plain,(
    ! [B_65] : k9_subset_1('#skF_3',B_65,'#skF_5') = k3_xboole_0(B_65,'#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_207])).

tff(c_38,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_230,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_38])).

tff(c_1015,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1007,c_230])).

tff(c_1022,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_116,c_1015])).

tff(c_1030,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_1022])).

tff(c_1037,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_1030])).

tff(c_1042,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_1037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.55  
% 2.97/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.97/1.55  
% 2.97/1.55  %Foreground sorts:
% 2.97/1.55  
% 2.97/1.55  
% 2.97/1.55  %Background operators:
% 2.97/1.55  
% 2.97/1.55  
% 2.97/1.55  %Foreground operators:
% 2.97/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.55  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.97/1.55  tff('#skF_5', type, '#skF_5': $i).
% 2.97/1.55  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.97/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.55  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.97/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.97/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.97/1.55  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.97/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.97/1.55  
% 2.97/1.56  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.97/1.56  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.97/1.56  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_subset_1)).
% 2.97/1.56  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.97/1.56  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.97/1.56  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.97/1.56  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.97/1.56  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.97/1.56  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.97/1.56  tff(c_107, plain, (![A_45, B_46]: (k4_xboole_0(A_45, k4_xboole_0(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.97/1.56  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.97/1.56  tff(c_116, plain, (![A_45, B_46]: (r1_tarski(k3_xboole_0(A_45, B_46), A_45))), inference(superposition, [status(thm), theory('equality')], [c_107, c_6])).
% 2.97/1.56  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.56  tff(c_30, plain, (![A_17]: (~v1_xboole_0(k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.97/1.56  tff(c_74, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | ~m1_subset_1(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.97/1.56  tff(c_10, plain, (![C_14, A_10]: (r1_tarski(C_14, A_10) | ~r2_hidden(C_14, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.97/1.56  tff(c_78, plain, (![B_39, A_10]: (r1_tarski(B_39, A_10) | ~m1_subset_1(B_39, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_74, c_10])).
% 2.97/1.56  tff(c_82, plain, (![B_41, A_42]: (r1_tarski(B_41, A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(negUnitSimplification, [status(thm)], [c_30, c_78])).
% 2.97/1.56  tff(c_94, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_82])).
% 2.97/1.56  tff(c_135, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(B_53, C_52) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.97/1.56  tff(c_146, plain, (![A_51]: (r1_tarski(A_51, '#skF_3') | ~r1_tarski(A_51, '#skF_4'))), inference(resolution, [status(thm)], [c_94, c_135])).
% 2.97/1.56  tff(c_12, plain, (![C_14, A_10]: (r2_hidden(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.97/1.56  tff(c_96, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.97/1.56  tff(c_102, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | v1_xboole_0(k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(resolution, [status(thm)], [c_12, c_96])).
% 2.97/1.56  tff(c_106, plain, (![C_14, A_10]: (m1_subset_1(C_14, k1_zfmisc_1(A_10)) | ~r1_tarski(C_14, A_10))), inference(negUnitSimplification, [status(thm)], [c_30, c_102])).
% 2.97/1.56  tff(c_1007, plain, (![A_166, C_167, B_168]: (r1_tarski(k3_subset_1(A_166, C_167), k3_subset_1(A_166, B_168)) | ~r1_tarski(B_168, C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(A_166)) | ~m1_subset_1(B_168, k1_zfmisc_1(A_166)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.97/1.56  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.56  tff(c_207, plain, (![A_64, B_65, C_66]: (k9_subset_1(A_64, B_65, C_66)=k3_xboole_0(B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.97/1.56  tff(c_220, plain, (![B_65]: (k9_subset_1('#skF_3', B_65, '#skF_5')=k3_xboole_0(B_65, '#skF_5'))), inference(resolution, [status(thm)], [c_40, c_207])).
% 2.97/1.56  tff(c_38, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.97/1.56  tff(c_230, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_220, c_38])).
% 2.97/1.56  tff(c_1015, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1007, c_230])).
% 2.97/1.56  tff(c_1022, plain, (~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_116, c_1015])).
% 2.97/1.56  tff(c_1030, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_106, c_1022])).
% 2.97/1.56  tff(c_1037, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_146, c_1030])).
% 2.97/1.56  tff(c_1042, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_1037])).
% 2.97/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.56  
% 2.97/1.56  Inference rules
% 2.97/1.56  ----------------------
% 2.97/1.56  #Ref     : 0
% 2.97/1.56  #Sup     : 220
% 2.97/1.56  #Fact    : 0
% 2.97/1.56  #Define  : 0
% 2.97/1.56  #Split   : 0
% 2.97/1.56  #Chain   : 0
% 2.97/1.56  #Close   : 0
% 2.97/1.56  
% 2.97/1.56  Ordering : KBO
% 2.97/1.56  
% 2.97/1.56  Simplification rules
% 2.97/1.56  ----------------------
% 2.97/1.56  #Subsume      : 12
% 2.97/1.56  #Demod        : 59
% 2.97/1.56  #Tautology    : 68
% 2.97/1.56  #SimpNegUnit  : 2
% 2.97/1.56  #BackRed      : 1
% 2.97/1.56  
% 2.97/1.56  #Partial instantiations: 0
% 2.97/1.56  #Strategies tried      : 1
% 2.97/1.56  
% 2.97/1.56  Timing (in seconds)
% 2.97/1.56  ----------------------
% 2.97/1.56  Preprocessing        : 0.34
% 2.97/1.56  Parsing              : 0.17
% 2.97/1.56  CNF conversion       : 0.02
% 2.97/1.56  Main loop            : 0.42
% 2.97/1.56  Inferencing          : 0.15
% 2.97/1.56  Reduction            : 0.13
% 2.97/1.56  Demodulation         : 0.10
% 2.97/1.56  BG Simplification    : 0.02
% 2.97/1.56  Subsumption          : 0.08
% 2.97/1.56  Abstraction          : 0.02
% 2.97/1.56  MUC search           : 0.00
% 2.97/1.56  Cooper               : 0.00
% 2.97/1.56  Total                : 0.79
% 2.97/1.56  Index Insertion      : 0.00
% 2.97/1.56  Index Deletion       : 0.00
% 2.97/1.57  Index Matching       : 0.00
% 2.97/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
