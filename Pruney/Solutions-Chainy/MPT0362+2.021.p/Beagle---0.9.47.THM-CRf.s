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
% DateTime   : Thu Dec  3 09:56:35 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 7.85s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  77 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => m1_subset_1(k9_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_70,plain,(
    ! [D_36,A_37,B_38] :
      ( r2_hidden(D_36,A_37)
      | ~ r2_hidden(D_36,k3_xboole_0(A_37,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_920,plain,(
    ! [A_107,B_108,B_109] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_107,B_108),B_109),A_107)
      | r1_tarski(k3_xboole_0(A_107,B_108),B_109) ) ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_953,plain,(
    ! [A_107,B_108] : r1_tarski(k3_xboole_0(A_107,B_108),A_107) ),
    inference(resolution,[status(thm)],[c_920,c_4])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_344,plain,(
    ! [A_56,B_57,C_58] :
      ( k9_subset_1(A_56,B_57,C_58) = k3_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_349,plain,(
    ! [B_57] : k9_subset_1('#skF_4',B_57,'#skF_6') = k3_xboole_0(B_57,'#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_344])).

tff(c_370,plain,(
    ! [A_61,B_62,C_63] :
      ( m1_subset_1(k9_subset_1(A_61,B_62,C_63),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(C_63,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_381,plain,(
    ! [B_57] :
      ( m1_subset_1(k3_xboole_0(B_57,'#skF_6'),k1_zfmisc_1('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_370])).

tff(c_396,plain,(
    ! [B_65] : m1_subset_1(k3_xboole_0(B_65,'#skF_6'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_381])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_475,plain,(
    ! [B_68] : k4_xboole_0('#skF_4',k3_xboole_0(B_68,'#skF_6')) = k3_subset_1('#skF_4',k3_xboole_0(B_68,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_396,c_30])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_80,plain,(
    ! [A_42,B_43] :
      ( k4_xboole_0(A_42,B_43) = k3_subset_1(A_42,B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_88,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_117,plain,(
    ! [C_44,B_45,A_46] :
      ( r1_tarski(k4_xboole_0(C_44,B_45),k4_xboole_0(C_44,A_46))
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_132,plain,(
    ! [A_46] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),k4_xboole_0('#skF_4',A_46))
      | ~ r1_tarski(A_46,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_117])).

tff(c_7887,plain,(
    ! [B_339] :
      ( r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k3_xboole_0(B_339,'#skF_6')))
      | ~ r1_tarski(k3_xboole_0(B_339,'#skF_6'),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_475,c_132])).

tff(c_36,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k9_subset_1('#skF_4','#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_351,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_5'),k3_subset_1('#skF_4',k3_xboole_0('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_36])).

tff(c_7892,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_5','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_7887,c_351])).

tff(c_7901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_953,c_7892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:42 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.71  
% 7.85/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.72  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 7.85/2.72  
% 7.85/2.72  %Foreground sorts:
% 7.85/2.72  
% 7.85/2.72  
% 7.85/2.72  %Background operators:
% 7.85/2.72  
% 7.85/2.72  
% 7.85/2.72  %Foreground operators:
% 7.85/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.85/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.85/2.72  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.85/2.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.85/2.72  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.85/2.72  tff('#skF_5', type, '#skF_5': $i).
% 7.85/2.72  tff('#skF_6', type, '#skF_6': $i).
% 7.85/2.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.85/2.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.85/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.85/2.72  tff('#skF_4', type, '#skF_4': $i).
% 7.85/2.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.85/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.85/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.85/2.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.85/2.72  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 7.85/2.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.85/2.72  
% 7.85/2.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.85/2.73  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 7.85/2.73  tff(f_67, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 7.85/2.73  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 7.85/2.73  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => m1_subset_1(k9_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k9_subset_1)).
% 7.85/2.73  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.85/2.73  tff(f_45, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 7.85/2.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.85/2.73  tff(c_70, plain, (![D_36, A_37, B_38]: (r2_hidden(D_36, A_37) | ~r2_hidden(D_36, k3_xboole_0(A_37, B_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.85/2.73  tff(c_920, plain, (![A_107, B_108, B_109]: (r2_hidden('#skF_1'(k3_xboole_0(A_107, B_108), B_109), A_107) | r1_tarski(k3_xboole_0(A_107, B_108), B_109))), inference(resolution, [status(thm)], [c_6, c_70])).
% 7.85/2.73  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.85/2.73  tff(c_953, plain, (![A_107, B_108]: (r1_tarski(k3_xboole_0(A_107, B_108), A_107))), inference(resolution, [status(thm)], [c_920, c_4])).
% 7.85/2.73  tff(c_38, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.85/2.73  tff(c_344, plain, (![A_56, B_57, C_58]: (k9_subset_1(A_56, B_57, C_58)=k3_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.85/2.73  tff(c_349, plain, (![B_57]: (k9_subset_1('#skF_4', B_57, '#skF_6')=k3_xboole_0(B_57, '#skF_6'))), inference(resolution, [status(thm)], [c_38, c_344])).
% 7.85/2.73  tff(c_370, plain, (![A_61, B_62, C_63]: (m1_subset_1(k9_subset_1(A_61, B_62, C_63), k1_zfmisc_1(A_61)) | ~m1_subset_1(C_63, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.85/2.73  tff(c_381, plain, (![B_57]: (m1_subset_1(k3_xboole_0(B_57, '#skF_6'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_349, c_370])).
% 7.85/2.73  tff(c_396, plain, (![B_65]: (m1_subset_1(k3_xboole_0(B_65, '#skF_6'), k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_381])).
% 7.85/2.73  tff(c_30, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.85/2.73  tff(c_475, plain, (![B_68]: (k4_xboole_0('#skF_4', k3_xboole_0(B_68, '#skF_6'))=k3_subset_1('#skF_4', k3_xboole_0(B_68, '#skF_6')))), inference(resolution, [status(thm)], [c_396, c_30])).
% 7.85/2.73  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.85/2.73  tff(c_80, plain, (![A_42, B_43]: (k4_xboole_0(A_42, B_43)=k3_subset_1(A_42, B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.85/2.73  tff(c_88, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_80])).
% 7.85/2.73  tff(c_117, plain, (![C_44, B_45, A_46]: (r1_tarski(k4_xboole_0(C_44, B_45), k4_xboole_0(C_44, A_46)) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.85/2.73  tff(c_132, plain, (![A_46]: (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k4_xboole_0('#skF_4', A_46)) | ~r1_tarski(A_46, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_88, c_117])).
% 7.85/2.73  tff(c_7887, plain, (![B_339]: (r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k3_xboole_0(B_339, '#skF_6'))) | ~r1_tarski(k3_xboole_0(B_339, '#skF_6'), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_475, c_132])).
% 7.85/2.73  tff(c_36, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k9_subset_1('#skF_4', '#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.85/2.73  tff(c_351, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_5'), k3_subset_1('#skF_4', k3_xboole_0('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_349, c_36])).
% 7.85/2.73  tff(c_7892, plain, (~r1_tarski(k3_xboole_0('#skF_5', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_7887, c_351])).
% 7.85/2.73  tff(c_7901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_953, c_7892])).
% 7.85/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.85/2.73  
% 7.85/2.73  Inference rules
% 7.85/2.73  ----------------------
% 7.85/2.73  #Ref     : 0
% 7.85/2.73  #Sup     : 1937
% 7.85/2.73  #Fact    : 0
% 7.85/2.73  #Define  : 0
% 7.85/2.73  #Split   : 26
% 7.85/2.73  #Chain   : 0
% 7.85/2.73  #Close   : 0
% 7.85/2.73  
% 7.85/2.73  Ordering : KBO
% 7.85/2.73  
% 7.85/2.73  Simplification rules
% 7.85/2.73  ----------------------
% 7.85/2.73  #Subsume      : 224
% 7.85/2.73  #Demod        : 814
% 7.85/2.73  #Tautology    : 232
% 7.85/2.73  #SimpNegUnit  : 4
% 7.85/2.73  #BackRed      : 5
% 7.85/2.73  
% 7.85/2.73  #Partial instantiations: 0
% 7.85/2.73  #Strategies tried      : 1
% 7.85/2.73  
% 7.85/2.73  Timing (in seconds)
% 7.85/2.73  ----------------------
% 7.85/2.73  Preprocessing        : 0.30
% 7.85/2.73  Parsing              : 0.15
% 7.85/2.73  CNF conversion       : 0.02
% 7.85/2.73  Main loop            : 1.67
% 7.85/2.73  Inferencing          : 0.47
% 7.85/2.73  Reduction            : 0.57
% 7.85/2.73  Demodulation         : 0.42
% 7.85/2.73  BG Simplification    : 0.06
% 7.85/2.73  Subsumption          : 0.46
% 7.85/2.73  Abstraction          : 0.07
% 7.85/2.73  MUC search           : 0.00
% 7.85/2.73  Cooper               : 0.00
% 7.85/2.73  Total                : 1.99
% 7.85/2.73  Index Insertion      : 0.00
% 7.85/2.73  Index Deletion       : 0.00
% 7.85/2.73  Index Matching       : 0.00
% 7.85/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
