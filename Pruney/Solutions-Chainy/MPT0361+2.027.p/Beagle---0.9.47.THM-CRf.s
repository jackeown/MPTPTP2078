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
% DateTime   : Thu Dec  3 09:56:30 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   59 (  94 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k3_enumset1 > k4_subset_1 > k1_enumset1 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_42,axiom,(
    ! [A,B,C] : k3_enumset1(A,A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k3_enumset1(A,A,A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_52,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_154,plain,(
    ! [A_74,B_75,C_76] :
      ( k4_subset_1(A_74,B_75,C_76) = k2_xboole_0(B_75,C_76)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_164,plain,(
    ! [B_77] :
      ( k4_subset_1('#skF_3',B_77,'#skF_5') = k2_xboole_0(B_77,'#skF_5')
      | ~ m1_subset_1(B_77,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_46,c_154])).

tff(c_177,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_164])).

tff(c_36,plain,(
    ! [A_22,B_23,C_24] :
      ( m1_subset_1(k4_subset_1(A_22,B_23,C_24),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_207,plain,
    ( m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_36])).

tff(c_211,plain,(
    m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_207])).

tff(c_74,plain,(
    ! [A_48,B_49,C_50] : k3_enumset1(A_48,A_48,A_48,B_49,C_50) = k1_enumset1(A_48,B_49,C_50) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    ! [A_11,B_12] : k3_enumset1(A_11,A_11,A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_90,plain,(
    ! [B_51,C_52] : k1_enumset1(B_51,B_51,C_52) = k2_tarski(B_51,C_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_28])).

tff(c_6,plain,(
    ! [E_7,A_1,C_3] : r2_hidden(E_7,k1_enumset1(A_1,E_7,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_99,plain,(
    ! [B_51,C_52] : r2_hidden(B_51,k2_tarski(B_51,C_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_6])).

tff(c_34,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_61,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,k3_tarski(B_45))
      | ~ r2_hidden(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_131,plain,(
    ! [A_61,A_62,B_63] :
      ( r1_tarski(A_61,k2_xboole_0(A_62,B_63))
      | ~ r2_hidden(A_61,k2_tarski(A_62,B_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_61])).

tff(c_138,plain,(
    ! [B_51,C_52] : r1_tarski(B_51,k2_xboole_0(B_51,C_52)) ),
    inference(resolution,[status(thm)],[c_99,c_131])).

tff(c_291,plain,(
    ! [A_84,C_85,B_86] :
      ( r1_tarski(k3_subset_1(A_84,C_85),k3_subset_1(A_84,B_86))
      | ~ r1_tarski(B_86,C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k4_subset_1('#skF_3','#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_203,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_44])).

tff(c_294,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_5'))
    | ~ m1_subset_1(k2_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_291,c_203])).

tff(c_298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_211,c_138,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.28  
% 2.25/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.28  %$ r2_hidden > r1_tarski > m1_subset_1 > k6_enumset1 > k3_enumset1 > k4_subset_1 > k1_enumset1 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.25/1.28  
% 2.25/1.28  %Foreground sorts:
% 2.25/1.28  
% 2.25/1.28  
% 2.25/1.28  %Background operators:
% 2.25/1.28  
% 2.25/1.28  
% 2.25/1.28  %Foreground operators:
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.25/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.28  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.25/1.28  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.25/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.25/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.25/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.25/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.25/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.25/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.28  
% 2.25/1.29  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 2.25/1.29  tff(f_64, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.25/1.29  tff(f_58, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.25/1.29  tff(f_42, axiom, (![A, B, C]: (k3_enumset1(A, A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_enumset1)).
% 2.25/1.29  tff(f_44, axiom, (![A, B]: (k3_enumset1(A, A, A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_enumset1)).
% 2.25/1.29  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.25/1.29  tff(f_52, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.25/1.29  tff(f_50, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.25/1.29  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.25/1.29  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.29  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.29  tff(c_154, plain, (![A_74, B_75, C_76]: (k4_subset_1(A_74, B_75, C_76)=k2_xboole_0(B_75, C_76) | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.25/1.29  tff(c_164, plain, (![B_77]: (k4_subset_1('#skF_3', B_77, '#skF_5')=k2_xboole_0(B_77, '#skF_5') | ~m1_subset_1(B_77, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_46, c_154])).
% 2.25/1.29  tff(c_177, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_164])).
% 2.25/1.29  tff(c_36, plain, (![A_22, B_23, C_24]: (m1_subset_1(k4_subset_1(A_22, B_23, C_24), k1_zfmisc_1(A_22)) | ~m1_subset_1(C_24, k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.25/1.29  tff(c_207, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_177, c_36])).
% 2.25/1.29  tff(c_211, plain, (m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_207])).
% 2.25/1.29  tff(c_74, plain, (![A_48, B_49, C_50]: (k3_enumset1(A_48, A_48, A_48, B_49, C_50)=k1_enumset1(A_48, B_49, C_50))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.25/1.29  tff(c_28, plain, (![A_11, B_12]: (k3_enumset1(A_11, A_11, A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.25/1.29  tff(c_90, plain, (![B_51, C_52]: (k1_enumset1(B_51, B_51, C_52)=k2_tarski(B_51, C_52))), inference(superposition, [status(thm), theory('equality')], [c_74, c_28])).
% 2.25/1.29  tff(c_6, plain, (![E_7, A_1, C_3]: (r2_hidden(E_7, k1_enumset1(A_1, E_7, C_3)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.29  tff(c_99, plain, (![B_51, C_52]: (r2_hidden(B_51, k2_tarski(B_51, C_52)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_6])).
% 2.25/1.29  tff(c_34, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.25/1.29  tff(c_61, plain, (![A_44, B_45]: (r1_tarski(A_44, k3_tarski(B_45)) | ~r2_hidden(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.25/1.29  tff(c_131, plain, (![A_61, A_62, B_63]: (r1_tarski(A_61, k2_xboole_0(A_62, B_63)) | ~r2_hidden(A_61, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_61])).
% 2.25/1.29  tff(c_138, plain, (![B_51, C_52]: (r1_tarski(B_51, k2_xboole_0(B_51, C_52)))), inference(resolution, [status(thm)], [c_99, c_131])).
% 2.25/1.29  tff(c_291, plain, (![A_84, C_85, B_86]: (r1_tarski(k3_subset_1(A_84, C_85), k3_subset_1(A_84, B_86)) | ~r1_tarski(B_86, C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.25/1.29  tff(c_44, plain, (~r1_tarski(k3_subset_1('#skF_3', k4_subset_1('#skF_3', '#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.29  tff(c_203, plain, (~r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_44])).
% 2.25/1.29  tff(c_294, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_5')) | ~m1_subset_1(k2_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_291, c_203])).
% 2.25/1.29  tff(c_298, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_211, c_138, c_294])).
% 2.25/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.29  
% 2.25/1.29  Inference rules
% 2.25/1.29  ----------------------
% 2.25/1.29  #Ref     : 0
% 2.25/1.29  #Sup     : 61
% 2.25/1.29  #Fact    : 0
% 2.25/1.29  #Define  : 0
% 2.25/1.29  #Split   : 0
% 2.25/1.29  #Chain   : 0
% 2.25/1.29  #Close   : 0
% 2.25/1.29  
% 2.25/1.29  Ordering : KBO
% 2.25/1.29  
% 2.25/1.29  Simplification rules
% 2.25/1.29  ----------------------
% 2.25/1.29  #Subsume      : 0
% 2.25/1.29  #Demod        : 16
% 2.25/1.29  #Tautology    : 27
% 2.25/1.29  #SimpNegUnit  : 0
% 2.25/1.29  #BackRed      : 1
% 2.25/1.29  
% 2.25/1.29  #Partial instantiations: 0
% 2.25/1.29  #Strategies tried      : 1
% 2.25/1.29  
% 2.25/1.29  Timing (in seconds)
% 2.25/1.29  ----------------------
% 2.25/1.29  Preprocessing        : 0.32
% 2.25/1.29  Parsing              : 0.17
% 2.25/1.29  CNF conversion       : 0.02
% 2.25/1.29  Main loop            : 0.19
% 2.25/1.29  Inferencing          : 0.07
% 2.25/1.29  Reduction            : 0.06
% 2.25/1.29  Demodulation         : 0.05
% 2.25/1.29  BG Simplification    : 0.02
% 2.25/1.29  Subsumption          : 0.04
% 2.25/1.29  Abstraction          : 0.02
% 2.25/1.29  MUC search           : 0.00
% 2.25/1.29  Cooper               : 0.00
% 2.25/1.29  Total                : 0.54
% 2.25/1.29  Index Insertion      : 0.00
% 2.25/1.29  Index Deletion       : 0.00
% 2.25/1.29  Index Matching       : 0.00
% 2.25/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
