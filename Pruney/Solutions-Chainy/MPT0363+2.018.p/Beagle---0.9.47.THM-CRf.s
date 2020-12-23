%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:38 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   51 (  64 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   68 ( 106 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_63,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_43,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_22,plain,(
    ! [A_14] : ~ v1_xboole_0(k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_147,plain,(
    ! [B_44,A_45] :
      ( r2_hidden(B_44,A_45)
      | ~ m1_subset_1(B_44,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_9] : k3_tarski(k1_zfmisc_1(A_9)) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_59,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,k3_tarski(B_23))
      | ~ r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_62,plain,(
    ! [A_22,A_9] :
      ( r1_tarski(A_22,A_9)
      | ~ r2_hidden(A_22,k1_zfmisc_1(A_9)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_59])).

tff(c_151,plain,(
    ! [B_44,A_9] :
      ( r1_tarski(B_44,A_9)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_147,c_62])).

tff(c_155,plain,(
    ! [B_46,A_47] :
      ( r1_tarski(B_46,A_47)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_151])).

tff(c_168,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_155])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_65,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_89,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_34])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_95,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,B_39) = k3_subset_1(A_38,B_39)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_107,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [A_43] :
      ( r1_xboole_0(A_43,'#skF_3')
      | ~ r1_tarski(A_43,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_2])).

tff(c_140,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_89,c_137])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_140])).

tff(c_146,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_177,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_189,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_tarski(A_4,k4_xboole_0(B_5,C_6))
      | ~ r1_xboole_0(A_4,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_230,plain,(
    ! [A_62] :
      ( r1_tarski(A_62,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_62,'#skF_3')
      | ~ r1_tarski(A_62,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_6])).

tff(c_145,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_239,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_230,c_145])).

tff(c_245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_146,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:42:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.23  
% 2.05/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.10/1.24  
% 2.10/1.24  %Foreground sorts:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Background operators:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Foreground operators:
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.24  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.10/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.10/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.24  
% 2.10/1.25  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_subset_1)).
% 2.10/1.25  tff(f_63, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.10/1.25  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.10/1.25  tff(f_43, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.10/1.25  tff(f_41, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.10/1.25  tff(f_60, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.10/1.25  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.10/1.25  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 2.10/1.25  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.10/1.25  tff(c_22, plain, (![A_14]: (~v1_xboole_0(k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.10/1.25  tff(c_147, plain, (![B_44, A_45]: (r2_hidden(B_44, A_45) | ~m1_subset_1(B_44, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.10/1.25  tff(c_10, plain, (![A_9]: (k3_tarski(k1_zfmisc_1(A_9))=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.25  tff(c_59, plain, (![A_22, B_23]: (r1_tarski(A_22, k3_tarski(B_23)) | ~r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.10/1.25  tff(c_62, plain, (![A_22, A_9]: (r1_tarski(A_22, A_9) | ~r2_hidden(A_22, k1_zfmisc_1(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_59])).
% 2.10/1.25  tff(c_151, plain, (![B_44, A_9]: (r1_tarski(B_44, A_9) | ~m1_subset_1(B_44, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_147, c_62])).
% 2.10/1.25  tff(c_155, plain, (![B_46, A_47]: (r1_tarski(B_46, A_47) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)))), inference(negUnitSimplification, [status(thm)], [c_22, c_151])).
% 2.10/1.25  tff(c_168, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_26, c_155])).
% 2.10/1.25  tff(c_28, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.10/1.25  tff(c_65, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_28])).
% 2.10/1.25  tff(c_34, plain, (r1_xboole_0('#skF_2', '#skF_3') | r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.10/1.25  tff(c_89, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_65, c_34])).
% 2.10/1.25  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.10/1.25  tff(c_95, plain, (![A_38, B_39]: (k4_xboole_0(A_38, B_39)=k3_subset_1(A_38, B_39) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.25  tff(c_107, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_95])).
% 2.10/1.25  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.25  tff(c_137, plain, (![A_43]: (r1_xboole_0(A_43, '#skF_3') | ~r1_tarski(A_43, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_107, c_2])).
% 2.10/1.25  tff(c_140, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_89, c_137])).
% 2.10/1.25  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_140])).
% 2.10/1.25  tff(c_146, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_28])).
% 2.10/1.25  tff(c_177, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.25  tff(c_189, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_177])).
% 2.10/1.25  tff(c_6, plain, (![A_4, B_5, C_6]: (r1_tarski(A_4, k4_xboole_0(B_5, C_6)) | ~r1_xboole_0(A_4, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.25  tff(c_230, plain, (![A_62]: (r1_tarski(A_62, k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_62, '#skF_3') | ~r1_tarski(A_62, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_189, c_6])).
% 2.10/1.25  tff(c_145, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_28])).
% 2.10/1.25  tff(c_239, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_230, c_145])).
% 2.10/1.25  tff(c_245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_146, c_239])).
% 2.10/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  
% 2.10/1.25  Inference rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Ref     : 0
% 2.10/1.25  #Sup     : 47
% 2.10/1.25  #Fact    : 0
% 2.10/1.25  #Define  : 0
% 2.10/1.25  #Split   : 1
% 2.10/1.25  #Chain   : 0
% 2.10/1.25  #Close   : 0
% 2.10/1.25  
% 2.10/1.25  Ordering : KBO
% 2.10/1.25  
% 2.10/1.25  Simplification rules
% 2.10/1.25  ----------------------
% 2.10/1.25  #Subsume      : 6
% 2.10/1.25  #Demod        : 4
% 2.10/1.25  #Tautology    : 21
% 2.10/1.25  #SimpNegUnit  : 5
% 2.10/1.25  #BackRed      : 0
% 2.10/1.25  
% 2.10/1.25  #Partial instantiations: 0
% 2.10/1.25  #Strategies tried      : 1
% 2.10/1.25  
% 2.10/1.25  Timing (in seconds)
% 2.10/1.25  ----------------------
% 2.10/1.25  Preprocessing        : 0.30
% 2.10/1.25  Parsing              : 0.16
% 2.10/1.25  CNF conversion       : 0.02
% 2.10/1.25  Main loop            : 0.18
% 2.10/1.25  Inferencing          : 0.08
% 2.10/1.25  Reduction            : 0.05
% 2.10/1.25  Demodulation         : 0.03
% 2.10/1.25  BG Simplification    : 0.01
% 2.10/1.25  Subsumption          : 0.03
% 2.10/1.25  Abstraction          : 0.01
% 2.10/1.25  MUC search           : 0.00
% 2.10/1.25  Cooper               : 0.00
% 2.10/1.25  Total                : 0.51
% 2.10/1.25  Index Insertion      : 0.00
% 2.10/1.25  Index Deletion       : 0.00
% 2.10/1.25  Index Matching       : 0.00
% 2.10/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
