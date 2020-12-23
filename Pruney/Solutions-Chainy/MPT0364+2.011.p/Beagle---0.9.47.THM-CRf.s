%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:40 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   63 (  85 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 ( 146 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,k3_subset_1(A,C))
            <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_61,axiom,(
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

tff(f_68,axiom,(
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
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(A,C) )
     => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(c_46,plain,
    ( r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5'))
    | r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_69,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_36,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_241,plain,(
    ! [A_59,B_60] :
      ( k3_subset_1(A_59,k3_subset_1(A_59,B_60)) = B_60
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_257,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_241])).

tff(c_155,plain,(
    ! [A_50,B_51] :
      ( m1_subset_1(k3_subset_1(A_50,B_51),k1_zfmisc_1(A_50))
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_28,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(A_14,B_15) = k3_subset_1(A_14,B_15)
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_501,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,k3_subset_1(A_78,B_79)) = k3_subset_1(A_78,k3_subset_1(A_78,B_79))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_155,c_28])).

tff(c_512,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_501])).

tff(c_519,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_512])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_569,plain,(
    ! [A_82] :
      ( r1_xboole_0(A_82,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_82,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_519,c_2])).

tff(c_40,plain,
    ( ~ r1_tarski('#skF_4','#skF_5')
    | ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_70,plain,(
    ~ r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_572,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_569,c_70])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_572])).

tff(c_577,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_577])).

tff(c_582,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_38,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_32,plain,(
    ! [A_18] : ~ v1_xboole_0(k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_585,plain,(
    ! [B_83,A_84] :
      ( r2_hidden(B_83,A_84)
      | ~ m1_subset_1(B_83,A_84)
      | v1_xboole_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_589,plain,(
    ! [B_83,A_7] :
      ( r1_tarski(B_83,A_7)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_585,c_8])).

tff(c_593,plain,(
    ! [B_85,A_86] :
      ( r1_tarski(B_85,A_86)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_86)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_589])).

tff(c_605,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_593])).

tff(c_581,plain,(
    r1_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_656,plain,(
    ! [A_96,B_97] :
      ( k3_subset_1(A_96,k3_subset_1(A_96,B_97)) = B_97
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_669,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_656])).

tff(c_752,plain,(
    ! [A_106,B_107] :
      ( m1_subset_1(k3_subset_1(A_106,B_107),k1_zfmisc_1(A_106))
      | ~ m1_subset_1(B_107,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_958,plain,(
    ! [A_124,B_125] :
      ( k4_xboole_0(A_124,k3_subset_1(A_124,B_125)) = k3_subset_1(A_124,k3_subset_1(A_124,B_125))
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_124)) ) ),
    inference(resolution,[status(thm)],[c_752,c_28])).

tff(c_969,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_36,c_958])).

tff(c_976,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_969])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] :
      ( r1_tarski(A_4,k4_xboole_0(B_5,C_6))
      | ~ r1_xboole_0(A_4,C_6)
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1125,plain,(
    ! [A_135] :
      ( r1_tarski(A_135,'#skF_5')
      | ~ r1_xboole_0(A_135,k3_subset_1('#skF_3','#skF_5'))
      | ~ r1_tarski(A_135,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_6])).

tff(c_1131,plain,
    ( r1_tarski('#skF_4','#skF_5')
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_581,c_1125])).

tff(c_1135,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_605,c_1131])).

tff(c_1137,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_582,c_1135])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:03:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.31/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.73  
% 3.31/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.73  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.31/1.73  
% 3.31/1.73  %Foreground sorts:
% 3.31/1.73  
% 3.31/1.73  
% 3.31/1.73  %Background operators:
% 3.31/1.73  
% 3.31/1.73  
% 3.31/1.73  %Foreground operators:
% 3.31/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.73  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.31/1.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.31/1.73  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.31/1.73  tff('#skF_5', type, '#skF_5': $i).
% 3.31/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.31/1.73  tff('#skF_3', type, '#skF_3': $i).
% 3.31/1.73  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.73  tff('#skF_4', type, '#skF_4': $i).
% 3.31/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.73  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.31/1.73  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.31/1.73  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.73  
% 3.31/1.74  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_subset_1)).
% 3.31/1.74  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.31/1.74  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.31/1.74  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.31/1.74  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 3.31/1.74  tff(f_68, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.31/1.74  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.31/1.74  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.31/1.74  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 3.31/1.74  tff(c_46, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5')) | r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.31/1.74  tff(c_69, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_46])).
% 3.31/1.74  tff(c_36, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.31/1.74  tff(c_241, plain, (![A_59, B_60]: (k3_subset_1(A_59, k3_subset_1(A_59, B_60))=B_60 | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.31/1.74  tff(c_257, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_36, c_241])).
% 3.31/1.74  tff(c_155, plain, (![A_50, B_51]: (m1_subset_1(k3_subset_1(A_50, B_51), k1_zfmisc_1(A_50)) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.74  tff(c_28, plain, (![A_14, B_15]: (k4_xboole_0(A_14, B_15)=k3_subset_1(A_14, B_15) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.31/1.74  tff(c_501, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k3_subset_1(A_78, B_79))=k3_subset_1(A_78, k3_subset_1(A_78, B_79)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(resolution, [status(thm)], [c_155, c_28])).
% 3.31/1.74  tff(c_512, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_501])).
% 3.31/1.74  tff(c_519, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_257, c_512])).
% 3.31/1.74  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.74  tff(c_569, plain, (![A_82]: (r1_xboole_0(A_82, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_82, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_519, c_2])).
% 3.31/1.74  tff(c_40, plain, (~r1_tarski('#skF_4', '#skF_5') | ~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.31/1.74  tff(c_70, plain, (~r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.31/1.74  tff(c_572, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_569, c_70])).
% 3.31/1.74  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_572])).
% 3.31/1.74  tff(c_577, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_40])).
% 3.31/1.74  tff(c_580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_577])).
% 3.31/1.74  tff(c_582, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_46])).
% 3.31/1.74  tff(c_38, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.31/1.74  tff(c_32, plain, (![A_18]: (~v1_xboole_0(k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.31/1.74  tff(c_585, plain, (![B_83, A_84]: (r2_hidden(B_83, A_84) | ~m1_subset_1(B_83, A_84) | v1_xboole_0(A_84))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.31/1.74  tff(c_8, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.31/1.74  tff(c_589, plain, (![B_83, A_7]: (r1_tarski(B_83, A_7) | ~m1_subset_1(B_83, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_585, c_8])).
% 3.31/1.74  tff(c_593, plain, (![B_85, A_86]: (r1_tarski(B_85, A_86) | ~m1_subset_1(B_85, k1_zfmisc_1(A_86)))), inference(negUnitSimplification, [status(thm)], [c_32, c_589])).
% 3.31/1.74  tff(c_605, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_593])).
% 3.31/1.74  tff(c_581, plain, (r1_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))), inference(splitRight, [status(thm)], [c_46])).
% 3.31/1.74  tff(c_656, plain, (![A_96, B_97]: (k3_subset_1(A_96, k3_subset_1(A_96, B_97))=B_97 | ~m1_subset_1(B_97, k1_zfmisc_1(A_96)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.31/1.74  tff(c_669, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(resolution, [status(thm)], [c_36, c_656])).
% 3.31/1.74  tff(c_752, plain, (![A_106, B_107]: (m1_subset_1(k3_subset_1(A_106, B_107), k1_zfmisc_1(A_106)) | ~m1_subset_1(B_107, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.74  tff(c_958, plain, (![A_124, B_125]: (k4_xboole_0(A_124, k3_subset_1(A_124, B_125))=k3_subset_1(A_124, k3_subset_1(A_124, B_125)) | ~m1_subset_1(B_125, k1_zfmisc_1(A_124)))), inference(resolution, [status(thm)], [c_752, c_28])).
% 3.31/1.74  tff(c_969, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_36, c_958])).
% 3.31/1.74  tff(c_976, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_669, c_969])).
% 3.31/1.74  tff(c_6, plain, (![A_4, B_5, C_6]: (r1_tarski(A_4, k4_xboole_0(B_5, C_6)) | ~r1_xboole_0(A_4, C_6) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.31/1.74  tff(c_1125, plain, (![A_135]: (r1_tarski(A_135, '#skF_5') | ~r1_xboole_0(A_135, k3_subset_1('#skF_3', '#skF_5')) | ~r1_tarski(A_135, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_976, c_6])).
% 3.31/1.74  tff(c_1131, plain, (r1_tarski('#skF_4', '#skF_5') | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_581, c_1125])).
% 3.31/1.74  tff(c_1135, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_605, c_1131])).
% 3.31/1.74  tff(c_1137, plain, $false, inference(negUnitSimplification, [status(thm)], [c_582, c_1135])).
% 3.31/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.74  
% 3.31/1.74  Inference rules
% 3.31/1.74  ----------------------
% 3.31/1.74  #Ref     : 0
% 3.31/1.74  #Sup     : 253
% 3.31/1.74  #Fact    : 0
% 3.31/1.74  #Define  : 0
% 3.31/1.74  #Split   : 2
% 3.31/1.74  #Chain   : 0
% 3.31/1.74  #Close   : 0
% 3.31/1.74  
% 3.31/1.74  Ordering : KBO
% 3.31/1.74  
% 3.31/1.74  Simplification rules
% 3.31/1.74  ----------------------
% 3.31/1.74  #Subsume      : 24
% 3.31/1.74  #Demod        : 35
% 3.31/1.74  #Tautology    : 100
% 3.31/1.74  #SimpNegUnit  : 5
% 3.31/1.74  #BackRed      : 0
% 3.31/1.74  
% 3.31/1.74  #Partial instantiations: 0
% 3.31/1.74  #Strategies tried      : 1
% 3.31/1.74  
% 3.31/1.74  Timing (in seconds)
% 3.31/1.75  ----------------------
% 3.31/1.75  Preprocessing        : 0.40
% 3.31/1.75  Parsing              : 0.21
% 3.31/1.75  CNF conversion       : 0.03
% 3.31/1.75  Main loop            : 0.44
% 3.31/1.75  Inferencing          : 0.17
% 3.31/1.75  Reduction            : 0.11
% 3.31/1.75  Demodulation         : 0.07
% 3.31/1.75  BG Simplification    : 0.03
% 3.31/1.75  Subsumption          : 0.08
% 3.31/1.75  Abstraction          : 0.03
% 3.31/1.75  MUC search           : 0.00
% 3.31/1.75  Cooper               : 0.00
% 3.31/1.75  Total                : 0.87
% 3.31/1.75  Index Insertion      : 0.00
% 3.31/1.75  Index Deletion       : 0.00
% 3.31/1.75  Index Matching       : 0.00
% 3.31/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
