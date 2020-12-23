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
% DateTime   : Thu Dec  3 09:55:42 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   48 (  76 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 150 expanded)
%              Number of equality atoms :   26 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k4_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_12] : m1_subset_1(k2_subset_1(A_12),k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_35,plain,(
    ! [A_12] : m1_subset_1(A_12,k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_149,plain,(
    ! [A_45,B_46,C_47] :
      ( k4_subset_1(A_45,B_46,C_47) = k2_xboole_0(B_46,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [A_48,B_49] :
      ( k4_subset_1(A_48,B_49,A_48) = k2_xboole_0(B_49,A_48)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(resolution,[status(thm)],[c_35,c_149])).

tff(c_162,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_156])).

tff(c_32,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_36,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_32])).

tff(c_170,plain,(
    k2_xboole_0('#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_36])).

tff(c_376,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden('#skF_1'(A_73,B_74,C_75),B_74)
      | r2_hidden('#skF_1'(A_73,B_74,C_75),A_73)
      | r2_hidden('#skF_2'(A_73,B_74,C_75),C_75)
      | k2_xboole_0(A_73,B_74) = C_75 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_18,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_454,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79,A_78),B_79)
      | r2_hidden('#skF_2'(A_78,B_79,A_78),A_78)
      | k2_xboole_0(A_78,B_79) = A_78 ) ),
    inference(resolution,[status(thm)],[c_376,c_18])).

tff(c_244,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_1'(A_65,B_66,C_67),B_66)
      | r2_hidden('#skF_1'(A_65,B_66,C_67),A_65)
      | ~ r2_hidden('#skF_2'(A_65,B_66,C_67),A_65)
      | k2_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4,C_5),C_5)
      | ~ r2_hidden('#skF_2'(A_3,B_4,C_5),A_3)
      | k2_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_291,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66,A_65),B_66)
      | ~ r2_hidden('#skF_2'(A_65,B_66,A_65),A_65)
      | k2_xboole_0(A_65,B_66) = A_65 ) ),
    inference(resolution,[status(thm)],[c_244,c_14])).

tff(c_630,plain,(
    ! [A_86,B_87] :
      ( r2_hidden('#skF_1'(A_86,B_87,A_86),B_87)
      | k2_xboole_0(A_86,B_87) = A_86 ) ),
    inference(resolution,[status(thm)],[c_454,c_291])).

tff(c_28,plain,(
    ! [C_16,A_13,B_14] :
      ( r2_hidden(C_16,A_13)
      | ~ r2_hidden(C_16,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_705,plain,(
    ! [A_90,B_91,A_92] :
      ( r2_hidden('#skF_1'(A_90,B_91,A_90),A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | k2_xboole_0(A_90,B_91) = A_90 ) ),
    inference(resolution,[status(thm)],[c_630,c_28])).

tff(c_727,plain,(
    ! [A_92,B_91] :
      ( r2_hidden('#skF_2'(A_92,B_91,A_92),A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | k2_xboole_0(A_92,B_91) = A_92 ) ),
    inference(resolution,[status(thm)],[c_705,c_18])).

tff(c_779,plain,(
    ! [A_97,B_98] :
      ( ~ r2_hidden('#skF_2'(A_97,B_98,A_97),A_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97))
      | k2_xboole_0(A_97,B_98) = A_97 ) ),
    inference(resolution,[status(thm)],[c_705,c_14])).

tff(c_798,plain,(
    ! [B_99,A_100] :
      ( ~ m1_subset_1(B_99,k1_zfmisc_1(A_100))
      | k2_xboole_0(A_100,B_99) = A_100 ) ),
    inference(resolution,[status(thm)],[c_727,c_779])).

tff(c_807,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_798])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_827,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_2])).

tff(c_840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_170,c_827])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n011.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 18:43:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.47  
% 3.01/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.47  %$ r2_hidden > m1_subset_1 > k4_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.01/1.47  
% 3.01/1.47  %Foreground sorts:
% 3.01/1.47  
% 3.01/1.47  
% 3.01/1.47  %Background operators:
% 3.01/1.47  
% 3.01/1.47  
% 3.01/1.47  %Foreground operators:
% 3.01/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.01/1.47  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.01/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.01/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.01/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.01/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.01/1.47  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.01/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.47  
% 3.12/1.49  tff(f_60, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.12/1.49  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.12/1.49  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.12/1.49  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.12/1.49  tff(f_36, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.12/1.49  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.12/1.49  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.12/1.49  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.12/1.49  tff(c_24, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.12/1.49  tff(c_26, plain, (![A_12]: (m1_subset_1(k2_subset_1(A_12), k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.12/1.49  tff(c_35, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 3.12/1.49  tff(c_149, plain, (![A_45, B_46, C_47]: (k4_subset_1(A_45, B_46, C_47)=k2_xboole_0(B_46, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.12/1.49  tff(c_156, plain, (![A_48, B_49]: (k4_subset_1(A_48, B_49, A_48)=k2_xboole_0(B_49, A_48) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(resolution, [status(thm)], [c_35, c_149])).
% 3.12/1.49  tff(c_162, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_156])).
% 3.12/1.49  tff(c_32, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.12/1.49  tff(c_36, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_32])).
% 3.12/1.49  tff(c_170, plain, (k2_xboole_0('#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_162, c_36])).
% 3.12/1.49  tff(c_376, plain, (![A_73, B_74, C_75]: (r2_hidden('#skF_1'(A_73, B_74, C_75), B_74) | r2_hidden('#skF_1'(A_73, B_74, C_75), A_73) | r2_hidden('#skF_2'(A_73, B_74, C_75), C_75) | k2_xboole_0(A_73, B_74)=C_75)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.12/1.49  tff(c_18, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.12/1.49  tff(c_454, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79, A_78), B_79) | r2_hidden('#skF_2'(A_78, B_79, A_78), A_78) | k2_xboole_0(A_78, B_79)=A_78)), inference(resolution, [status(thm)], [c_376, c_18])).
% 3.12/1.49  tff(c_244, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_1'(A_65, B_66, C_67), B_66) | r2_hidden('#skF_1'(A_65, B_66, C_67), A_65) | ~r2_hidden('#skF_2'(A_65, B_66, C_67), A_65) | k2_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.12/1.49  tff(c_14, plain, (![A_3, B_4, C_5]: (~r2_hidden('#skF_1'(A_3, B_4, C_5), C_5) | ~r2_hidden('#skF_2'(A_3, B_4, C_5), A_3) | k2_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.12/1.49  tff(c_291, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66, A_65), B_66) | ~r2_hidden('#skF_2'(A_65, B_66, A_65), A_65) | k2_xboole_0(A_65, B_66)=A_65)), inference(resolution, [status(thm)], [c_244, c_14])).
% 3.12/1.49  tff(c_630, plain, (![A_86, B_87]: (r2_hidden('#skF_1'(A_86, B_87, A_86), B_87) | k2_xboole_0(A_86, B_87)=A_86)), inference(resolution, [status(thm)], [c_454, c_291])).
% 3.12/1.49  tff(c_28, plain, (![C_16, A_13, B_14]: (r2_hidden(C_16, A_13) | ~r2_hidden(C_16, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.12/1.49  tff(c_705, plain, (![A_90, B_91, A_92]: (r2_hidden('#skF_1'(A_90, B_91, A_90), A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | k2_xboole_0(A_90, B_91)=A_90)), inference(resolution, [status(thm)], [c_630, c_28])).
% 3.12/1.49  tff(c_727, plain, (![A_92, B_91]: (r2_hidden('#skF_2'(A_92, B_91, A_92), A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | k2_xboole_0(A_92, B_91)=A_92)), inference(resolution, [status(thm)], [c_705, c_18])).
% 3.12/1.49  tff(c_779, plain, (![A_97, B_98]: (~r2_hidden('#skF_2'(A_97, B_98, A_97), A_97) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)) | k2_xboole_0(A_97, B_98)=A_97)), inference(resolution, [status(thm)], [c_705, c_14])).
% 3.12/1.49  tff(c_798, plain, (![B_99, A_100]: (~m1_subset_1(B_99, k1_zfmisc_1(A_100)) | k2_xboole_0(A_100, B_99)=A_100)), inference(resolution, [status(thm)], [c_727, c_779])).
% 3.12/1.49  tff(c_807, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_34, c_798])).
% 3.12/1.49  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.12/1.49  tff(c_827, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_807, c_2])).
% 3.12/1.49  tff(c_840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_170, c_827])).
% 3.12/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.49  
% 3.12/1.49  Inference rules
% 3.12/1.49  ----------------------
% 3.12/1.49  #Ref     : 0
% 3.12/1.49  #Sup     : 181
% 3.12/1.49  #Fact    : 6
% 3.12/1.49  #Define  : 0
% 3.12/1.49  #Split   : 0
% 3.12/1.49  #Chain   : 0
% 3.12/1.49  #Close   : 0
% 3.12/1.49  
% 3.12/1.49  Ordering : KBO
% 3.12/1.49  
% 3.12/1.49  Simplification rules
% 3.12/1.49  ----------------------
% 3.12/1.49  #Subsume      : 37
% 3.12/1.49  #Demod        : 22
% 3.12/1.49  #Tautology    : 53
% 3.12/1.49  #SimpNegUnit  : 1
% 3.12/1.49  #BackRed      : 4
% 3.12/1.49  
% 3.12/1.49  #Partial instantiations: 0
% 3.12/1.49  #Strategies tried      : 1
% 3.12/1.49  
% 3.12/1.49  Timing (in seconds)
% 3.12/1.49  ----------------------
% 3.12/1.49  Preprocessing        : 0.28
% 3.12/1.49  Parsing              : 0.14
% 3.12/1.49  CNF conversion       : 0.02
% 3.12/1.49  Main loop            : 0.46
% 3.12/1.49  Inferencing          : 0.17
% 3.12/1.49  Reduction            : 0.13
% 3.12/1.49  Demodulation         : 0.10
% 3.12/1.49  BG Simplification    : 0.02
% 3.12/1.49  Subsumption          : 0.11
% 3.12/1.49  Abstraction          : 0.03
% 3.12/1.49  MUC search           : 0.00
% 3.12/1.49  Cooper               : 0.00
% 3.12/1.49  Total                : 0.77
% 3.12/1.49  Index Insertion      : 0.00
% 3.12/1.49  Index Deletion       : 0.00
% 3.12/1.49  Index Matching       : 0.00
% 3.12/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
