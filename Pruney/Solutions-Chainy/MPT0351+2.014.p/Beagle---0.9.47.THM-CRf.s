%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:38 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.96s
% Verified   : 
% Statistics : Number of formulae       :   54 (  62 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  66 expanded)
%              Number of equality atoms :   22 (  28 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_52,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_23] : m1_subset_1(k2_subset_1(A_23),k1_zfmisc_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_35,plain,(
    ! [A_23] : m1_subset_1(A_23,k1_zfmisc_1(A_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26])).

tff(c_367,plain,(
    ! [A_72,B_73,C_74] :
      ( k4_subset_1(A_72,B_73,C_74) = k2_xboole_0(B_73,C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_72))
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_395,plain,(
    ! [A_76,B_77] :
      ( k4_subset_1(A_76,B_77,A_76) = k2_xboole_0(B_77,A_76)
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_35,c_367])).

tff(c_402,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_395])).

tff(c_32,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_32])).

tff(c_424,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_36])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_300,plain,(
    ! [C_65,A_66,B_67] :
      ( r2_hidden(C_65,A_66)
      | ~ r2_hidden(C_65,B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_429,plain,(
    ! [A_82,B_83,A_84] :
      ( r2_hidden('#skF_1'(A_82,B_83),A_84)
      | ~ m1_subset_1(A_82,k1_zfmisc_1(A_84))
      | r1_tarski(A_82,B_83) ) ),
    inference(resolution,[status(thm)],[c_8,c_300])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_441,plain,(
    ! [A_85,A_86] :
      ( ~ m1_subset_1(A_85,k1_zfmisc_1(A_86))
      | r1_tarski(A_85,A_86) ) ),
    inference(resolution,[status(thm)],[c_429,c_6])).

tff(c_450,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_441])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_454,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_450,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_138,plain,(
    ! [A_43,B_44] : k2_xboole_0(k3_xboole_0(A_43,B_44),k4_xboole_0(A_43,B_44)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_147,plain,(
    ! [B_2,A_1] : k2_xboole_0(k3_xboole_0(B_2,A_1),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_138])).

tff(c_461,plain,(
    k2_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_454,c_147])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_508,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_14])).

tff(c_515,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_424,c_508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:29:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.80  
% 2.96/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.80  %$ r2_hidden > r1_tarski > m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.96/1.80  
% 2.96/1.80  %Foreground sorts:
% 2.96/1.80  
% 2.96/1.80  
% 2.96/1.80  %Background operators:
% 2.96/1.80  
% 2.96/1.80  
% 2.96/1.80  %Foreground operators:
% 2.96/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.96/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.96/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.96/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.96/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.96/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.96/1.80  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.96/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.96/1.80  tff('#skF_2', type, '#skF_2': $i).
% 2.96/1.80  tff('#skF_3', type, '#skF_3': $i).
% 2.96/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.96/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.96/1.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.96/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.96/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.96/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.96/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.96/1.80  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.96/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.96/1.80  
% 2.96/1.82  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.96/1.82  tff(f_52, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.96/1.82  tff(f_54, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.96/1.82  tff(f_67, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.96/1.82  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.96/1.82  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 2.96/1.82  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.96/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.96/1.82  tff(f_44, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.96/1.82  tff(f_42, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.96/1.82  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.96/1.82  tff(c_24, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.96/1.82  tff(c_26, plain, (![A_23]: (m1_subset_1(k2_subset_1(A_23), k1_zfmisc_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.96/1.82  tff(c_35, plain, (![A_23]: (m1_subset_1(A_23, k1_zfmisc_1(A_23)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26])).
% 2.96/1.82  tff(c_367, plain, (![A_72, B_73, C_74]: (k4_subset_1(A_72, B_73, C_74)=k2_xboole_0(B_73, C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(A_72)) | ~m1_subset_1(B_73, k1_zfmisc_1(A_72)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.96/1.82  tff(c_395, plain, (![A_76, B_77]: (k4_subset_1(A_76, B_77, A_76)=k2_xboole_0(B_77, A_76) | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(resolution, [status(thm)], [c_35, c_367])).
% 2.96/1.82  tff(c_402, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_395])).
% 2.96/1.82  tff(c_32, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.96/1.82  tff(c_36, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_32])).
% 2.96/1.82  tff(c_424, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_402, c_36])).
% 2.96/1.82  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.96/1.82  tff(c_300, plain, (![C_65, A_66, B_67]: (r2_hidden(C_65, A_66) | ~r2_hidden(C_65, B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.96/1.82  tff(c_429, plain, (![A_82, B_83, A_84]: (r2_hidden('#skF_1'(A_82, B_83), A_84) | ~m1_subset_1(A_82, k1_zfmisc_1(A_84)) | r1_tarski(A_82, B_83))), inference(resolution, [status(thm)], [c_8, c_300])).
% 2.96/1.82  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.96/1.82  tff(c_441, plain, (![A_85, A_86]: (~m1_subset_1(A_85, k1_zfmisc_1(A_86)) | r1_tarski(A_85, A_86))), inference(resolution, [status(thm)], [c_429, c_6])).
% 2.96/1.82  tff(c_450, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_441])).
% 2.96/1.82  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.96/1.82  tff(c_454, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_450, c_12])).
% 2.96/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.96/1.82  tff(c_138, plain, (![A_43, B_44]: (k2_xboole_0(k3_xboole_0(A_43, B_44), k4_xboole_0(A_43, B_44))=A_43)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.96/1.82  tff(c_147, plain, (![B_2, A_1]: (k2_xboole_0(k3_xboole_0(B_2, A_1), k4_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_138])).
% 2.96/1.82  tff(c_461, plain, (k2_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_454, c_147])).
% 2.96/1.82  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.96/1.82  tff(c_508, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_461, c_14])).
% 2.96/1.82  tff(c_515, plain, $false, inference(negUnitSimplification, [status(thm)], [c_424, c_508])).
% 2.96/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.96/1.82  
% 2.96/1.82  Inference rules
% 2.96/1.82  ----------------------
% 2.96/1.82  #Ref     : 0
% 2.96/1.82  #Sup     : 122
% 2.96/1.82  #Fact    : 0
% 2.96/1.82  #Define  : 0
% 2.96/1.82  #Split   : 0
% 2.96/1.82  #Chain   : 0
% 2.96/1.82  #Close   : 0
% 2.96/1.82  
% 2.96/1.82  Ordering : KBO
% 2.96/1.82  
% 2.96/1.82  Simplification rules
% 2.96/1.82  ----------------------
% 2.96/1.82  #Subsume      : 2
% 2.96/1.82  #Demod        : 31
% 2.96/1.82  #Tautology    : 88
% 2.96/1.82  #SimpNegUnit  : 1
% 2.96/1.82  #BackRed      : 2
% 2.96/1.82  
% 2.96/1.82  #Partial instantiations: 0
% 2.96/1.82  #Strategies tried      : 1
% 2.96/1.82  
% 2.96/1.82  Timing (in seconds)
% 2.96/1.82  ----------------------
% 2.96/1.83  Preprocessing        : 0.49
% 2.96/1.83  Parsing              : 0.26
% 2.96/1.83  CNF conversion       : 0.03
% 2.96/1.83  Main loop            : 0.43
% 2.96/1.83  Inferencing          : 0.17
% 2.96/1.83  Reduction            : 0.14
% 2.96/1.83  Demodulation         : 0.11
% 2.96/1.83  BG Simplification    : 0.02
% 2.96/1.83  Subsumption          : 0.07
% 2.96/1.83  Abstraction          : 0.03
% 2.96/1.83  MUC search           : 0.00
% 2.96/1.83  Cooper               : 0.00
% 2.96/1.83  Total                : 0.96
% 2.96/1.83  Index Insertion      : 0.00
% 2.96/1.83  Index Deletion       : 0.00
% 2.96/1.83  Index Matching       : 0.00
% 2.96/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
