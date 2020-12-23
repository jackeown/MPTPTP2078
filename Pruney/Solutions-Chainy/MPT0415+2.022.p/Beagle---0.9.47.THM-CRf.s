%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:48 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   27 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  71 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_120,plain,(
    ! [A_44] : k4_xboole_0(A_44,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_116])).

tff(c_14,plain,(
    ! [C_11,B_10] : ~ r2_hidden(C_11,k4_xboole_0(B_10,k1_tarski(C_11))) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_125,plain,(
    ! [C_11] : ~ r2_hidden(C_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_14])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_240,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_1'(A_81,B_82,C_83),C_83)
      | r2_hidden(k3_subset_1(A_81,'#skF_1'(A_81,B_82,C_83)),B_82)
      | k7_setfam_1(A_81,B_82) = C_83
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k1_zfmisc_1(A_81)))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_276,plain,(
    ! [A_81,C_83] :
      ( r2_hidden('#skF_1'(A_81,k1_xboole_0,C_83),C_83)
      | k7_setfam_1(A_81,k1_xboole_0) = C_83
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k1_zfmisc_1(A_81)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(resolution,[status(thm)],[c_240,c_125])).

tff(c_288,plain,(
    ! [A_84,C_85] :
      ( r2_hidden('#skF_1'(A_84,k1_xboole_0,C_85),C_85)
      | k7_setfam_1(A_84,k1_xboole_0) = C_85
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_276])).

tff(c_296,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_1'(A_84,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_84,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_288])).

tff(c_306,plain,(
    ! [A_86] : k7_setfam_1(A_86,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_296])).

tff(c_40,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_148,plain,(
    ! [A_55,B_56] :
      ( k7_setfam_1(A_55,k7_setfam_1(A_55,B_56)) = B_56
      | ~ m1_subset_1(B_56,k1_zfmisc_1(k1_zfmisc_1(A_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_150,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_148])).

tff(c_155,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_150])).

tff(c_312,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_306,c_155])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.37  
% 2.31/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.37  %$ r2_hidden > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.31/1.37  
% 2.31/1.37  %Foreground sorts:
% 2.31/1.37  
% 2.31/1.37  
% 2.31/1.37  %Background operators:
% 2.31/1.37  
% 2.31/1.37  
% 2.31/1.37  %Foreground operators:
% 2.31/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.31/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.37  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.31/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.31/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.37  
% 2.31/1.38  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.31/1.38  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.31/1.38  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.31/1.38  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.31/1.38  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.31/1.38  tff(f_44, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.31/1.38  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.31/1.38  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.31/1.38  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.38  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.31/1.38  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.38  tff(c_107, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.38  tff(c_116, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 2.31/1.38  tff(c_120, plain, (![A_44]: (k4_xboole_0(A_44, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_116])).
% 2.31/1.38  tff(c_14, plain, (![C_11, B_10]: (~r2_hidden(C_11, k4_xboole_0(B_10, k1_tarski(C_11))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.31/1.38  tff(c_125, plain, (![C_11]: (~r2_hidden(C_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_120, c_14])).
% 2.31/1.38  tff(c_18, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.31/1.38  tff(c_240, plain, (![A_81, B_82, C_83]: (r2_hidden('#skF_1'(A_81, B_82, C_83), C_83) | r2_hidden(k3_subset_1(A_81, '#skF_1'(A_81, B_82, C_83)), B_82) | k7_setfam_1(A_81, B_82)=C_83 | ~m1_subset_1(C_83, k1_zfmisc_1(k1_zfmisc_1(A_81))) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.31/1.38  tff(c_276, plain, (![A_81, C_83]: (r2_hidden('#skF_1'(A_81, k1_xboole_0, C_83), C_83) | k7_setfam_1(A_81, k1_xboole_0)=C_83 | ~m1_subset_1(C_83, k1_zfmisc_1(k1_zfmisc_1(A_81))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(resolution, [status(thm)], [c_240, c_125])).
% 2.31/1.38  tff(c_288, plain, (![A_84, C_85]: (r2_hidden('#skF_1'(A_84, k1_xboole_0, C_85), C_85) | k7_setfam_1(A_84, k1_xboole_0)=C_85 | ~m1_subset_1(C_85, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_276])).
% 2.31/1.38  tff(c_296, plain, (![A_84]: (r2_hidden('#skF_1'(A_84, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_84, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_288])).
% 2.31/1.38  tff(c_306, plain, (![A_86]: (k7_setfam_1(A_86, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_125, c_296])).
% 2.31/1.38  tff(c_40, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.38  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.31/1.38  tff(c_148, plain, (![A_55, B_56]: (k7_setfam_1(A_55, k7_setfam_1(A_55, B_56))=B_56 | ~m1_subset_1(B_56, k1_zfmisc_1(k1_zfmisc_1(A_55))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.31/1.38  tff(c_150, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_44, c_148])).
% 2.31/1.38  tff(c_155, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_150])).
% 2.31/1.38  tff(c_312, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_306, c_155])).
% 2.31/1.38  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_312])).
% 2.31/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.38  
% 2.31/1.38  Inference rules
% 2.31/1.38  ----------------------
% 2.31/1.38  #Ref     : 0
% 2.31/1.38  #Sup     : 63
% 2.31/1.38  #Fact    : 0
% 2.31/1.38  #Define  : 0
% 2.31/1.38  #Split   : 0
% 2.31/1.38  #Chain   : 0
% 2.31/1.38  #Close   : 0
% 2.31/1.38  
% 2.31/1.38  Ordering : KBO
% 2.31/1.38  
% 2.31/1.38  Simplification rules
% 2.31/1.38  ----------------------
% 2.31/1.38  #Subsume      : 12
% 2.31/1.38  #Demod        : 20
% 2.31/1.38  #Tautology    : 30
% 2.31/1.38  #SimpNegUnit  : 6
% 2.31/1.38  #BackRed      : 1
% 2.31/1.38  
% 2.31/1.38  #Partial instantiations: 0
% 2.31/1.38  #Strategies tried      : 1
% 2.31/1.38  
% 2.31/1.38  Timing (in seconds)
% 2.31/1.38  ----------------------
% 2.31/1.39  Preprocessing        : 0.33
% 2.31/1.39  Parsing              : 0.17
% 2.31/1.39  CNF conversion       : 0.02
% 2.31/1.39  Main loop            : 0.21
% 2.31/1.39  Inferencing          : 0.08
% 2.31/1.39  Reduction            : 0.06
% 2.31/1.39  Demodulation         : 0.04
% 2.31/1.39  BG Simplification    : 0.02
% 2.31/1.39  Subsumption          : 0.04
% 2.31/1.39  Abstraction          : 0.01
% 2.31/1.39  MUC search           : 0.00
% 2.31/1.39  Cooper               : 0.00
% 2.31/1.39  Total                : 0.56
% 2.31/1.39  Index Insertion      : 0.00
% 2.31/1.39  Index Deletion       : 0.00
% 2.31/1.39  Index Matching       : 0.00
% 2.31/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
