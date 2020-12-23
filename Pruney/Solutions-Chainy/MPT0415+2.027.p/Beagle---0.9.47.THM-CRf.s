%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:49 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   51 (  69 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   55 (  81 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
         => ( C = k7_setfam_1(A,B)
          <=> ! [D] :
                ( m1_subset_1(D,k1_zfmisc_1(A))
               => ( r2_hidden(D,C)
                <=> r2_hidden(k3_subset_1(A,D),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    ! [A_36,B_37] :
      ( k3_xboole_0(A_36,B_37) = A_36
      | ~ r1_tarski(A_36,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_5] : k3_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_70])).

tff(c_91,plain,(
    ! [A_41,B_42] : k5_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_100,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_91])).

tff(c_104,plain,(
    ! [A_43] : k4_xboole_0(k1_xboole_0,A_43) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_100])).

tff(c_16,plain,(
    ! [C_12,B_11] : ~ r2_hidden(C_12,k4_xboole_0(B_11,k1_tarski(C_12))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109,plain,(
    ! [C_12] : ~ r2_hidden(C_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_20,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_229,plain,(
    ! [A_81,B_82,C_83] :
      ( r2_hidden('#skF_1'(A_81,B_82,C_83),C_83)
      | r2_hidden(k3_subset_1(A_81,'#skF_1'(A_81,B_82,C_83)),B_82)
      | k7_setfam_1(A_81,B_82) = C_83
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k1_zfmisc_1(A_81)))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_259,plain,(
    ! [A_81,C_83] :
      ( r2_hidden('#skF_1'(A_81,k1_xboole_0,C_83),C_83)
      | k7_setfam_1(A_81,k1_xboole_0) = C_83
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k1_zfmisc_1(A_81)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(resolution,[status(thm)],[c_229,c_109])).

tff(c_270,plain,(
    ! [A_84,C_85] :
      ( r2_hidden('#skF_1'(A_84,k1_xboole_0,C_85),C_85)
      | k7_setfam_1(A_84,k1_xboole_0) = C_85
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k1_zfmisc_1(A_84))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_259])).

tff(c_278,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_1'(A_84,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_84,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_270])).

tff(c_288,plain,(
    ! [A_86] : k7_setfam_1(A_86,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_278])).

tff(c_40,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_133,plain,(
    ! [A_54,B_55] :
      ( k7_setfam_1(A_54,k7_setfam_1(A_54,B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(k1_zfmisc_1(A_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_44,c_133])).

tff(c_140,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_135])).

tff(c_294,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_140])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_294])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:25:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.36  
% 2.13/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.13/1.36  
% 2.13/1.36  %Foreground sorts:
% 2.13/1.36  
% 2.13/1.36  
% 2.13/1.36  %Background operators:
% 2.13/1.36  
% 2.13/1.36  
% 2.13/1.36  %Foreground operators:
% 2.13/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.13/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.36  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.13/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.36  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.13/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.36  
% 2.13/1.37  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.13/1.37  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.13/1.37  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.13/1.37  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.37  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.13/1.37  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.13/1.37  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.13/1.37  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.13/1.37  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.13/1.37  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.37  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.37  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.13/1.37  tff(c_70, plain, (![A_36, B_37]: (k3_xboole_0(A_36, B_37)=A_36 | ~r1_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.37  tff(c_74, plain, (![A_5]: (k3_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_70])).
% 2.13/1.37  tff(c_91, plain, (![A_41, B_42]: (k5_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.13/1.37  tff(c_100, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_74, c_91])).
% 2.13/1.37  tff(c_104, plain, (![A_43]: (k4_xboole_0(k1_xboole_0, A_43)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_100])).
% 2.13/1.37  tff(c_16, plain, (![C_12, B_11]: (~r2_hidden(C_12, k4_xboole_0(B_11, k1_tarski(C_12))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.13/1.37  tff(c_109, plain, (![C_12]: (~r2_hidden(C_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_104, c_16])).
% 2.13/1.37  tff(c_20, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.13/1.37  tff(c_229, plain, (![A_81, B_82, C_83]: (r2_hidden('#skF_1'(A_81, B_82, C_83), C_83) | r2_hidden(k3_subset_1(A_81, '#skF_1'(A_81, B_82, C_83)), B_82) | k7_setfam_1(A_81, B_82)=C_83 | ~m1_subset_1(C_83, k1_zfmisc_1(k1_zfmisc_1(A_81))) | ~m1_subset_1(B_82, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.13/1.37  tff(c_259, plain, (![A_81, C_83]: (r2_hidden('#skF_1'(A_81, k1_xboole_0, C_83), C_83) | k7_setfam_1(A_81, k1_xboole_0)=C_83 | ~m1_subset_1(C_83, k1_zfmisc_1(k1_zfmisc_1(A_81))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(resolution, [status(thm)], [c_229, c_109])).
% 2.13/1.37  tff(c_270, plain, (![A_84, C_85]: (r2_hidden('#skF_1'(A_84, k1_xboole_0, C_85), C_85) | k7_setfam_1(A_84, k1_xboole_0)=C_85 | ~m1_subset_1(C_85, k1_zfmisc_1(k1_zfmisc_1(A_84))))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_259])).
% 2.13/1.37  tff(c_278, plain, (![A_84]: (r2_hidden('#skF_1'(A_84, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_84, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_270])).
% 2.13/1.37  tff(c_288, plain, (![A_86]: (k7_setfam_1(A_86, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_109, c_278])).
% 2.13/1.37  tff(c_40, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.37  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.13/1.37  tff(c_133, plain, (![A_54, B_55]: (k7_setfam_1(A_54, k7_setfam_1(A_54, B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(k1_zfmisc_1(A_54))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.13/1.37  tff(c_135, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_44, c_133])).
% 2.13/1.37  tff(c_140, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_135])).
% 2.13/1.37  tff(c_294, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_288, c_140])).
% 2.13/1.37  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_294])).
% 2.13/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.37  
% 2.13/1.37  Inference rules
% 2.13/1.37  ----------------------
% 2.13/1.37  #Ref     : 0
% 2.13/1.37  #Sup     : 59
% 2.13/1.37  #Fact    : 0
% 2.13/1.37  #Define  : 0
% 2.13/1.37  #Split   : 0
% 2.13/1.37  #Chain   : 0
% 2.13/1.37  #Close   : 0
% 2.13/1.37  
% 2.13/1.37  Ordering : KBO
% 2.13/1.37  
% 2.13/1.37  Simplification rules
% 2.13/1.37  ----------------------
% 2.13/1.37  #Subsume      : 13
% 2.13/1.37  #Demod        : 19
% 2.13/1.37  #Tautology    : 27
% 2.13/1.37  #SimpNegUnit  : 7
% 2.13/1.37  #BackRed      : 1
% 2.13/1.37  
% 2.13/1.37  #Partial instantiations: 0
% 2.13/1.37  #Strategies tried      : 1
% 2.13/1.37  
% 2.13/1.37  Timing (in seconds)
% 2.13/1.37  ----------------------
% 2.13/1.37  Preprocessing        : 0.30
% 2.13/1.37  Parsing              : 0.15
% 2.13/1.37  CNF conversion       : 0.02
% 2.13/1.38  Main loop            : 0.21
% 2.13/1.38  Inferencing          : 0.08
% 2.13/1.38  Reduction            : 0.06
% 2.13/1.38  Demodulation         : 0.04
% 2.13/1.38  BG Simplification    : 0.01
% 2.13/1.38  Subsumption          : 0.04
% 2.13/1.38  Abstraction          : 0.01
% 2.13/1.38  MUC search           : 0.00
% 2.13/1.38  Cooper               : 0.00
% 2.13/1.38  Total                : 0.53
% 2.13/1.38  Index Insertion      : 0.00
% 2.13/1.38  Index Deletion       : 0.00
% 2.13/1.38  Index Matching       : 0.00
% 2.13/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
