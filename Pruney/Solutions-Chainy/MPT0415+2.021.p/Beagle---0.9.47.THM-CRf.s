%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:48 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   54 (  75 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   11
%              Number of atoms          :   60 (  91 expanded)
%              Number of equality atoms :   30 (  49 expanded)
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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ~ ( B != k1_xboole_0
            & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
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

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_100,plain,(
    ! [A_44,B_45] : k5_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_109,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_100])).

tff(c_112,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_109])).

tff(c_18,plain,(
    ! [B_13] : k4_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) != k1_tarski(B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_113,plain,(
    ! [B_13] : k1_tarski(B_13) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_18])).

tff(c_88,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [A_39] :
      ( k1_tarski(A_39) = k1_xboole_0
      | ~ r2_hidden(A_39,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_88,c_6])).

tff(c_141,plain,(
    ! [A_39] : ~ r2_hidden(A_39,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_93])).

tff(c_22,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_221,plain,(
    ! [A_78,B_79,C_80] :
      ( r2_hidden('#skF_1'(A_78,B_79,C_80),C_80)
      | r2_hidden(k3_subset_1(A_78,'#skF_1'(A_78,B_79,C_80)),B_79)
      | k7_setfam_1(A_78,B_79) = C_80
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k1_zfmisc_1(A_78)))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_243,plain,(
    ! [A_78,C_80] :
      ( r2_hidden('#skF_1'(A_78,k1_xboole_0,C_80),C_80)
      | k7_setfam_1(A_78,k1_xboole_0) = C_80
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k1_zfmisc_1(A_78)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(resolution,[status(thm)],[c_221,c_141])).

tff(c_252,plain,(
    ! [A_81,C_82] :
      ( r2_hidden('#skF_1'(A_81,k1_xboole_0,C_82),C_82)
      | k7_setfam_1(A_81,k1_xboole_0) = C_82
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k1_zfmisc_1(A_81))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_243])).

tff(c_260,plain,(
    ! [A_81] :
      ( r2_hidden('#skF_1'(A_81,k1_xboole_0,k1_xboole_0),k1_xboole_0)
      | k7_setfam_1(A_81,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_22,c_252])).

tff(c_279,plain,(
    ! [A_86] : k7_setfam_1(A_86,k1_xboole_0) = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_260])).

tff(c_42,plain,(
    k7_setfam_1('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_156,plain,(
    ! [A_57,B_58] :
      ( k7_setfam_1(A_57,k7_setfam_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(k1_zfmisc_1(A_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_158,plain,(
    k7_setfam_1('#skF_2',k7_setfam_1('#skF_2','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_156])).

tff(c_163,plain,(
    k7_setfam_1('#skF_2',k1_xboole_0) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_158])).

tff(c_285,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_163])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_285])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.26  
% 2.14/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.27  %$ r2_hidden > r1_tarski > m1_subset_1 > k1_enumset1 > k7_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.14/1.27  
% 2.14/1.27  %Foreground sorts:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Background operators:
% 2.14/1.27  
% 2.14/1.27  
% 2.14/1.27  %Foreground operators:
% 2.14/1.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.27  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 2.14/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.14/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.14/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.14/1.27  
% 2.14/1.28  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 2.14/1.28  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.14/1.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.14/1.28  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.14/1.28  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.14/1.28  tff(f_43, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.14/1.28  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.14/1.28  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.14/1.28  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => ((C = k7_setfam_1(A, B)) <=> (![D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (r2_hidden(D, C) <=> r2_hidden(k3_subset_1(A, D), B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_setfam_1)).
% 2.14/1.28  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 2.14/1.28  tff(c_44, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.28  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.28  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.28  tff(c_100, plain, (![A_44, B_45]: (k5_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.28  tff(c_109, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_100])).
% 2.14/1.28  tff(c_112, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_109])).
% 2.14/1.28  tff(c_18, plain, (![B_13]: (k4_xboole_0(k1_tarski(B_13), k1_tarski(B_13))!=k1_tarski(B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.14/1.28  tff(c_113, plain, (![B_13]: (k1_tarski(B_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_18])).
% 2.14/1.28  tff(c_88, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.28  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.28  tff(c_93, plain, (![A_39]: (k1_tarski(A_39)=k1_xboole_0 | ~r2_hidden(A_39, k1_xboole_0))), inference(resolution, [status(thm)], [c_88, c_6])).
% 2.14/1.28  tff(c_141, plain, (![A_39]: (~r2_hidden(A_39, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_113, c_93])).
% 2.14/1.28  tff(c_22, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.28  tff(c_221, plain, (![A_78, B_79, C_80]: (r2_hidden('#skF_1'(A_78, B_79, C_80), C_80) | r2_hidden(k3_subset_1(A_78, '#skF_1'(A_78, B_79, C_80)), B_79) | k7_setfam_1(A_78, B_79)=C_80 | ~m1_subset_1(C_80, k1_zfmisc_1(k1_zfmisc_1(A_78))) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.28  tff(c_243, plain, (![A_78, C_80]: (r2_hidden('#skF_1'(A_78, k1_xboole_0, C_80), C_80) | k7_setfam_1(A_78, k1_xboole_0)=C_80 | ~m1_subset_1(C_80, k1_zfmisc_1(k1_zfmisc_1(A_78))) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(resolution, [status(thm)], [c_221, c_141])).
% 2.14/1.28  tff(c_252, plain, (![A_81, C_82]: (r2_hidden('#skF_1'(A_81, k1_xboole_0, C_82), C_82) | k7_setfam_1(A_81, k1_xboole_0)=C_82 | ~m1_subset_1(C_82, k1_zfmisc_1(k1_zfmisc_1(A_81))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_243])).
% 2.14/1.28  tff(c_260, plain, (![A_81]: (r2_hidden('#skF_1'(A_81, k1_xboole_0, k1_xboole_0), k1_xboole_0) | k7_setfam_1(A_81, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22, c_252])).
% 2.14/1.28  tff(c_279, plain, (![A_86]: (k7_setfam_1(A_86, k1_xboole_0)=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_141, c_260])).
% 2.14/1.28  tff(c_42, plain, (k7_setfam_1('#skF_2', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.28  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.14/1.28  tff(c_156, plain, (![A_57, B_58]: (k7_setfam_1(A_57, k7_setfam_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(k1_zfmisc_1(A_57))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.14/1.28  tff(c_158, plain, (k7_setfam_1('#skF_2', k7_setfam_1('#skF_2', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_46, c_156])).
% 2.14/1.28  tff(c_163, plain, (k7_setfam_1('#skF_2', k1_xboole_0)='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_158])).
% 2.14/1.28  tff(c_285, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_279, c_163])).
% 2.14/1.28  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_285])).
% 2.14/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.28  
% 2.14/1.28  Inference rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Ref     : 0
% 2.14/1.28  #Sup     : 55
% 2.14/1.28  #Fact    : 0
% 2.14/1.28  #Define  : 0
% 2.14/1.28  #Split   : 0
% 2.14/1.28  #Chain   : 0
% 2.14/1.28  #Close   : 0
% 2.14/1.28  
% 2.14/1.28  Ordering : KBO
% 2.14/1.28  
% 2.14/1.28  Simplification rules
% 2.14/1.28  ----------------------
% 2.14/1.28  #Subsume      : 9
% 2.14/1.28  #Demod        : 20
% 2.14/1.28  #Tautology    : 30
% 2.14/1.28  #SimpNegUnit  : 6
% 2.14/1.28  #BackRed      : 3
% 2.14/1.28  
% 2.14/1.28  #Partial instantiations: 0
% 2.14/1.28  #Strategies tried      : 1
% 2.14/1.28  
% 2.14/1.28  Timing (in seconds)
% 2.14/1.28  ----------------------
% 2.14/1.28  Preprocessing        : 0.32
% 2.14/1.28  Parsing              : 0.16
% 2.14/1.28  CNF conversion       : 0.02
% 2.14/1.28  Main loop            : 0.21
% 2.14/1.28  Inferencing          : 0.08
% 2.14/1.28  Reduction            : 0.06
% 2.14/1.28  Demodulation         : 0.05
% 2.14/1.28  BG Simplification    : 0.02
% 2.14/1.28  Subsumption          : 0.04
% 2.14/1.28  Abstraction          : 0.01
% 2.14/1.28  MUC search           : 0.00
% 2.14/1.28  Cooper               : 0.00
% 2.14/1.28  Total                : 0.56
% 2.14/1.28  Index Insertion      : 0.00
% 2.14/1.28  Index Deletion       : 0.00
% 2.14/1.28  Index Matching       : 0.00
% 2.14/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
