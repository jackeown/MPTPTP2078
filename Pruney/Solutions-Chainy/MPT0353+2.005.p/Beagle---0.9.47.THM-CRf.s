%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:53 EST 2020

% Result     : Theorem 30.78s
% Output     : CNFRefutation 30.78s
% Verified   : 
% Statistics : Number of formulae       :   61 (  75 expanded)
%              Number of leaves         :   33 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  90 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_79,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_46,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_81,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_76,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_689,plain,(
    ! [A_97,B_98] :
      ( k4_xboole_0(A_97,B_98) = k3_subset_1(A_97,B_98)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_727,plain,(
    k4_xboole_0('#skF_5','#skF_7') = k3_subset_1('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_68,c_689])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_58,plain,(
    ! [A_34] : ~ v1_xboole_0(k1_zfmisc_1(A_34)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_148,plain,(
    ! [B_64,A_65] :
      ( r2_hidden(B_64,A_65)
      | ~ m1_subset_1(B_64,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_32,plain,(
    ! [C_25,A_21] :
      ( r1_tarski(C_25,A_21)
      | ~ r2_hidden(C_25,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [B_64,A_21] :
      ( r1_tarski(B_64,A_21)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_21))
      | v1_xboole_0(k1_zfmisc_1(A_21)) ) ),
    inference(resolution,[status(thm)],[c_148,c_32])).

tff(c_161,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_156])).

tff(c_177,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_161])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_200,plain,(
    k3_xboole_0('#skF_6','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_177,c_24])).

tff(c_827,plain,(
    ! [A_99,B_100,C_101] : k4_xboole_0(k3_xboole_0(A_99,B_100),C_101) = k3_xboole_0(A_99,k4_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_914,plain,(
    ! [C_102] : k3_xboole_0('#skF_6',k4_xboole_0('#skF_5',C_102)) = k4_xboole_0('#skF_6',C_102) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_827])).

tff(c_959,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) = k4_xboole_0('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_914])).

tff(c_60,plain,(
    ! [A_35,B_36] : k6_subset_1(A_35,B_36) = k4_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    ! [A_32,B_33] : m1_subset_1(k6_subset_1(A_32,B_33),k1_zfmisc_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_71,plain,(
    ! [A_32,B_33] : m1_subset_1(k4_xboole_0(A_32,B_33),k1_zfmisc_1(A_32)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_56])).

tff(c_1288,plain,(
    ! [A_115,B_116,C_117] :
      ( k9_subset_1(A_115,B_116,C_117) = k3_xboole_0(B_116,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_10949,plain,(
    ! [A_269,B_270,B_271] : k9_subset_1(A_269,B_270,k4_xboole_0(A_269,B_271)) = k3_xboole_0(B_270,k4_xboole_0(A_269,B_271)) ),
    inference(resolution,[status(thm)],[c_71,c_1288])).

tff(c_11012,plain,(
    ! [B_270] : k9_subset_1('#skF_5',B_270,k3_subset_1('#skF_5','#skF_7')) = k3_xboole_0(B_270,k4_xboole_0('#skF_5','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_727,c_10949])).

tff(c_11039,plain,(
    ! [B_270] : k9_subset_1('#skF_5',B_270,k3_subset_1('#skF_5','#skF_7')) = k3_xboole_0(B_270,k3_subset_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_11012])).

tff(c_1038,plain,(
    ! [A_103,B_104,C_105] :
      ( k7_subset_1(A_103,B_104,C_105) = k4_xboole_0(B_104,C_105)
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1076,plain,(
    ! [C_105] : k7_subset_1('#skF_5','#skF_6',C_105) = k4_xboole_0('#skF_6',C_105) ),
    inference(resolution,[status(thm)],[c_70,c_1038])).

tff(c_66,plain,(
    k9_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_7')) != k7_subset_1('#skF_5','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1102,plain,(
    k9_subset_1('#skF_5','#skF_6',k3_subset_1('#skF_5','#skF_7')) != k4_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1076,c_66])).

tff(c_86700,plain,(
    k3_xboole_0('#skF_6',k3_subset_1('#skF_5','#skF_7')) != k4_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11039,c_1102])).

tff(c_86703,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_959,c_86700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:52:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.78/20.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.78/20.80  
% 30.78/20.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.78/20.80  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 30.78/20.80  
% 30.78/20.80  %Foreground sorts:
% 30.78/20.80  
% 30.78/20.80  
% 30.78/20.80  %Background operators:
% 30.78/20.80  
% 30.78/20.80  
% 30.78/20.80  %Foreground operators:
% 30.78/20.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 30.78/20.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.78/20.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.78/20.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 30.78/20.80  tff('#skF_7', type, '#skF_7': $i).
% 30.78/20.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 30.78/20.80  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 30.78/20.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.78/20.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 30.78/20.80  tff('#skF_5', type, '#skF_5': $i).
% 30.78/20.80  tff('#skF_6', type, '#skF_6': $i).
% 30.78/20.80  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 30.78/20.80  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 30.78/20.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.78/20.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 30.78/20.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.78/20.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.78/20.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 30.78/20.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 30.78/20.80  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 30.78/20.80  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 30.78/20.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.78/20.80  
% 30.78/20.82  tff(f_97, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 30.78/20.82  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 30.78/20.82  tff(f_79, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 30.78/20.82  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 30.78/20.82  tff(f_55, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 30.78/20.82  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 30.78/20.82  tff(f_46, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 30.78/20.82  tff(f_81, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 30.78/20.82  tff(f_76, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 30.78/20.82  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 30.78/20.82  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 30.78/20.82  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 30.78/20.82  tff(c_689, plain, (![A_97, B_98]: (k4_xboole_0(A_97, B_98)=k3_subset_1(A_97, B_98) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 30.78/20.82  tff(c_727, plain, (k4_xboole_0('#skF_5', '#skF_7')=k3_subset_1('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_68, c_689])).
% 30.78/20.82  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 30.78/20.82  tff(c_58, plain, (![A_34]: (~v1_xboole_0(k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 30.78/20.82  tff(c_148, plain, (![B_64, A_65]: (r2_hidden(B_64, A_65) | ~m1_subset_1(B_64, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_70])).
% 30.78/20.82  tff(c_32, plain, (![C_25, A_21]: (r1_tarski(C_25, A_21) | ~r2_hidden(C_25, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 30.78/20.82  tff(c_156, plain, (![B_64, A_21]: (r1_tarski(B_64, A_21) | ~m1_subset_1(B_64, k1_zfmisc_1(A_21)) | v1_xboole_0(k1_zfmisc_1(A_21)))), inference(resolution, [status(thm)], [c_148, c_32])).
% 30.78/20.82  tff(c_161, plain, (![B_66, A_67]: (r1_tarski(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)))), inference(negUnitSimplification, [status(thm)], [c_58, c_156])).
% 30.78/20.82  tff(c_177, plain, (r1_tarski('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_70, c_161])).
% 30.78/20.82  tff(c_24, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 30.78/20.82  tff(c_200, plain, (k3_xboole_0('#skF_6', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_177, c_24])).
% 30.78/20.82  tff(c_827, plain, (![A_99, B_100, C_101]: (k4_xboole_0(k3_xboole_0(A_99, B_100), C_101)=k3_xboole_0(A_99, k4_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 30.78/20.82  tff(c_914, plain, (![C_102]: (k3_xboole_0('#skF_6', k4_xboole_0('#skF_5', C_102))=k4_xboole_0('#skF_6', C_102))), inference(superposition, [status(thm), theory('equality')], [c_200, c_827])).
% 30.78/20.82  tff(c_959, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))=k4_xboole_0('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_727, c_914])).
% 30.78/20.82  tff(c_60, plain, (![A_35, B_36]: (k6_subset_1(A_35, B_36)=k4_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_81])).
% 30.78/20.82  tff(c_56, plain, (![A_32, B_33]: (m1_subset_1(k6_subset_1(A_32, B_33), k1_zfmisc_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 30.78/20.82  tff(c_71, plain, (![A_32, B_33]: (m1_subset_1(k4_xboole_0(A_32, B_33), k1_zfmisc_1(A_32)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_56])).
% 30.78/20.82  tff(c_1288, plain, (![A_115, B_116, C_117]: (k9_subset_1(A_115, B_116, C_117)=k3_xboole_0(B_116, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 30.78/20.82  tff(c_10949, plain, (![A_269, B_270, B_271]: (k9_subset_1(A_269, B_270, k4_xboole_0(A_269, B_271))=k3_xboole_0(B_270, k4_xboole_0(A_269, B_271)))), inference(resolution, [status(thm)], [c_71, c_1288])).
% 30.78/20.82  tff(c_11012, plain, (![B_270]: (k9_subset_1('#skF_5', B_270, k3_subset_1('#skF_5', '#skF_7'))=k3_xboole_0(B_270, k4_xboole_0('#skF_5', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_727, c_10949])).
% 30.78/20.82  tff(c_11039, plain, (![B_270]: (k9_subset_1('#skF_5', B_270, k3_subset_1('#skF_5', '#skF_7'))=k3_xboole_0(B_270, k3_subset_1('#skF_5', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_727, c_11012])).
% 30.78/20.82  tff(c_1038, plain, (![A_103, B_104, C_105]: (k7_subset_1(A_103, B_104, C_105)=k4_xboole_0(B_104, C_105) | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 30.78/20.82  tff(c_1076, plain, (![C_105]: (k7_subset_1('#skF_5', '#skF_6', C_105)=k4_xboole_0('#skF_6', C_105))), inference(resolution, [status(thm)], [c_70, c_1038])).
% 30.78/20.82  tff(c_66, plain, (k9_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_7'))!=k7_subset_1('#skF_5', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_97])).
% 30.78/20.82  tff(c_1102, plain, (k9_subset_1('#skF_5', '#skF_6', k3_subset_1('#skF_5', '#skF_7'))!=k4_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1076, c_66])).
% 30.78/20.82  tff(c_86700, plain, (k3_xboole_0('#skF_6', k3_subset_1('#skF_5', '#skF_7'))!=k4_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_11039, c_1102])).
% 30.78/20.82  tff(c_86703, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_959, c_86700])).
% 30.78/20.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.78/20.82  
% 30.78/20.82  Inference rules
% 30.78/20.82  ----------------------
% 30.78/20.82  #Ref     : 0
% 30.78/20.82  #Sup     : 21449
% 30.78/20.82  #Fact    : 0
% 30.78/20.82  #Define  : 0
% 30.78/20.82  #Split   : 3
% 30.78/20.82  #Chain   : 0
% 30.78/20.82  #Close   : 0
% 30.78/20.82  
% 30.78/20.82  Ordering : KBO
% 30.78/20.82  
% 30.78/20.82  Simplification rules
% 30.78/20.82  ----------------------
% 30.78/20.82  #Subsume      : 1576
% 30.78/20.82  #Demod        : 22453
% 30.78/20.82  #Tautology    : 9466
% 30.78/20.82  #SimpNegUnit  : 197
% 30.78/20.82  #BackRed      : 66
% 30.78/20.82  
% 30.78/20.82  #Partial instantiations: 0
% 30.78/20.82  #Strategies tried      : 1
% 30.78/20.82  
% 30.78/20.82  Timing (in seconds)
% 30.78/20.82  ----------------------
% 30.78/20.82  Preprocessing        : 0.33
% 30.78/20.82  Parsing              : 0.17
% 30.78/20.82  CNF conversion       : 0.02
% 30.78/20.82  Main loop            : 19.74
% 30.78/20.82  Inferencing          : 2.10
% 30.78/20.82  Reduction            : 12.13
% 30.78/20.82  Demodulation         : 11.08
% 30.78/20.82  BG Simplification    : 0.25
% 30.78/20.82  Subsumption          : 4.36
% 30.78/20.82  Abstraction          : 0.37
% 30.78/20.82  MUC search           : 0.00
% 30.78/20.82  Cooper               : 0.00
% 30.78/20.82  Total                : 20.10
% 30.78/20.82  Index Insertion      : 0.00
% 30.78/20.82  Index Deletion       : 0.00
% 30.78/20.82  Index Matching       : 0.00
% 30.78/20.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
