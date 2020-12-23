%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:41 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   72 (  84 expanded)
%              Number of leaves         :   35 (  43 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 (  86 expanded)
%              Number of equality atoms :   38 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_56,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_58,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_48,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_54,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_28,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_30,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30])).

tff(c_826,plain,(
    ! [A_87,B_88,C_89] :
      ( k4_subset_1(A_87,B_88,C_89) = k2_xboole_0(B_88,C_89)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(A_87))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1406,plain,(
    ! [A_104,B_105] :
      ( k4_subset_1(A_104,B_105,A_104) = k2_xboole_0(B_105,A_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(resolution,[status(thm)],[c_39,c_826])).

tff(c_1413,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') = k2_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1406])).

tff(c_36,plain,(
    k4_subset_1('#skF_2','#skF_3',k2_subset_1('#skF_2')) != k2_subset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    k4_subset_1('#skF_2','#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_36])).

tff(c_1423,plain,(
    k2_xboole_0('#skF_3','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1413,c_40])).

tff(c_20,plain,(
    ! [B_18,A_17] : k2_tarski(B_18,A_17) = k2_tarski(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_120,plain,(
    ! [A_46,B_47] : k3_tarski(k2_tarski(A_46,B_47)) = k2_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_144,plain,(
    ! [B_50,A_51] : k3_tarski(k2_tarski(B_50,A_51)) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_120])).

tff(c_26,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_150,plain,(
    ! [B_50,A_51] : k2_xboole_0(B_50,A_51) = k2_xboole_0(A_51,B_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_26])).

tff(c_12,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_76,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,A_6) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_389,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_398,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k4_xboole_0(A_6,A_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_389])).

tff(c_401,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_398])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_819,plain,(
    ! [C_84,A_85,B_86] :
      ( r2_hidden(C_84,A_85)
      | ~ r2_hidden(C_84,B_86)
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1704,plain,(
    ! [A_111,B_112,A_113] :
      ( r2_hidden('#skF_1'(A_111,B_112),A_113)
      | ~ m1_subset_1(A_111,k1_zfmisc_1(A_113))
      | r1_tarski(A_111,B_112) ) ),
    inference(resolution,[status(thm)],[c_6,c_819])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1716,plain,(
    ! [A_114,A_115] :
      ( ~ m1_subset_1(A_114,k1_zfmisc_1(A_115))
      | r1_tarski(A_114,A_115) ) ),
    inference(resolution,[status(thm)],[c_1704,c_4])).

tff(c_1725,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_1716])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1729,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1725,c_14])).

tff(c_10,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = k4_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1733,plain,(
    k5_xboole_0('#skF_3','#skF_3') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1729,c_10])).

tff(c_1736,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_1733])).

tff(c_16,plain,(
    ! [A_13,B_14] : k2_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1750,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k2_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1736,c_16])).

tff(c_1756,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_12,c_1750])).

tff(c_1758,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1423,c_1756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:19:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.57  
% 3.44/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.57  %$ r2_hidden > r1_tarski > m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.44/1.57  
% 3.44/1.57  %Foreground sorts:
% 3.44/1.57  
% 3.44/1.57  
% 3.44/1.57  %Background operators:
% 3.44/1.57  
% 3.44/1.57  
% 3.44/1.57  %Foreground operators:
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.44/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.44/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.57  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.44/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.44/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.44/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.44/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.44/1.57  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.44/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.44/1.57  
% 3.44/1.59  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 3.44/1.59  tff(f_56, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.44/1.59  tff(f_58, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.44/1.59  tff(f_71, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.44/1.59  tff(f_48, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.44/1.59  tff(f_54, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.44/1.59  tff(f_38, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.44/1.59  tff(f_46, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.44/1.59  tff(f_34, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.44/1.59  tff(f_36, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.44/1.59  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.44/1.59  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.44/1.59  tff(f_42, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.44/1.59  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.44/1.59  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.59  tff(c_28, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.44/1.59  tff(c_30, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.44/1.59  tff(c_39, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30])).
% 3.44/1.59  tff(c_826, plain, (![A_87, B_88, C_89]: (k4_subset_1(A_87, B_88, C_89)=k2_xboole_0(B_88, C_89) | ~m1_subset_1(C_89, k1_zfmisc_1(A_87)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.44/1.59  tff(c_1406, plain, (![A_104, B_105]: (k4_subset_1(A_104, B_105, A_104)=k2_xboole_0(B_105, A_104) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(resolution, [status(thm)], [c_39, c_826])).
% 3.44/1.59  tff(c_1413, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')=k2_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1406])).
% 3.44/1.59  tff(c_36, plain, (k4_subset_1('#skF_2', '#skF_3', k2_subset_1('#skF_2'))!=k2_subset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.44/1.59  tff(c_40, plain, (k4_subset_1('#skF_2', '#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_36])).
% 3.44/1.59  tff(c_1423, plain, (k2_xboole_0('#skF_3', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1413, c_40])).
% 3.44/1.59  tff(c_20, plain, (![B_18, A_17]: (k2_tarski(B_18, A_17)=k2_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.44/1.59  tff(c_120, plain, (![A_46, B_47]: (k3_tarski(k2_tarski(A_46, B_47))=k2_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.59  tff(c_144, plain, (![B_50, A_51]: (k3_tarski(k2_tarski(B_50, A_51))=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_20, c_120])).
% 3.44/1.59  tff(c_26, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.44/1.59  tff(c_150, plain, (![B_50, A_51]: (k2_xboole_0(B_50, A_51)=k2_xboole_0(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_144, c_26])).
% 3.44/1.59  tff(c_12, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.44/1.59  tff(c_69, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.44/1.59  tff(c_76, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_69])).
% 3.44/1.59  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, A_6)=A_6)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.44/1.59  tff(c_389, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.59  tff(c_398, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k4_xboole_0(A_6, A_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_389])).
% 3.44/1.59  tff(c_401, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_398])).
% 3.44/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.59  tff(c_819, plain, (![C_84, A_85, B_86]: (r2_hidden(C_84, A_85) | ~r2_hidden(C_84, B_86) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.44/1.59  tff(c_1704, plain, (![A_111, B_112, A_113]: (r2_hidden('#skF_1'(A_111, B_112), A_113) | ~m1_subset_1(A_111, k1_zfmisc_1(A_113)) | r1_tarski(A_111, B_112))), inference(resolution, [status(thm)], [c_6, c_819])).
% 3.44/1.59  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.44/1.59  tff(c_1716, plain, (![A_114, A_115]: (~m1_subset_1(A_114, k1_zfmisc_1(A_115)) | r1_tarski(A_114, A_115))), inference(resolution, [status(thm)], [c_1704, c_4])).
% 3.44/1.59  tff(c_1725, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_1716])).
% 3.44/1.59  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.44/1.59  tff(c_1729, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_1725, c_14])).
% 3.44/1.59  tff(c_10, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k3_xboole_0(A_8, B_9))=k4_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.44/1.59  tff(c_1733, plain, (k5_xboole_0('#skF_3', '#skF_3')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1729, c_10])).
% 3.44/1.59  tff(c_1736, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_401, c_1733])).
% 3.44/1.59  tff(c_16, plain, (![A_13, B_14]: (k2_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.44/1.59  tff(c_1750, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k2_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1736, c_16])).
% 3.44/1.59  tff(c_1756, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_12, c_1750])).
% 3.44/1.59  tff(c_1758, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1423, c_1756])).
% 3.44/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.59  
% 3.44/1.59  Inference rules
% 3.44/1.59  ----------------------
% 3.44/1.59  #Ref     : 0
% 3.44/1.59  #Sup     : 424
% 3.44/1.59  #Fact    : 0
% 3.44/1.59  #Define  : 0
% 3.44/1.59  #Split   : 0
% 3.44/1.59  #Chain   : 0
% 3.44/1.59  #Close   : 0
% 3.44/1.59  
% 3.44/1.59  Ordering : KBO
% 3.44/1.59  
% 3.44/1.59  Simplification rules
% 3.44/1.59  ----------------------
% 3.44/1.59  #Subsume      : 15
% 3.44/1.59  #Demod        : 464
% 3.44/1.59  #Tautology    : 330
% 3.44/1.59  #SimpNegUnit  : 1
% 3.44/1.59  #BackRed      : 1
% 3.44/1.59  
% 3.44/1.59  #Partial instantiations: 0
% 3.44/1.59  #Strategies tried      : 1
% 3.44/1.59  
% 3.44/1.59  Timing (in seconds)
% 3.44/1.59  ----------------------
% 3.44/1.59  Preprocessing        : 0.32
% 3.44/1.59  Parsing              : 0.17
% 3.44/1.59  CNF conversion       : 0.02
% 3.44/1.59  Main loop            : 0.46
% 3.44/1.59  Inferencing          : 0.15
% 3.44/1.59  Reduction            : 0.20
% 3.44/1.59  Demodulation         : 0.17
% 3.44/1.59  BG Simplification    : 0.02
% 3.44/1.59  Subsumption          : 0.06
% 3.44/1.59  Abstraction          : 0.03
% 3.44/1.59  MUC search           : 0.00
% 3.44/1.59  Cooper               : 0.00
% 3.44/1.59  Total                : 0.80
% 3.44/1.59  Index Insertion      : 0.00
% 3.44/1.59  Index Deletion       : 0.00
% 3.44/1.59  Index Matching       : 0.00
% 3.44/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
