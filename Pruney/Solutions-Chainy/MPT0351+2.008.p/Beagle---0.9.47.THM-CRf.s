%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:37 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   76 (  85 expanded)
%              Number of leaves         :   41 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 (  97 expanded)
%              Number of equality atoms :   30 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_66,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_83,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_88,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_68,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(c_14,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_224,plain,(
    ! [A_91,B_92] : k3_tarski(k2_tarski(A_91,B_92)) = k2_xboole_0(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_239,plain,(
    ! [B_93,A_94] : k3_tarski(k2_tarski(B_93,A_94)) = k2_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_224])).

tff(c_46,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_245,plain,(
    ! [B_93,A_94] : k2_xboole_0(B_93,A_94) = k2_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_46])).

tff(c_68,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_58,plain,(
    ! [A_65] : k2_subset_1(A_65) = A_65 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_60,plain,(
    ! [A_66] : m1_subset_1(k2_subset_1(A_66),k1_zfmisc_1(A_66)) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_70,plain,(
    ! [A_66] : m1_subset_1(A_66,k1_zfmisc_1(A_66)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60])).

tff(c_747,plain,(
    ! [A_178,B_179,C_180] :
      ( k4_subset_1(A_178,B_179,C_180) = k2_xboole_0(B_179,C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(A_178))
      | ~ m1_subset_1(B_179,k1_zfmisc_1(A_178)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_779,plain,(
    ! [A_181,B_182] :
      ( k4_subset_1(A_181,B_182,A_181) = k2_xboole_0(B_182,A_181)
      | ~ m1_subset_1(B_182,k1_zfmisc_1(A_181)) ) ),
    inference(resolution,[status(thm)],[c_70,c_747])).

tff(c_797,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_779])).

tff(c_813,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') = k2_xboole_0('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_797])).

tff(c_66,plain,(
    k4_subset_1('#skF_6','#skF_7',k2_subset_1('#skF_6')) != k2_subset_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_69,plain,(
    k4_subset_1('#skF_6','#skF_7','#skF_6') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_58,c_66])).

tff(c_870,plain,(
    k2_xboole_0('#skF_6','#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_813,c_69])).

tff(c_62,plain,(
    ! [A_67] : ~ v1_xboole_0(k1_zfmisc_1(A_67)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_48,plain,(
    ! [A_62] : k3_tarski(k1_zfmisc_1(A_62)) = A_62 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    ! [B_64,A_63] :
      ( r2_hidden(B_64,A_63)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_364,plain,(
    ! [C_114,A_115,D_116] :
      ( r2_hidden(C_114,k3_tarski(A_115))
      | ~ r2_hidden(D_116,A_115)
      | ~ r2_hidden(C_114,D_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_539,plain,(
    ! [C_146,A_147,B_148] :
      ( r2_hidden(C_146,k3_tarski(A_147))
      | ~ r2_hidden(C_146,B_148)
      | ~ m1_subset_1(B_148,A_147)
      | v1_xboole_0(A_147) ) ),
    inference(resolution,[status(thm)],[c_52,c_364])).

tff(c_879,plain,(
    ! [A_185,B_186,A_187] :
      ( r2_hidden('#skF_1'(A_185,B_186),k3_tarski(A_187))
      | ~ m1_subset_1(A_185,A_187)
      | v1_xboole_0(A_187)
      | r1_tarski(A_185,B_186) ) ),
    inference(resolution,[status(thm)],[c_8,c_539])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_917,plain,(
    ! [A_194,A_195] :
      ( ~ m1_subset_1(A_194,A_195)
      | v1_xboole_0(A_195)
      | r1_tarski(A_194,k3_tarski(A_195)) ) ),
    inference(resolution,[status(thm)],[c_879,c_6])).

tff(c_939,plain,(
    ! [A_194,A_62] :
      ( ~ m1_subset_1(A_194,k1_zfmisc_1(A_62))
      | v1_xboole_0(k1_zfmisc_1(A_62))
      | r1_tarski(A_194,A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_917])).

tff(c_945,plain,(
    ! [A_196,A_197] :
      ( ~ m1_subset_1(A_196,k1_zfmisc_1(A_197))
      | r1_tarski(A_196,A_197) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_939])).

tff(c_984,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_68,c_945])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_992,plain,(
    k3_xboole_0('#skF_7','#skF_6') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_984,c_12])).

tff(c_133,plain,(
    ! [B_79,A_80] : k3_xboole_0(B_79,A_80) = k3_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_148,plain,(
    ! [A_80,B_79] : k2_xboole_0(A_80,k3_xboole_0(B_79,A_80)) = A_80 ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_10])).

tff(c_996,plain,(
    k2_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_992,c_148])).

tff(c_1015,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_870,c_996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.52  
% 3.09/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 3.09/1.53  
% 3.09/1.53  %Foreground sorts:
% 3.09/1.53  
% 3.09/1.53  
% 3.09/1.53  %Background operators:
% 3.09/1.53  
% 3.09/1.53  
% 3.09/1.53  %Foreground operators:
% 3.09/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.09/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.09/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.09/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.53  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.09/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.09/1.53  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.09/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.53  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.09/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.09/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.09/1.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.09/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.09/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.09/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.53  
% 3.24/1.54  tff(f_42, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.24/1.54  tff(f_66, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.24/1.54  tff(f_99, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.24/1.54  tff(f_83, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.24/1.54  tff(f_85, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.24/1.54  tff(f_94, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.24/1.54  tff(f_88, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.24/1.54  tff(f_68, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.24/1.54  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.24/1.54  tff(f_81, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.24/1.54  tff(f_64, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tarski)).
% 3.24/1.54  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.24/1.54  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.24/1.54  tff(f_36, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.24/1.54  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.24/1.54  tff(c_224, plain, (![A_91, B_92]: (k3_tarski(k2_tarski(A_91, B_92))=k2_xboole_0(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.54  tff(c_239, plain, (![B_93, A_94]: (k3_tarski(k2_tarski(B_93, A_94))=k2_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_14, c_224])).
% 3.24/1.54  tff(c_46, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.24/1.54  tff(c_245, plain, (![B_93, A_94]: (k2_xboole_0(B_93, A_94)=k2_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_239, c_46])).
% 3.24/1.54  tff(c_68, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.54  tff(c_58, plain, (![A_65]: (k2_subset_1(A_65)=A_65)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.24/1.54  tff(c_60, plain, (![A_66]: (m1_subset_1(k2_subset_1(A_66), k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.24/1.54  tff(c_70, plain, (![A_66]: (m1_subset_1(A_66, k1_zfmisc_1(A_66)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60])).
% 3.24/1.54  tff(c_747, plain, (![A_178, B_179, C_180]: (k4_subset_1(A_178, B_179, C_180)=k2_xboole_0(B_179, C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(A_178)) | ~m1_subset_1(B_179, k1_zfmisc_1(A_178)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.24/1.54  tff(c_779, plain, (![A_181, B_182]: (k4_subset_1(A_181, B_182, A_181)=k2_xboole_0(B_182, A_181) | ~m1_subset_1(B_182, k1_zfmisc_1(A_181)))), inference(resolution, [status(thm)], [c_70, c_747])).
% 3.24/1.54  tff(c_797, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_779])).
% 3.24/1.54  tff(c_813, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')=k2_xboole_0('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_797])).
% 3.24/1.54  tff(c_66, plain, (k4_subset_1('#skF_6', '#skF_7', k2_subset_1('#skF_6'))!=k2_subset_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.24/1.54  tff(c_69, plain, (k4_subset_1('#skF_6', '#skF_7', '#skF_6')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_58, c_66])).
% 3.24/1.54  tff(c_870, plain, (k2_xboole_0('#skF_6', '#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_813, c_69])).
% 3.24/1.54  tff(c_62, plain, (![A_67]: (~v1_xboole_0(k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.24/1.54  tff(c_48, plain, (![A_62]: (k3_tarski(k1_zfmisc_1(A_62))=A_62)), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.24/1.54  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.54  tff(c_52, plain, (![B_64, A_63]: (r2_hidden(B_64, A_63) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.24/1.54  tff(c_364, plain, (![C_114, A_115, D_116]: (r2_hidden(C_114, k3_tarski(A_115)) | ~r2_hidden(D_116, A_115) | ~r2_hidden(C_114, D_116))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.24/1.54  tff(c_539, plain, (![C_146, A_147, B_148]: (r2_hidden(C_146, k3_tarski(A_147)) | ~r2_hidden(C_146, B_148) | ~m1_subset_1(B_148, A_147) | v1_xboole_0(A_147))), inference(resolution, [status(thm)], [c_52, c_364])).
% 3.24/1.54  tff(c_879, plain, (![A_185, B_186, A_187]: (r2_hidden('#skF_1'(A_185, B_186), k3_tarski(A_187)) | ~m1_subset_1(A_185, A_187) | v1_xboole_0(A_187) | r1_tarski(A_185, B_186))), inference(resolution, [status(thm)], [c_8, c_539])).
% 3.24/1.54  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.24/1.54  tff(c_917, plain, (![A_194, A_195]: (~m1_subset_1(A_194, A_195) | v1_xboole_0(A_195) | r1_tarski(A_194, k3_tarski(A_195)))), inference(resolution, [status(thm)], [c_879, c_6])).
% 3.24/1.54  tff(c_939, plain, (![A_194, A_62]: (~m1_subset_1(A_194, k1_zfmisc_1(A_62)) | v1_xboole_0(k1_zfmisc_1(A_62)) | r1_tarski(A_194, A_62))), inference(superposition, [status(thm), theory('equality')], [c_48, c_917])).
% 3.24/1.54  tff(c_945, plain, (![A_196, A_197]: (~m1_subset_1(A_196, k1_zfmisc_1(A_197)) | r1_tarski(A_196, A_197))), inference(negUnitSimplification, [status(thm)], [c_62, c_939])).
% 3.24/1.54  tff(c_984, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_68, c_945])).
% 3.24/1.54  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.24/1.54  tff(c_992, plain, (k3_xboole_0('#skF_7', '#skF_6')='#skF_7'), inference(resolution, [status(thm)], [c_984, c_12])).
% 3.24/1.54  tff(c_133, plain, (![B_79, A_80]: (k3_xboole_0(B_79, A_80)=k3_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.54  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.24/1.54  tff(c_148, plain, (![A_80, B_79]: (k2_xboole_0(A_80, k3_xboole_0(B_79, A_80))=A_80)), inference(superposition, [status(thm), theory('equality')], [c_133, c_10])).
% 3.24/1.54  tff(c_996, plain, (k2_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_992, c_148])).
% 3.24/1.54  tff(c_1015, plain, $false, inference(negUnitSimplification, [status(thm)], [c_870, c_996])).
% 3.24/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.54  
% 3.24/1.54  Inference rules
% 3.24/1.54  ----------------------
% 3.24/1.54  #Ref     : 0
% 3.24/1.54  #Sup     : 224
% 3.24/1.54  #Fact    : 0
% 3.24/1.54  #Define  : 0
% 3.24/1.54  #Split   : 1
% 3.24/1.54  #Chain   : 0
% 3.24/1.54  #Close   : 0
% 3.24/1.54  
% 3.24/1.54  Ordering : KBO
% 3.24/1.54  
% 3.24/1.54  Simplification rules
% 3.24/1.54  ----------------------
% 3.24/1.54  #Subsume      : 15
% 3.24/1.54  #Demod        : 54
% 3.24/1.54  #Tautology    : 81
% 3.24/1.54  #SimpNegUnit  : 20
% 3.24/1.54  #BackRed      : 1
% 3.24/1.54  
% 3.24/1.54  #Partial instantiations: 0
% 3.24/1.54  #Strategies tried      : 1
% 3.24/1.54  
% 3.24/1.54  Timing (in seconds)
% 3.24/1.54  ----------------------
% 3.24/1.54  Preprocessing        : 0.34
% 3.24/1.54  Parsing              : 0.18
% 3.24/1.54  CNF conversion       : 0.02
% 3.24/1.54  Main loop            : 0.39
% 3.24/1.54  Inferencing          : 0.13
% 3.24/1.54  Reduction            : 0.13
% 3.24/1.54  Demodulation         : 0.10
% 3.24/1.54  BG Simplification    : 0.02
% 3.24/1.54  Subsumption          : 0.08
% 3.24/1.54  Abstraction          : 0.02
% 3.24/1.54  MUC search           : 0.00
% 3.24/1.54  Cooper               : 0.00
% 3.24/1.54  Total                : 0.76
% 3.24/1.55  Index Insertion      : 0.00
% 3.24/1.55  Index Deletion       : 0.00
% 3.24/1.55  Index Matching       : 0.00
% 3.24/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
