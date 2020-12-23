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
% DateTime   : Thu Dec  3 09:55:40 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   73 (  81 expanded)
%              Number of leaves         :   41 (  46 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 (  77 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_60,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_80,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_77,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_48,plain,(
    ! [A_47] : k2_subset_1(A_47) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_56,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_59,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_56])).

tff(c_12,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_175,plain,(
    ! [A_76,B_77] : k3_tarski(k2_tarski(A_76,B_77)) = k2_xboole_0(B_77,A_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_132])).

tff(c_38,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_181,plain,(
    ! [B_77,A_76] : k2_xboole_0(B_77,A_76) = k2_xboole_0(A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_38])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_52,plain,(
    ! [A_49] : ~ v1_xboole_0(k1_zfmisc_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_282,plain,(
    ! [B_81,A_82] :
      ( r2_hidden(B_81,A_82)
      | ~ m1_subset_1(B_81,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_26,plain,(
    ! [C_42,A_38] :
      ( r1_tarski(C_42,A_38)
      | ~ r2_hidden(C_42,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_286,plain,(
    ! [B_81,A_38] :
      ( r1_tarski(B_81,A_38)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_38))
      | v1_xboole_0(k1_zfmisc_1(A_38)) ) ),
    inference(resolution,[status(thm)],[c_282,c_26])).

tff(c_293,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(B_83,A_84)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_286])).

tff(c_306,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_293])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_334,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_306,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_351,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_2])).

tff(c_354,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_351])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_372,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_8])).

tff(c_375,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_4,c_372])).

tff(c_50,plain,(
    ! [A_48] : m1_subset_1(k2_subset_1(A_48),k1_zfmisc_1(A_48)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_60,plain,(
    ! [A_48] : m1_subset_1(A_48,k1_zfmisc_1(A_48)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_50])).

tff(c_523,plain,(
    ! [A_122,B_123,C_124] :
      ( k4_subset_1(A_122,B_123,C_124) = k2_xboole_0(B_123,C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(A_122))
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_537,plain,(
    ! [A_125,B_126] :
      ( k4_subset_1(A_125,B_126,A_125) = k2_xboole_0(B_126,A_125)
      | ~ m1_subset_1(B_126,k1_zfmisc_1(A_125)) ) ),
    inference(resolution,[status(thm)],[c_60,c_523])).

tff(c_546,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_537])).

tff(c_552,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_375,c_546])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_552])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:07:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.33  
% 2.61/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.33  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.61/1.33  
% 2.61/1.33  %Foreground sorts:
% 2.61/1.33  
% 2.61/1.33  
% 2.61/1.33  %Background operators:
% 2.61/1.33  
% 2.61/1.33  
% 2.61/1.33  %Foreground operators:
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.33  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.61/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.61/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.33  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.33  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.61/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.61/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.33  
% 2.61/1.35  tff(f_75, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.61/1.35  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.61/1.35  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.61/1.35  tff(f_60, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.61/1.35  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.61/1.35  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.61/1.35  tff(f_80, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.61/1.35  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.61/1.35  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.61/1.35  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.61/1.35  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.61/1.35  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.61/1.35  tff(f_77, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.61/1.35  tff(f_86, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.61/1.35  tff(c_48, plain, (![A_47]: (k2_subset_1(A_47)=A_47)), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.61/1.35  tff(c_56, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.61/1.35  tff(c_59, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_56])).
% 2.61/1.35  tff(c_12, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.35  tff(c_132, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.35  tff(c_175, plain, (![A_76, B_77]: (k3_tarski(k2_tarski(A_76, B_77))=k2_xboole_0(B_77, A_76))), inference(superposition, [status(thm), theory('equality')], [c_12, c_132])).
% 2.61/1.35  tff(c_38, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.61/1.35  tff(c_181, plain, (![B_77, A_76]: (k2_xboole_0(B_77, A_76)=k2_xboole_0(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_175, c_38])).
% 2.61/1.35  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.35  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.35  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.61/1.35  tff(c_52, plain, (![A_49]: (~v1_xboole_0(k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.61/1.35  tff(c_282, plain, (![B_81, A_82]: (r2_hidden(B_81, A_82) | ~m1_subset_1(B_81, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.61/1.35  tff(c_26, plain, (![C_42, A_38]: (r1_tarski(C_42, A_38) | ~r2_hidden(C_42, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.61/1.35  tff(c_286, plain, (![B_81, A_38]: (r1_tarski(B_81, A_38) | ~m1_subset_1(B_81, k1_zfmisc_1(A_38)) | v1_xboole_0(k1_zfmisc_1(A_38)))), inference(resolution, [status(thm)], [c_282, c_26])).
% 2.61/1.35  tff(c_293, plain, (![B_83, A_84]: (r1_tarski(B_83, A_84) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)))), inference(negUnitSimplification, [status(thm)], [c_52, c_286])).
% 2.61/1.35  tff(c_306, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_293])).
% 2.61/1.35  tff(c_6, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.35  tff(c_334, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_306, c_6])).
% 2.61/1.35  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.35  tff(c_351, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_334, c_2])).
% 2.61/1.35  tff(c_354, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_351])).
% 2.61/1.35  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.35  tff(c_372, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_354, c_8])).
% 2.61/1.35  tff(c_375, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_4, c_372])).
% 2.61/1.35  tff(c_50, plain, (![A_48]: (m1_subset_1(k2_subset_1(A_48), k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.61/1.35  tff(c_60, plain, (![A_48]: (m1_subset_1(A_48, k1_zfmisc_1(A_48)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_50])).
% 2.61/1.35  tff(c_523, plain, (![A_122, B_123, C_124]: (k4_subset_1(A_122, B_123, C_124)=k2_xboole_0(B_123, C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(A_122)) | ~m1_subset_1(B_123, k1_zfmisc_1(A_122)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.61/1.35  tff(c_537, plain, (![A_125, B_126]: (k4_subset_1(A_125, B_126, A_125)=k2_xboole_0(B_126, A_125) | ~m1_subset_1(B_126, k1_zfmisc_1(A_125)))), inference(resolution, [status(thm)], [c_60, c_523])).
% 2.61/1.35  tff(c_546, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_537])).
% 2.61/1.35  tff(c_552, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_375, c_546])).
% 2.61/1.35  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_552])).
% 2.61/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  Inference rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Ref     : 0
% 2.61/1.35  #Sup     : 114
% 2.61/1.35  #Fact    : 0
% 2.61/1.35  #Define  : 0
% 2.61/1.35  #Split   : 0
% 2.61/1.35  #Chain   : 0
% 2.61/1.35  #Close   : 0
% 2.61/1.35  
% 2.61/1.35  Ordering : KBO
% 2.61/1.35  
% 2.61/1.35  Simplification rules
% 2.61/1.35  ----------------------
% 2.61/1.35  #Subsume      : 7
% 2.61/1.35  #Demod        : 25
% 2.61/1.35  #Tautology    : 80
% 2.61/1.35  #SimpNegUnit  : 3
% 2.61/1.35  #BackRed      : 0
% 2.61/1.35  
% 2.61/1.35  #Partial instantiations: 0
% 2.61/1.35  #Strategies tried      : 1
% 2.61/1.35  
% 2.61/1.35  Timing (in seconds)
% 2.61/1.35  ----------------------
% 2.61/1.35  Preprocessing        : 0.34
% 2.61/1.35  Parsing              : 0.18
% 2.61/1.35  CNF conversion       : 0.02
% 2.61/1.35  Main loop            : 0.24
% 2.61/1.35  Inferencing          : 0.09
% 2.61/1.35  Reduction            : 0.08
% 2.61/1.35  Demodulation         : 0.06
% 2.61/1.35  BG Simplification    : 0.02
% 2.61/1.35  Subsumption          : 0.04
% 2.61/1.35  Abstraction          : 0.02
% 2.61/1.35  MUC search           : 0.00
% 2.61/1.35  Cooper               : 0.00
% 2.61/1.35  Total                : 0.61
% 2.61/1.35  Index Insertion      : 0.00
% 2.61/1.35  Index Deletion       : 0.00
% 2.61/1.35  Index Matching       : 0.00
% 2.61/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
