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
% DateTime   : Thu Dec  3 09:56:32 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   60 (  72 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 104 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_62,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_56,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_77,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_6])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_32,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_180,plain,(
    ! [B_53,A_54] :
      ( r2_hidden(B_53,A_54)
      | ~ m1_subset_1(B_53,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [C_16,A_12] :
      ( r1_tarski(C_16,A_12)
      | ~ r2_hidden(C_16,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_187,plain,(
    ! [B_53,A_12] :
      ( r1_tarski(B_53,A_12)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12)) ) ),
    inference(resolution,[status(thm)],[c_180,c_12])).

tff(c_203,plain,(
    ! [B_58,A_59] :
      ( r1_tarski(B_58,A_59)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_59)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_187])).

tff(c_220,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_203])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_228,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_220,c_10])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [B_33,A_34] : k2_xboole_0(B_33,k3_xboole_0(A_34,B_33)) = B_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_8])).

tff(c_267,plain,(
    k2_xboole_0('#skF_3','#skF_5') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_74])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_417,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,'#skF_3')
      | ~ r1_tarski(A_67,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_4])).

tff(c_431,plain,(
    ! [B_33] : r1_tarski(k3_xboole_0(B_33,'#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_77,c_417])).

tff(c_14,plain,(
    ! [C_16,A_12] :
      ( r2_hidden(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_168,plain,(
    ! [B_49,A_50] :
      ( m1_subset_1(B_49,A_50)
      | ~ r2_hidden(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_171,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | v1_xboole_0(k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_168])).

tff(c_174,plain,(
    ! [C_16,A_12] :
      ( m1_subset_1(C_16,k1_zfmisc_1(A_12))
      | ~ r1_tarski(C_16,A_12) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_171])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1071,plain,(
    ! [A_104,C_105,B_106] :
      ( r1_tarski(k3_subset_1(A_104,C_105),k3_subset_1(A_104,B_106))
      | ~ r1_tarski(B_106,C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_250,plain,(
    ! [A_60,B_61,C_62] :
      ( k9_subset_1(A_60,B_61,C_62) = k3_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_263,plain,(
    ! [B_61] : k9_subset_1('#skF_3',B_61,'#skF_5') = k3_xboole_0(B_61,'#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_250])).

tff(c_40,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_366,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_263,c_40])).

tff(c_1074,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1071,c_366])).

tff(c_1080,plain,(
    ~ m1_subset_1(k3_xboole_0('#skF_4','#skF_5'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_6,c_1074])).

tff(c_1084,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_1080])).

tff(c_1091,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_1084])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n019.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 19:44:22 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.41  
% 2.87/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.87/1.42  
% 2.87/1.42  %Foreground sorts:
% 2.87/1.42  
% 2.87/1.42  
% 2.87/1.42  %Background operators:
% 2.87/1.42  
% 2.87/1.42  
% 2.87/1.42  %Foreground operators:
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.87/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.87/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.87/1.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.87/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.42  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 2.87/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.42  
% 2.87/1.43  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.87/1.43  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.87/1.43  tff(f_83, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 2.87/1.43  tff(f_62, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.87/1.43  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.87/1.43  tff(f_46, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.87/1.43  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.87/1.43  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.87/1.43  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.87/1.43  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 2.87/1.43  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.87/1.43  tff(c_56, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.87/1.43  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.87/1.43  tff(c_77, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_56, c_6])).
% 2.87/1.43  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.43  tff(c_32, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.87/1.43  tff(c_180, plain, (![B_53, A_54]: (r2_hidden(B_53, A_54) | ~m1_subset_1(B_53, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.43  tff(c_12, plain, (![C_16, A_12]: (r1_tarski(C_16, A_12) | ~r2_hidden(C_16, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.43  tff(c_187, plain, (![B_53, A_12]: (r1_tarski(B_53, A_12) | ~m1_subset_1(B_53, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)))), inference(resolution, [status(thm)], [c_180, c_12])).
% 2.87/1.43  tff(c_203, plain, (![B_58, A_59]: (r1_tarski(B_58, A_59) | ~m1_subset_1(B_58, k1_zfmisc_1(A_59)))), inference(negUnitSimplification, [status(thm)], [c_32, c_187])).
% 2.87/1.43  tff(c_220, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_203])).
% 2.87/1.43  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.87/1.43  tff(c_228, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_220, c_10])).
% 2.87/1.43  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.87/1.43  tff(c_74, plain, (![B_33, A_34]: (k2_xboole_0(B_33, k3_xboole_0(A_34, B_33))=B_33)), inference(superposition, [status(thm), theory('equality')], [c_56, c_8])).
% 2.87/1.43  tff(c_267, plain, (k2_xboole_0('#skF_3', '#skF_5')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_228, c_74])).
% 2.87/1.43  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.87/1.43  tff(c_417, plain, (![A_67]: (r1_tarski(A_67, '#skF_3') | ~r1_tarski(A_67, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_267, c_4])).
% 2.87/1.43  tff(c_431, plain, (![B_33]: (r1_tarski(k3_xboole_0(B_33, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_77, c_417])).
% 2.87/1.43  tff(c_14, plain, (![C_16, A_12]: (r2_hidden(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.43  tff(c_168, plain, (![B_49, A_50]: (m1_subset_1(B_49, A_50) | ~r2_hidden(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.87/1.43  tff(c_171, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | v1_xboole_0(k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(resolution, [status(thm)], [c_14, c_168])).
% 2.87/1.43  tff(c_174, plain, (![C_16, A_12]: (m1_subset_1(C_16, k1_zfmisc_1(A_12)) | ~r1_tarski(C_16, A_12))), inference(negUnitSimplification, [status(thm)], [c_32, c_171])).
% 2.87/1.43  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.43  tff(c_1071, plain, (![A_104, C_105, B_106]: (r1_tarski(k3_subset_1(A_104, C_105), k3_subset_1(A_104, B_106)) | ~r1_tarski(B_106, C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(A_104)) | ~m1_subset_1(B_106, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.87/1.43  tff(c_250, plain, (![A_60, B_61, C_62]: (k9_subset_1(A_60, B_61, C_62)=k3_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.87/1.43  tff(c_263, plain, (![B_61]: (k9_subset_1('#skF_3', B_61, '#skF_5')=k3_xboole_0(B_61, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_250])).
% 2.87/1.43  tff(c_40, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.87/1.43  tff(c_366, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_263, c_40])).
% 2.87/1.43  tff(c_1074, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3')) | ~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(resolution, [status(thm)], [c_1071, c_366])).
% 2.87/1.43  tff(c_1080, plain, (~m1_subset_1(k3_xboole_0('#skF_4', '#skF_5'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_6, c_1074])).
% 2.87/1.43  tff(c_1084, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_3')), inference(resolution, [status(thm)], [c_174, c_1080])).
% 2.87/1.43  tff(c_1091, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_431, c_1084])).
% 2.87/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.43  
% 2.87/1.43  Inference rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Ref     : 0
% 2.87/1.43  #Sup     : 258
% 2.87/1.43  #Fact    : 0
% 2.87/1.43  #Define  : 0
% 2.87/1.43  #Split   : 0
% 2.87/1.43  #Chain   : 0
% 2.87/1.43  #Close   : 0
% 2.87/1.43  
% 2.87/1.43  Ordering : KBO
% 2.87/1.43  
% 2.87/1.43  Simplification rules
% 2.87/1.43  ----------------------
% 2.87/1.43  #Subsume      : 6
% 2.87/1.43  #Demod        : 100
% 2.87/1.43  #Tautology    : 153
% 2.87/1.43  #SimpNegUnit  : 2
% 2.87/1.43  #BackRed      : 1
% 2.87/1.43  
% 2.87/1.43  #Partial instantiations: 0
% 2.87/1.43  #Strategies tried      : 1
% 2.87/1.43  
% 2.87/1.43  Timing (in seconds)
% 2.87/1.43  ----------------------
% 2.87/1.43  Preprocessing        : 0.31
% 2.87/1.43  Parsing              : 0.16
% 2.87/1.43  CNF conversion       : 0.02
% 2.87/1.43  Main loop            : 0.37
% 2.87/1.43  Inferencing          : 0.14
% 2.87/1.43  Reduction            : 0.13
% 2.87/1.43  Demodulation         : 0.10
% 2.87/1.43  BG Simplification    : 0.02
% 2.87/1.43  Subsumption          : 0.06
% 2.87/1.43  Abstraction          : 0.02
% 2.87/1.43  MUC search           : 0.00
% 2.87/1.43  Cooper               : 0.00
% 2.87/1.43  Total                : 0.71
% 2.87/1.43  Index Insertion      : 0.00
% 2.87/1.43  Index Deletion       : 0.00
% 2.87/1.43  Index Matching       : 0.00
% 2.87/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
