%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:31 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.96s
% Verified   : 
% Statistics : Number of formulae       :   59 (  81 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 132 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,k4_subset_1(A,B,C)),k3_subset_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

tff(f_64,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [B_38,A_39] :
      ( r2_hidden(B_38,A_39)
      | ~ m1_subset_1(B_38,A_39)
      | v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_76,plain,(
    ! [B_38,A_9] :
      ( r1_tarski(B_38,A_9)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_72,c_8])).

tff(c_80,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(B_40,A_41)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_76])).

tff(c_92,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_80])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_93,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_80])).

tff(c_220,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_tarski(k2_xboole_0(A_57,C_58),B_59)
      | ~ r1_tarski(C_58,B_59)
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94,plain,(
    ! [B_42,A_43] :
      ( m1_subset_1(B_42,A_43)
      | ~ r2_hidden(B_42,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_100,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_10,c_94])).

tff(c_104,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_100])).

tff(c_144,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k3_subset_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_158,plain,(
    ! [A_9,C_13] :
      ( k4_xboole_0(A_9,C_13) = k3_subset_1(A_9,C_13)
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_104,c_144])).

tff(c_3103,plain,(
    ! [B_156,A_157,C_158] :
      ( k4_xboole_0(B_156,k2_xboole_0(A_157,C_158)) = k3_subset_1(B_156,k2_xboole_0(A_157,C_158))
      | ~ r1_tarski(C_158,B_156)
      | ~ r1_tarski(A_157,B_156) ) ),
    inference(resolution,[status(thm)],[c_220,c_158])).

tff(c_161,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_144])).

tff(c_105,plain,(
    ! [A_44,B_45,C_46] : k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_114,plain,(
    ! [A_44,B_45,C_46] : r1_tarski(k4_xboole_0(A_44,k2_xboole_0(B_45,C_46)),k4_xboole_0(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_178,plain,(
    ! [C_46] : r1_tarski(k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_46)),k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_114])).

tff(c_3235,plain,(
    ! [C_158] :
      ( r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4',C_158)),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski(C_158,'#skF_3')
      | ~ r1_tarski('#skF_4','#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3103,c_178])).

tff(c_3306,plain,(
    ! [C_159] :
      ( r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4',C_159)),k3_subset_1('#skF_3','#skF_4'))
      | ~ r1_tarski(C_159,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_3235])).

tff(c_588,plain,(
    ! [A_84,B_85,C_86] :
      ( k4_subset_1(A_84,B_85,C_86) = k2_xboole_0(B_85,C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_602,plain,(
    ! [B_87] :
      ( k4_subset_1('#skF_3',B_87,'#skF_5') = k2_xboole_0(B_87,'#skF_5')
      | ~ m1_subset_1(B_87,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_38,c_588])).

tff(c_620,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_602])).

tff(c_36,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k4_subset_1('#skF_3','#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_625,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3',k2_xboole_0('#skF_4','#skF_5')),k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_36])).

tff(c_3311,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_3306,c_625])).

tff(c_3319,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_3311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.90  
% 4.63/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.91  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.63/1.91  
% 4.63/1.91  %Foreground sorts:
% 4.63/1.91  
% 4.63/1.91  
% 4.63/1.91  %Background operators:
% 4.63/1.91  
% 4.63/1.91  
% 4.63/1.91  %Foreground operators:
% 4.63/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.91  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.63/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.63/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.63/1.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.63/1.91  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.63/1.91  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.91  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.63/1.91  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.91  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.63/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.63/1.91  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.63/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.63/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.91  
% 4.96/1.92  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, k4_subset_1(A, B, C)), k3_subset_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_subset_1)).
% 4.96/1.92  tff(f_64, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.96/1.92  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.96/1.92  tff(f_42, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.96/1.92  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.96/1.92  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.96/1.92  tff(f_29, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 4.96/1.92  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.96/1.92  tff(f_70, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.96/1.92  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.96/1.92  tff(c_32, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.96/1.92  tff(c_72, plain, (![B_38, A_39]: (r2_hidden(B_38, A_39) | ~m1_subset_1(B_38, A_39) | v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.96/1.92  tff(c_8, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.96/1.92  tff(c_76, plain, (![B_38, A_9]: (r1_tarski(B_38, A_9) | ~m1_subset_1(B_38, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_72, c_8])).
% 4.96/1.92  tff(c_80, plain, (![B_40, A_41]: (r1_tarski(B_40, A_41) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)))), inference(negUnitSimplification, [status(thm)], [c_32, c_76])).
% 4.96/1.92  tff(c_92, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_80])).
% 4.96/1.92  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.96/1.92  tff(c_93, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_40, c_80])).
% 4.96/1.92  tff(c_220, plain, (![A_57, C_58, B_59]: (r1_tarski(k2_xboole_0(A_57, C_58), B_59) | ~r1_tarski(C_58, B_59) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.96/1.92  tff(c_10, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.96/1.92  tff(c_94, plain, (![B_42, A_43]: (m1_subset_1(B_42, A_43) | ~r2_hidden(B_42, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.96/1.92  tff(c_100, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_10, c_94])).
% 4.96/1.92  tff(c_104, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(negUnitSimplification, [status(thm)], [c_32, c_100])).
% 4.96/1.92  tff(c_144, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k3_subset_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.96/1.92  tff(c_158, plain, (![A_9, C_13]: (k4_xboole_0(A_9, C_13)=k3_subset_1(A_9, C_13) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_104, c_144])).
% 4.96/1.92  tff(c_3103, plain, (![B_156, A_157, C_158]: (k4_xboole_0(B_156, k2_xboole_0(A_157, C_158))=k3_subset_1(B_156, k2_xboole_0(A_157, C_158)) | ~r1_tarski(C_158, B_156) | ~r1_tarski(A_157, B_156))), inference(resolution, [status(thm)], [c_220, c_158])).
% 4.96/1.92  tff(c_161, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_144])).
% 4.96/1.92  tff(c_105, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.96/1.92  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.96/1.92  tff(c_114, plain, (![A_44, B_45, C_46]: (r1_tarski(k4_xboole_0(A_44, k2_xboole_0(B_45, C_46)), k4_xboole_0(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_105, c_2])).
% 4.96/1.92  tff(c_178, plain, (![C_46]: (r1_tarski(k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_46)), k3_subset_1('#skF_3', '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_161, c_114])).
% 4.96/1.92  tff(c_3235, plain, (![C_158]: (r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', C_158)), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski(C_158, '#skF_3') | ~r1_tarski('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_3103, c_178])).
% 4.96/1.92  tff(c_3306, plain, (![C_159]: (r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', C_159)), k3_subset_1('#skF_3', '#skF_4')) | ~r1_tarski(C_159, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_3235])).
% 4.96/1.92  tff(c_588, plain, (![A_84, B_85, C_86]: (k4_subset_1(A_84, B_85, C_86)=k2_xboole_0(B_85, C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(A_84)) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.96/1.92  tff(c_602, plain, (![B_87]: (k4_subset_1('#skF_3', B_87, '#skF_5')=k2_xboole_0(B_87, '#skF_5') | ~m1_subset_1(B_87, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_38, c_588])).
% 4.96/1.92  tff(c_620, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_602])).
% 4.96/1.92  tff(c_36, plain, (~r1_tarski(k3_subset_1('#skF_3', k4_subset_1('#skF_3', '#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.96/1.92  tff(c_625, plain, (~r1_tarski(k3_subset_1('#skF_3', k2_xboole_0('#skF_4', '#skF_5')), k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_620, c_36])).
% 4.96/1.92  tff(c_3311, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_3306, c_625])).
% 4.96/1.92  tff(c_3319, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_3311])).
% 4.96/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.96/1.92  
% 4.96/1.92  Inference rules
% 4.96/1.92  ----------------------
% 4.96/1.92  #Ref     : 0
% 4.96/1.92  #Sup     : 785
% 4.96/1.92  #Fact    : 0
% 4.96/1.92  #Define  : 0
% 4.96/1.92  #Split   : 0
% 4.96/1.92  #Chain   : 0
% 4.96/1.92  #Close   : 0
% 4.96/1.92  
% 4.96/1.92  Ordering : KBO
% 4.96/1.92  
% 4.96/1.92  Simplification rules
% 4.96/1.92  ----------------------
% 4.96/1.92  #Subsume      : 18
% 4.96/1.92  #Demod        : 505
% 4.96/1.92  #Tautology    : 241
% 4.96/1.92  #SimpNegUnit  : 18
% 4.96/1.92  #BackRed      : 1
% 4.96/1.92  
% 4.96/1.92  #Partial instantiations: 0
% 4.96/1.92  #Strategies tried      : 1
% 4.96/1.92  
% 4.96/1.92  Timing (in seconds)
% 4.96/1.92  ----------------------
% 4.96/1.92  Preprocessing        : 0.30
% 4.96/1.92  Parsing              : 0.15
% 4.96/1.92  CNF conversion       : 0.02
% 4.96/1.92  Main loop            : 0.85
% 4.96/1.92  Inferencing          : 0.26
% 4.96/1.92  Reduction            : 0.35
% 4.96/1.92  Demodulation         : 0.26
% 4.96/1.92  BG Simplification    : 0.04
% 4.96/1.92  Subsumption          : 0.14
% 4.96/1.92  Abstraction          : 0.06
% 4.96/1.92  MUC search           : 0.00
% 4.96/1.92  Cooper               : 0.00
% 4.96/1.92  Total                : 1.18
% 4.96/1.92  Index Insertion      : 0.00
% 4.96/1.92  Index Deletion       : 0.00
% 4.96/1.92  Index Matching       : 0.00
% 4.96/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
