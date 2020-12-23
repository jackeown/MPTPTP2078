%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:53 EST 2020

% Result     : Theorem 11.83s
% Output     : CNFRefutation 11.89s
% Verified   : 
% Statistics : Number of formulae       :   59 (  73 expanded)
%              Number of leaves         :   31 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   62 (  90 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_63,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_224,plain,(
    ! [A_61,B_62] :
      ( k4_xboole_0(A_61,B_62) = k3_subset_1(A_61,B_62)
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_245,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_224])).

tff(c_48,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_131,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [C_17,A_13] :
      ( r1_tarski(C_17,A_13)
      | ~ r2_hidden(C_17,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_138,plain,(
    ! [B_55,A_13] :
      ( r1_tarski(B_55,A_13)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_13))
      | v1_xboole_0(k1_zfmisc_1(A_13)) ) ),
    inference(resolution,[status(thm)],[c_131,c_12])).

tff(c_158,plain,(
    ! [B_59,A_60] :
      ( r1_tarski(B_59,A_60)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_138])).

tff(c_178,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_158])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_178,c_8])).

tff(c_313,plain,(
    ! [A_65,B_66,C_67] : k4_xboole_0(k3_xboole_0(A_65,B_66),C_67) = k3_xboole_0(A_65,k4_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_460,plain,(
    ! [C_73] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_3',C_73)) = k4_xboole_0('#skF_4',C_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_313])).

tff(c_478,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_460])).

tff(c_38,plain,(
    ! [A_25,B_26] : k6_subset_1(A_25,B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    ! [A_22,B_23] : m1_subset_1(k6_subset_1(A_22,B_23),k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_49,plain,(
    ! [A_22,B_23] : m1_subset_1(k4_xboole_0(A_22,B_23),k1_zfmisc_1(A_22)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34])).

tff(c_877,plain,(
    ! [A_86,B_87,C_88] :
      ( k9_subset_1(A_86,B_87,C_88) = k3_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_11154,plain,(
    ! [A_199,B_200,B_201] : k9_subset_1(A_199,B_200,k4_xboole_0(A_199,B_201)) = k3_xboole_0(B_200,k4_xboole_0(A_199,B_201)) ),
    inference(resolution,[status(thm)],[c_49,c_877])).

tff(c_11190,plain,(
    ! [B_200] : k9_subset_1('#skF_3',B_200,k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0(B_200,k4_xboole_0('#skF_3','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_11154])).

tff(c_11205,plain,(
    ! [B_200] : k9_subset_1('#skF_3',B_200,k3_subset_1('#skF_3','#skF_5')) = k3_xboole_0(B_200,k3_subset_1('#skF_3','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_11190])).

tff(c_753,plain,(
    ! [A_81,B_82,C_83] :
      ( k7_subset_1(A_81,B_82,C_83) = k4_xboole_0(B_82,C_83)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_774,plain,(
    ! [C_83] : k7_subset_1('#skF_3','#skF_4',C_83) = k4_xboole_0('#skF_4',C_83) ),
    inference(resolution,[status(thm)],[c_48,c_753])).

tff(c_44,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k7_subset_1('#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_776,plain,(
    k9_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_44])).

tff(c_18192,plain,(
    k3_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_5')) != k4_xboole_0('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11205,c_776])).

tff(c_18195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_18192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:02:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.83/4.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.83/4.99  
% 11.83/4.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.83/4.99  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 11.83/4.99  
% 11.83/4.99  %Foreground sorts:
% 11.83/4.99  
% 11.83/4.99  
% 11.83/4.99  %Background operators:
% 11.83/4.99  
% 11.83/4.99  
% 11.83/4.99  %Foreground operators:
% 11.83/4.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.83/4.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.83/4.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.83/4.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.83/4.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.83/4.99  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 11.83/4.99  tff('#skF_5', type, '#skF_5': $i).
% 11.83/4.99  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 11.83/4.99  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 11.83/4.99  tff('#skF_3', type, '#skF_3': $i).
% 11.83/4.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 11.83/4.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.83/4.99  tff('#skF_4', type, '#skF_4': $i).
% 11.83/4.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.83/4.99  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 11.83/4.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.83/4.99  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.83/4.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 11.83/4.99  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 11.83/4.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 11.83/4.99  
% 11.89/5.00  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 11.89/5.00  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 11.89/5.00  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 11.89/5.00  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 11.89/5.00  tff(f_44, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 11.89/5.00  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 11.89/5.00  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_xboole_1)).
% 11.89/5.00  tff(f_68, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 11.89/5.00  tff(f_63, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 11.89/5.00  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 11.89/5.00  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 11.89/5.00  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.89/5.00  tff(c_224, plain, (![A_61, B_62]: (k4_xboole_0(A_61, B_62)=k3_subset_1(A_61, B_62) | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.89/5.00  tff(c_245, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_46, c_224])).
% 11.89/5.00  tff(c_48, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.89/5.00  tff(c_36, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 11.89/5.00  tff(c_131, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.89/5.00  tff(c_12, plain, (![C_17, A_13]: (r1_tarski(C_17, A_13) | ~r2_hidden(C_17, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 11.89/5.00  tff(c_138, plain, (![B_55, A_13]: (r1_tarski(B_55, A_13) | ~m1_subset_1(B_55, k1_zfmisc_1(A_13)) | v1_xboole_0(k1_zfmisc_1(A_13)))), inference(resolution, [status(thm)], [c_131, c_12])).
% 11.89/5.00  tff(c_158, plain, (![B_59, A_60]: (r1_tarski(B_59, A_60) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)))), inference(negUnitSimplification, [status(thm)], [c_36, c_138])).
% 11.89/5.00  tff(c_178, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_158])).
% 11.89/5.00  tff(c_8, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 11.89/5.00  tff(c_183, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_178, c_8])).
% 11.89/5.00  tff(c_313, plain, (![A_65, B_66, C_67]: (k4_xboole_0(k3_xboole_0(A_65, B_66), C_67)=k3_xboole_0(A_65, k4_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 11.89/5.00  tff(c_460, plain, (![C_73]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_3', C_73))=k4_xboole_0('#skF_4', C_73))), inference(superposition, [status(thm), theory('equality')], [c_183, c_313])).
% 11.89/5.00  tff(c_478, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_245, c_460])).
% 11.89/5.00  tff(c_38, plain, (![A_25, B_26]: (k6_subset_1(A_25, B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_68])).
% 11.89/5.00  tff(c_34, plain, (![A_22, B_23]: (m1_subset_1(k6_subset_1(A_22, B_23), k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 11.89/5.00  tff(c_49, plain, (![A_22, B_23]: (m1_subset_1(k4_xboole_0(A_22, B_23), k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34])).
% 11.89/5.00  tff(c_877, plain, (![A_86, B_87, C_88]: (k9_subset_1(A_86, B_87, C_88)=k3_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 11.89/5.00  tff(c_11154, plain, (![A_199, B_200, B_201]: (k9_subset_1(A_199, B_200, k4_xboole_0(A_199, B_201))=k3_xboole_0(B_200, k4_xboole_0(A_199, B_201)))), inference(resolution, [status(thm)], [c_49, c_877])).
% 11.89/5.00  tff(c_11190, plain, (![B_200]: (k9_subset_1('#skF_3', B_200, k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0(B_200, k4_xboole_0('#skF_3', '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_245, c_11154])).
% 11.89/5.00  tff(c_11205, plain, (![B_200]: (k9_subset_1('#skF_3', B_200, k3_subset_1('#skF_3', '#skF_5'))=k3_xboole_0(B_200, k3_subset_1('#skF_3', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_245, c_11190])).
% 11.89/5.00  tff(c_753, plain, (![A_81, B_82, C_83]: (k7_subset_1(A_81, B_82, C_83)=k4_xboole_0(B_82, C_83) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 11.89/5.00  tff(c_774, plain, (![C_83]: (k7_subset_1('#skF_3', '#skF_4', C_83)=k4_xboole_0('#skF_4', C_83))), inference(resolution, [status(thm)], [c_48, c_753])).
% 11.89/5.00  tff(c_44, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k7_subset_1('#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_84])).
% 11.89/5.00  tff(c_776, plain, (k9_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_774, c_44])).
% 11.89/5.00  tff(c_18192, plain, (k3_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_5'))!=k4_xboole_0('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_11205, c_776])).
% 11.89/5.00  tff(c_18195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_478, c_18192])).
% 11.89/5.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.89/5.00  
% 11.89/5.00  Inference rules
% 11.89/5.00  ----------------------
% 11.89/5.00  #Ref     : 0
% 11.89/5.00  #Sup     : 4572
% 11.89/5.00  #Fact    : 0
% 11.89/5.00  #Define  : 0
% 11.89/5.00  #Split   : 0
% 11.89/5.00  #Chain   : 0
% 11.89/5.00  #Close   : 0
% 11.89/5.00  
% 11.89/5.00  Ordering : KBO
% 11.89/5.00  
% 11.89/5.00  Simplification rules
% 11.89/5.00  ----------------------
% 11.89/5.00  #Subsume      : 373
% 11.89/5.00  #Demod        : 3908
% 11.89/5.00  #Tautology    : 1295
% 11.89/5.00  #SimpNegUnit  : 9
% 11.89/5.00  #BackRed      : 15
% 11.89/5.00  
% 11.89/5.00  #Partial instantiations: 0
% 11.89/5.00  #Strategies tried      : 1
% 11.89/5.00  
% 11.89/5.00  Timing (in seconds)
% 11.89/5.00  ----------------------
% 11.89/5.00  Preprocessing        : 0.32
% 11.89/5.00  Parsing              : 0.17
% 11.89/5.00  CNF conversion       : 0.02
% 11.89/5.00  Main loop            : 3.92
% 11.89/5.00  Inferencing          : 0.63
% 11.89/5.01  Reduction            : 2.51
% 11.89/5.01  Demodulation         : 2.30
% 11.89/5.01  BG Simplification    : 0.10
% 11.89/5.01  Subsumption          : 0.53
% 11.89/5.01  Abstraction          : 0.14
% 11.89/5.01  MUC search           : 0.00
% 11.89/5.01  Cooper               : 0.00
% 11.89/5.01  Total                : 4.28
% 11.89/5.01  Index Insertion      : 0.00
% 11.89/5.01  Index Deletion       : 0.00
% 11.89/5.01  Index Matching       : 0.00
% 11.89/5.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
