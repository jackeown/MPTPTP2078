%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:54 EST 2020

% Result     : Theorem 9.49s
% Output     : CNFRefutation 9.49s
% Verified   : 
% Statistics : Number of formulae       :   54 (  79 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   50 (  95 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_159,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k3_subset_1(A_40,B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_179,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_159])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_104,plain,(
    ! [A_35,B_36] :
      ( k3_subset_1(A_35,k3_subset_1(A_35,B_36)) = B_36
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_119,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_104])).

tff(c_180,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_159])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_14,B_15] : k6_subset_1(A_14,B_15) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_10,B_11] : m1_subset_1(k6_subset_1(A_10,B_11),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_25,plain,(
    ! [A_10,B_11] : m1_subset_1(k4_xboole_0(A_10,B_11),k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_10])).

tff(c_168,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_subset_1(A_10,k4_xboole_0(A_10,B_11)) ),
    inference(resolution,[status(thm)],[c_25,c_159])).

tff(c_286,plain,(
    ! [A_47,B_48] : k3_subset_1(A_47,k4_xboole_0(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_168])).

tff(c_301,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_286])).

tff(c_313,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_301])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_128,plain,(
    ! [A_37,B_38,C_39] : k4_xboole_0(k3_xboole_0(A_37,B_38),C_39) = k3_xboole_0(A_37,k4_xboole_0(B_38,C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_909,plain,(
    ! [A_70,B_71,C_72] : k4_xboole_0(k3_xboole_0(A_70,B_71),C_72) = k3_xboole_0(B_71,k4_xboole_0(A_70,C_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_1050,plain,(
    ! [C_74] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_1',C_74)) = k4_xboole_0('#skF_2',C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_909])).

tff(c_1089,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_1050])).

tff(c_315,plain,(
    ! [A_49,B_50,C_51] :
      ( k9_subset_1(A_49,B_50,C_51) = k3_xboole_0(B_50,C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2625,plain,(
    ! [A_97,B_98,B_99] : k9_subset_1(A_97,B_98,k4_xboole_0(A_97,B_99)) = k3_xboole_0(B_98,k4_xboole_0(A_97,B_99)) ),
    inference(resolution,[status(thm)],[c_25,c_315])).

tff(c_2685,plain,(
    ! [B_98] : k9_subset_1('#skF_1',B_98,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_98,k4_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_2625])).

tff(c_2711,plain,(
    ! [B_98] : k9_subset_1('#skF_1',B_98,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_98,k3_subset_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_2685])).

tff(c_181,plain,(
    ! [A_42,B_43,C_44] :
      ( k7_subset_1(A_42,B_43,C_44) = k4_xboole_0(B_43,C_44)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_198,plain,(
    ! [C_44] : k7_subset_1('#skF_1','#skF_2',C_44) = k4_xboole_0('#skF_2',C_44) ),
    inference(resolution,[status(thm)],[c_24,c_181])).

tff(c_20,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_276,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_198,c_20])).

tff(c_15024,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2711,c_276])).

tff(c_15027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_15024])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.49/3.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.43  
% 9.49/3.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.43  %$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 9.49/3.43  
% 9.49/3.43  %Foreground sorts:
% 9.49/3.43  
% 9.49/3.43  
% 9.49/3.43  %Background operators:
% 9.49/3.43  
% 9.49/3.43  
% 9.49/3.43  %Foreground operators:
% 9.49/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.49/3.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.49/3.43  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.49/3.43  tff('#skF_2', type, '#skF_2': $i).
% 9.49/3.43  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.49/3.43  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 9.49/3.43  tff('#skF_3', type, '#skF_3': $i).
% 9.49/3.43  tff('#skF_1', type, '#skF_1': $i).
% 9.49/3.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.49/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.49/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.49/3.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.49/3.43  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 9.49/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.49/3.43  
% 9.49/3.44  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 9.49/3.44  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.49/3.44  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.49/3.44  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.49/3.44  tff(f_43, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 9.49/3.44  tff(f_37, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 9.49/3.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.49/3.44  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 9.49/3.44  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 9.49/3.44  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.49/3.44  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.49/3.44  tff(c_159, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k3_subset_1(A_40, B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.49/3.44  tff(c_179, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_159])).
% 9.49/3.44  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.49/3.44  tff(c_104, plain, (![A_35, B_36]: (k3_subset_1(A_35, k3_subset_1(A_35, B_36))=B_36 | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.49/3.44  tff(c_119, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_24, c_104])).
% 9.49/3.44  tff(c_180, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_159])).
% 9.49/3.44  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.49/3.44  tff(c_14, plain, (![A_14, B_15]: (k6_subset_1(A_14, B_15)=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.49/3.44  tff(c_10, plain, (![A_10, B_11]: (m1_subset_1(k6_subset_1(A_10, B_11), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.49/3.44  tff(c_25, plain, (![A_10, B_11]: (m1_subset_1(k4_xboole_0(A_10, B_11), k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_10])).
% 9.49/3.44  tff(c_168, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_subset_1(A_10, k4_xboole_0(A_10, B_11)))), inference(resolution, [status(thm)], [c_25, c_159])).
% 9.49/3.44  tff(c_286, plain, (![A_47, B_48]: (k3_subset_1(A_47, k4_xboole_0(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_168])).
% 9.49/3.44  tff(c_301, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_180, c_286])).
% 9.49/3.44  tff(c_313, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_301])).
% 9.49/3.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.49/3.44  tff(c_128, plain, (![A_37, B_38, C_39]: (k4_xboole_0(k3_xboole_0(A_37, B_38), C_39)=k3_xboole_0(A_37, k4_xboole_0(B_38, C_39)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.49/3.44  tff(c_909, plain, (![A_70, B_71, C_72]: (k4_xboole_0(k3_xboole_0(A_70, B_71), C_72)=k3_xboole_0(B_71, k4_xboole_0(A_70, C_72)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_128])).
% 9.49/3.44  tff(c_1050, plain, (![C_74]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_1', C_74))=k4_xboole_0('#skF_2', C_74))), inference(superposition, [status(thm), theory('equality')], [c_313, c_909])).
% 9.49/3.44  tff(c_1089, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_179, c_1050])).
% 9.49/3.44  tff(c_315, plain, (![A_49, B_50, C_51]: (k9_subset_1(A_49, B_50, C_51)=k3_xboole_0(B_50, C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.49/3.44  tff(c_2625, plain, (![A_97, B_98, B_99]: (k9_subset_1(A_97, B_98, k4_xboole_0(A_97, B_99))=k3_xboole_0(B_98, k4_xboole_0(A_97, B_99)))), inference(resolution, [status(thm)], [c_25, c_315])).
% 9.49/3.44  tff(c_2685, plain, (![B_98]: (k9_subset_1('#skF_1', B_98, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_98, k4_xboole_0('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_179, c_2625])).
% 9.49/3.44  tff(c_2711, plain, (![B_98]: (k9_subset_1('#skF_1', B_98, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_98, k3_subset_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_2685])).
% 9.49/3.44  tff(c_181, plain, (![A_42, B_43, C_44]: (k7_subset_1(A_42, B_43, C_44)=k4_xboole_0(B_43, C_44) | ~m1_subset_1(B_43, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.49/3.44  tff(c_198, plain, (![C_44]: (k7_subset_1('#skF_1', '#skF_2', C_44)=k4_xboole_0('#skF_2', C_44))), inference(resolution, [status(thm)], [c_24, c_181])).
% 9.49/3.44  tff(c_20, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k7_subset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.49/3.44  tff(c_276, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_198, c_20])).
% 9.49/3.44  tff(c_15024, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2711, c_276])).
% 9.49/3.44  tff(c_15027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1089, c_15024])).
% 9.49/3.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.49/3.44  
% 9.49/3.44  Inference rules
% 9.49/3.44  ----------------------
% 9.49/3.44  #Ref     : 0
% 9.49/3.44  #Sup     : 3826
% 9.49/3.44  #Fact    : 0
% 9.49/3.44  #Define  : 0
% 9.49/3.44  #Split   : 0
% 9.49/3.44  #Chain   : 0
% 9.49/3.44  #Close   : 0
% 9.49/3.44  
% 9.49/3.44  Ordering : KBO
% 9.49/3.44  
% 9.49/3.44  Simplification rules
% 9.49/3.44  ----------------------
% 9.49/3.44  #Subsume      : 58
% 9.49/3.44  #Demod        : 3619
% 9.49/3.44  #Tautology    : 1976
% 9.49/3.44  #SimpNegUnit  : 0
% 9.49/3.44  #BackRed      : 4
% 9.49/3.44  
% 9.49/3.44  #Partial instantiations: 0
% 9.49/3.44  #Strategies tried      : 1
% 9.49/3.44  
% 9.49/3.44  Timing (in seconds)
% 9.49/3.44  ----------------------
% 9.58/3.44  Preprocessing        : 0.29
% 9.58/3.44  Parsing              : 0.16
% 9.58/3.44  CNF conversion       : 0.02
% 9.58/3.44  Main loop            : 2.34
% 9.58/3.44  Inferencing          : 0.46
% 9.58/3.44  Reduction            : 1.30
% 9.58/3.44  Demodulation         : 1.15
% 9.58/3.44  BG Simplification    : 0.06
% 9.58/3.44  Subsumption          : 0.39
% 9.58/3.44  Abstraction          : 0.09
% 9.58/3.44  MUC search           : 0.00
% 9.58/3.44  Cooper               : 0.00
% 9.58/3.44  Total                : 2.66
% 9.58/3.44  Index Insertion      : 0.00
% 9.58/3.44  Index Deletion       : 0.00
% 9.58/3.44  Index Matching       : 0.00
% 9.58/3.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
