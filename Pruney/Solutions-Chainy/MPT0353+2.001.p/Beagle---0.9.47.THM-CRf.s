%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:52 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 (  94 expanded)
%              Number of equality atoms :   32 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k9_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_143,plain,(
    ! [A_52,B_53,C_54] :
      ( k9_subset_1(A_52,B_53,C_54) = k3_xboole_0(B_53,C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_149,plain,(
    ! [B_53] : k9_subset_1('#skF_2',B_53,'#skF_3') = k3_xboole_0(B_53,'#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_143])).

tff(c_581,plain,(
    ! [A_74,C_75,B_76] :
      ( k9_subset_1(A_74,C_75,B_76) = k9_subset_1(A_74,B_76,C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_585,plain,(
    ! [B_76] : k9_subset_1('#skF_2',B_76,'#skF_3') = k9_subset_1('#skF_2','#skF_3',B_76) ),
    inference(resolution,[status(thm)],[c_28,c_581])).

tff(c_589,plain,(
    ! [B_76] : k9_subset_1('#skF_2','#skF_3',B_76) = k3_xboole_0(B_76,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_585])).

tff(c_346,plain,(
    ! [A_63,B_64,C_65] :
      ( k7_subset_1(A_63,B_64,C_65) = k4_xboole_0(B_64,C_65)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_352,plain,(
    ! [C_65] : k7_subset_1('#skF_2','#skF_3',C_65) = k4_xboole_0('#skF_3',C_65) ),
    inference(resolution,[status(thm)],[c_28,c_346])).

tff(c_24,plain,(
    k9_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_4')) != k7_subset_1('#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_362,plain,(
    k9_subset_1('#skF_2','#skF_3',k3_subset_1('#skF_2','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_24])).

tff(c_619,plain,(
    k3_xboole_0(k3_subset_1('#skF_2','#skF_4'),'#skF_3') != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_362])).

tff(c_620,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) != k4_xboole_0('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_619])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_122,plain,(
    ! [C_47,A_48,B_49] :
      ( r2_hidden(C_47,A_48)
      | ~ r2_hidden(C_47,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_950,plain,(
    ! [A_85,B_86,A_87] :
      ( r2_hidden('#skF_1'(A_85,B_86),A_87)
      | ~ m1_subset_1(A_85,k1_zfmisc_1(A_87))
      | r1_tarski(A_85,B_86) ) ),
    inference(resolution,[status(thm)],[c_8,c_122])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_962,plain,(
    ! [A_88,A_89] :
      ( ~ m1_subset_1(A_88,k1_zfmisc_1(A_89))
      | r1_tarski(A_88,A_89) ) ),
    inference(resolution,[status(thm)],[c_950,c_6])).

tff(c_970,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_962])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_978,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_970,c_10])).

tff(c_88,plain,(
    ! [A_42,B_43,C_44] : k4_xboole_0(k3_xboole_0(A_42,B_43),C_44) = k3_xboole_0(A_42,k4_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_103,plain,(
    ! [A_1,B_2,C_44] : k4_xboole_0(k3_xboole_0(A_1,B_2),C_44) = k3_xboole_0(B_2,k4_xboole_0(A_1,C_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_1065,plain,(
    ! [C_92] : k3_xboole_0('#skF_2',k4_xboole_0('#skF_3',C_92)) = k4_xboole_0('#skF_3',C_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_978,c_103])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_126,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k3_subset_1(A_50,B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_133,plain,(
    k4_xboole_0('#skF_2','#skF_4') = k3_subset_1('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_126])).

tff(c_190,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(B_58,k4_xboole_0(A_57,C_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k4_xboole_0(k3_xboole_0(A_10,B_11),C_12) = k3_xboole_0(A_10,k4_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_231,plain,(
    ! [B_60,A_61,C_62] : k3_xboole_0(B_60,k4_xboole_0(A_61,C_62)) = k3_xboole_0(A_61,k4_xboole_0(B_60,C_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_12])).

tff(c_305,plain,(
    ! [A_61] : k3_xboole_0(A_61,k3_subset_1('#skF_2','#skF_4')) = k3_xboole_0('#skF_2',k4_xboole_0(A_61,'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_231])).

tff(c_1076,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_2','#skF_4')) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1065,c_305])).

tff(c_1110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_620,c_1076])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:11:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.02/1.47  
% 3.02/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_subset_1 > k7_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.15/1.47  
% 3.15/1.47  %Foreground sorts:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Background operators:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Foreground operators:
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.47  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.15/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.47  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.15/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.47  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.15/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.47  
% 3.15/1.48  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.48  tff(f_71, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 3.15/1.48  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.15/1.48  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k9_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k9_subset_1)).
% 3.15/1.48  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.15/1.48  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.15/1.48  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.15/1.48  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.15/1.48  tff(f_40, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.15/1.48  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.15/1.48  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.48  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.48  tff(c_143, plain, (![A_52, B_53, C_54]: (k9_subset_1(A_52, B_53, C_54)=k3_xboole_0(B_53, C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.48  tff(c_149, plain, (![B_53]: (k9_subset_1('#skF_2', B_53, '#skF_3')=k3_xboole_0(B_53, '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_143])).
% 3.15/1.48  tff(c_581, plain, (![A_74, C_75, B_76]: (k9_subset_1(A_74, C_75, B_76)=k9_subset_1(A_74, B_76, C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.15/1.48  tff(c_585, plain, (![B_76]: (k9_subset_1('#skF_2', B_76, '#skF_3')=k9_subset_1('#skF_2', '#skF_3', B_76))), inference(resolution, [status(thm)], [c_28, c_581])).
% 3.15/1.48  tff(c_589, plain, (![B_76]: (k9_subset_1('#skF_2', '#skF_3', B_76)=k3_xboole_0(B_76, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_149, c_585])).
% 3.15/1.48  tff(c_346, plain, (![A_63, B_64, C_65]: (k7_subset_1(A_63, B_64, C_65)=k4_xboole_0(B_64, C_65) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.15/1.48  tff(c_352, plain, (![C_65]: (k7_subset_1('#skF_2', '#skF_3', C_65)=k4_xboole_0('#skF_3', C_65))), inference(resolution, [status(thm)], [c_28, c_346])).
% 3.15/1.48  tff(c_24, plain, (k9_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_4'))!=k7_subset_1('#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.48  tff(c_362, plain, (k9_subset_1('#skF_2', '#skF_3', k3_subset_1('#skF_2', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_352, c_24])).
% 3.15/1.48  tff(c_619, plain, (k3_xboole_0(k3_subset_1('#skF_2', '#skF_4'), '#skF_3')!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_362])).
% 3.15/1.48  tff(c_620, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))!=k4_xboole_0('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_619])).
% 3.15/1.48  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.15/1.48  tff(c_122, plain, (![C_47, A_48, B_49]: (r2_hidden(C_47, A_48) | ~r2_hidden(C_47, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.15/1.48  tff(c_950, plain, (![A_85, B_86, A_87]: (r2_hidden('#skF_1'(A_85, B_86), A_87) | ~m1_subset_1(A_85, k1_zfmisc_1(A_87)) | r1_tarski(A_85, B_86))), inference(resolution, [status(thm)], [c_8, c_122])).
% 3.15/1.48  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.15/1.48  tff(c_962, plain, (![A_88, A_89]: (~m1_subset_1(A_88, k1_zfmisc_1(A_89)) | r1_tarski(A_88, A_89))), inference(resolution, [status(thm)], [c_950, c_6])).
% 3.15/1.48  tff(c_970, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_962])).
% 3.15/1.48  tff(c_10, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.15/1.48  tff(c_978, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_970, c_10])).
% 3.15/1.48  tff(c_88, plain, (![A_42, B_43, C_44]: (k4_xboole_0(k3_xboole_0(A_42, B_43), C_44)=k3_xboole_0(A_42, k4_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.48  tff(c_103, plain, (![A_1, B_2, C_44]: (k4_xboole_0(k3_xboole_0(A_1, B_2), C_44)=k3_xboole_0(B_2, k4_xboole_0(A_1, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_88])).
% 3.15/1.48  tff(c_1065, plain, (![C_92]: (k3_xboole_0('#skF_2', k4_xboole_0('#skF_3', C_92))=k4_xboole_0('#skF_3', C_92))), inference(superposition, [status(thm), theory('equality')], [c_978, c_103])).
% 3.15/1.48  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.15/1.48  tff(c_126, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k3_subset_1(A_50, B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.15/1.48  tff(c_133, plain, (k4_xboole_0('#skF_2', '#skF_4')=k3_subset_1('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_126])).
% 3.15/1.48  tff(c_190, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(B_58, k4_xboole_0(A_57, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_88])).
% 3.15/1.48  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_xboole_0(k3_xboole_0(A_10, B_11), C_12)=k3_xboole_0(A_10, k4_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.48  tff(c_231, plain, (![B_60, A_61, C_62]: (k3_xboole_0(B_60, k4_xboole_0(A_61, C_62))=k3_xboole_0(A_61, k4_xboole_0(B_60, C_62)))), inference(superposition, [status(thm), theory('equality')], [c_190, c_12])).
% 3.15/1.48  tff(c_305, plain, (![A_61]: (k3_xboole_0(A_61, k3_subset_1('#skF_2', '#skF_4'))=k3_xboole_0('#skF_2', k4_xboole_0(A_61, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_133, c_231])).
% 3.15/1.48  tff(c_1076, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_2', '#skF_4'))=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1065, c_305])).
% 3.15/1.48  tff(c_1110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_620, c_1076])).
% 3.15/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.48  
% 3.15/1.48  Inference rules
% 3.15/1.48  ----------------------
% 3.15/1.48  #Ref     : 0
% 3.15/1.48  #Sup     : 278
% 3.15/1.48  #Fact    : 0
% 3.15/1.48  #Define  : 0
% 3.15/1.48  #Split   : 0
% 3.15/1.48  #Chain   : 0
% 3.15/1.48  #Close   : 0
% 3.15/1.48  
% 3.15/1.48  Ordering : KBO
% 3.15/1.48  
% 3.15/1.48  Simplification rules
% 3.15/1.48  ----------------------
% 3.15/1.48  #Subsume      : 15
% 3.15/1.48  #Demod        : 77
% 3.15/1.48  #Tautology    : 114
% 3.15/1.48  #SimpNegUnit  : 1
% 3.15/1.48  #BackRed      : 2
% 3.15/1.48  
% 3.15/1.48  #Partial instantiations: 0
% 3.15/1.48  #Strategies tried      : 1
% 3.15/1.48  
% 3.15/1.48  Timing (in seconds)
% 3.15/1.48  ----------------------
% 3.15/1.48  Preprocessing        : 0.29
% 3.15/1.48  Parsing              : 0.16
% 3.15/1.48  CNF conversion       : 0.02
% 3.15/1.48  Main loop            : 0.42
% 3.15/1.48  Inferencing          : 0.15
% 3.15/1.48  Reduction            : 0.16
% 3.15/1.48  Demodulation         : 0.13
% 3.15/1.48  BG Simplification    : 0.02
% 3.15/1.48  Subsumption          : 0.06
% 3.15/1.48  Abstraction          : 0.02
% 3.15/1.49  MUC search           : 0.00
% 3.15/1.49  Cooper               : 0.00
% 3.15/1.49  Total                : 0.74
% 3.15/1.49  Index Insertion      : 0.00
% 3.15/1.49  Index Deletion       : 0.00
% 3.15/1.49  Index Matching       : 0.00
% 3.15/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
