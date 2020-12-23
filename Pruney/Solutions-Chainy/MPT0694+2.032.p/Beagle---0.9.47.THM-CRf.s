%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:57 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   52 (  97 expanded)
%              Number of leaves         :   22 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 182 expanded)
%              Number of equality atoms :    5 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,k10_relat_1(C,B))),k3_xboole_0(k9_relat_1(C,A),B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k7_relat_1(A,B))
        & v1_funct_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_funct_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [A_16,B_17] :
      ( v1_funct_1(k7_relat_1(A_16,B_17))
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    ! [A_34,C_35,B_36] :
      ( k3_xboole_0(A_34,k10_relat_1(C_35,B_36)) = k10_relat_1(k7_relat_1(C_35,A_34),B_36)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [C_35,A_34,B_36] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_35,A_34),B_36),A_34)
      | ~ v1_relat_1(C_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_2])).

tff(c_56,plain,(
    ! [A_43,C_44,B_45] :
      ( k9_relat_1(k7_relat_1(A_43,C_44),B_45) = k9_relat_1(A_43,B_45)
      | ~ r1_tarski(B_45,C_44)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_18,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,k10_relat_1(B_22,A_21)),A_21)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_117,plain,(
    ! [A_58,C_59,A_60] :
      ( r1_tarski(k9_relat_1(A_58,k10_relat_1(k7_relat_1(A_58,C_59),A_60)),A_60)
      | ~ v1_funct_1(k7_relat_1(A_58,C_59))
      | ~ v1_relat_1(k7_relat_1(A_58,C_59))
      | ~ r1_tarski(k10_relat_1(k7_relat_1(A_58,C_59),A_60),C_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_18])).

tff(c_129,plain,(
    ! [C_61,A_62,B_63] :
      ( r1_tarski(k9_relat_1(C_61,k10_relat_1(k7_relat_1(C_61,A_62),B_63)),B_63)
      | ~ v1_funct_1(k7_relat_1(C_61,A_62))
      | ~ v1_relat_1(k7_relat_1(C_61,A_62))
      | ~ v1_relat_1(C_61) ) ),
    inference(resolution,[status(thm)],[c_39,c_117])).

tff(c_16,plain,(
    ! [A_18,C_20,B_19] :
      ( k3_xboole_0(A_18,k10_relat_1(C_20,B_19)) = k10_relat_1(k7_relat_1(C_20,A_18),B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [C_10,A_8,B_9] :
      ( r1_tarski(k9_relat_1(C_10,A_8),k9_relat_1(C_10,B_9))
      | ~ r1_tarski(A_8,B_9)
      | ~ v1_relat_1(C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [A_3,B_4,C_5] :
      ( r1_tarski(A_3,k3_xboole_0(B_4,C_5))
      | ~ r1_tarski(A_3,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2')
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_4,c_20])).

tff(c_80,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_83,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2')),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_90,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2,c_83])).

tff(c_91,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1',k10_relat_1('#skF_3','#skF_2'))),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_95,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_91])).

tff(c_97,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k10_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_95])).

tff(c_132,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_129,c_97])).

tff(c_139,plain,
    ( ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_132])).

tff(c_148,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_151,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_151])).

tff(c_156,plain,(
    ~ v1_funct_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_160,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_156])).

tff(c_164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.31  % Computer   : n010.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 16:41:44 EST 2020
% 0.12/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/1.62  
% 2.33/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.63  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.58/1.63  
% 2.58/1.63  %Foreground sorts:
% 2.58/1.63  
% 2.58/1.63  
% 2.58/1.63  %Background operators:
% 2.58/1.63  
% 2.58/1.63  
% 2.58/1.63  %Foreground operators:
% 2.58/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.58/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.58/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.63  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.63  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.58/1.63  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.63  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.63  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.58/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.63  
% 2.58/1.65  tff(f_75, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, k10_relat_1(C, B))), k3_xboole_0(k9_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_funct_1)).
% 2.58/1.65  tff(f_58, axiom, (![A, B]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k7_relat_1(A, B)) & v1_funct_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_funct_1)).
% 2.58/1.65  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.58/1.65  tff(f_62, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.58/1.65  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.58/1.65  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.58/1.65  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 2.58/1.65  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t156_relat_1)).
% 2.58/1.65  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.58/1.65  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.58/1.65  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.58/1.65  tff(c_12, plain, (![A_16, B_17]: (v1_funct_1(k7_relat_1(A_16, B_17)) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.58/1.65  tff(c_6, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.65  tff(c_30, plain, (![A_34, C_35, B_36]: (k3_xboole_0(A_34, k10_relat_1(C_35, B_36))=k10_relat_1(k7_relat_1(C_35, A_34), B_36) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.58/1.65  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.65  tff(c_39, plain, (![C_35, A_34, B_36]: (r1_tarski(k10_relat_1(k7_relat_1(C_35, A_34), B_36), A_34) | ~v1_relat_1(C_35))), inference(superposition, [status(thm), theory('equality')], [c_30, c_2])).
% 2.58/1.65  tff(c_56, plain, (![A_43, C_44, B_45]: (k9_relat_1(k7_relat_1(A_43, C_44), B_45)=k9_relat_1(A_43, B_45) | ~r1_tarski(B_45, C_44) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.58/1.65  tff(c_18, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, k10_relat_1(B_22, A_21)), A_21) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.58/1.65  tff(c_117, plain, (![A_58, C_59, A_60]: (r1_tarski(k9_relat_1(A_58, k10_relat_1(k7_relat_1(A_58, C_59), A_60)), A_60) | ~v1_funct_1(k7_relat_1(A_58, C_59)) | ~v1_relat_1(k7_relat_1(A_58, C_59)) | ~r1_tarski(k10_relat_1(k7_relat_1(A_58, C_59), A_60), C_59) | ~v1_relat_1(A_58))), inference(superposition, [status(thm), theory('equality')], [c_56, c_18])).
% 2.58/1.65  tff(c_129, plain, (![C_61, A_62, B_63]: (r1_tarski(k9_relat_1(C_61, k10_relat_1(k7_relat_1(C_61, A_62), B_63)), B_63) | ~v1_funct_1(k7_relat_1(C_61, A_62)) | ~v1_relat_1(k7_relat_1(C_61, A_62)) | ~v1_relat_1(C_61))), inference(resolution, [status(thm)], [c_39, c_117])).
% 2.58/1.65  tff(c_16, plain, (![A_18, C_20, B_19]: (k3_xboole_0(A_18, k10_relat_1(C_20, B_19))=k10_relat_1(k7_relat_1(C_20, A_18), B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.58/1.65  tff(c_8, plain, (![C_10, A_8, B_9]: (r1_tarski(k9_relat_1(C_10, A_8), k9_relat_1(C_10, B_9)) | ~r1_tarski(A_8, B_9) | ~v1_relat_1(C_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.65  tff(c_4, plain, (![A_3, B_4, C_5]: (r1_tarski(A_3, k3_xboole_0(B_4, C_5)) | ~r1_tarski(A_3, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.65  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.58/1.65  tff(c_54, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2') | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_4, c_20])).
% 2.58/1.65  tff(c_80, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_54])).
% 2.58/1.65  tff(c_83, plain, (~r1_tarski(k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2')), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8, c_80])).
% 2.58/1.65  tff(c_90, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_2, c_83])).
% 2.58/1.65  tff(c_91, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), '#skF_2')), inference(splitRight, [status(thm)], [c_54])).
% 2.58/1.65  tff(c_95, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_91])).
% 2.58/1.65  tff(c_97, plain, (~r1_tarski(k9_relat_1('#skF_3', k10_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_95])).
% 2.58/1.65  tff(c_132, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_129, c_97])).
% 2.58/1.65  tff(c_139, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_132])).
% 2.58/1.65  tff(c_148, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_139])).
% 2.58/1.65  tff(c_151, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_148])).
% 2.58/1.65  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_151])).
% 2.58/1.65  tff(c_156, plain, (~v1_funct_1(k7_relat_1('#skF_3', '#skF_1'))), inference(splitRight, [status(thm)], [c_139])).
% 2.58/1.65  tff(c_160, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_156])).
% 2.58/1.65  tff(c_164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_160])).
% 2.58/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.65  
% 2.58/1.65  Inference rules
% 2.58/1.65  ----------------------
% 2.58/1.65  #Ref     : 0
% 2.58/1.65  #Sup     : 29
% 2.58/1.65  #Fact    : 0
% 2.58/1.65  #Define  : 0
% 2.58/1.65  #Split   : 2
% 2.58/1.65  #Chain   : 0
% 2.58/1.65  #Close   : 0
% 2.58/1.65  
% 2.58/1.65  Ordering : KBO
% 2.58/1.65  
% 2.58/1.65  Simplification rules
% 2.58/1.65  ----------------------
% 2.58/1.65  #Subsume      : 6
% 2.58/1.65  #Demod        : 9
% 2.58/1.65  #Tautology    : 4
% 2.58/1.65  #SimpNegUnit  : 0
% 2.58/1.65  #BackRed      : 0
% 2.58/1.65  
% 2.58/1.65  #Partial instantiations: 0
% 2.58/1.65  #Strategies tried      : 1
% 2.58/1.65  
% 2.58/1.65  Timing (in seconds)
% 2.58/1.65  ----------------------
% 2.58/1.65  Preprocessing        : 0.46
% 2.58/1.65  Parsing              : 0.24
% 2.58/1.65  CNF conversion       : 0.03
% 2.58/1.66  Main loop            : 0.32
% 2.58/1.66  Inferencing          : 0.13
% 2.58/1.66  Reduction            : 0.09
% 2.58/1.66  Demodulation         : 0.07
% 2.58/1.66  BG Simplification    : 0.02
% 2.58/1.66  Subsumption          : 0.06
% 2.58/1.66  Abstraction          : 0.02
% 2.58/1.66  MUC search           : 0.00
% 2.58/1.66  Cooper               : 0.00
% 2.58/1.66  Total                : 0.83
% 2.58/1.66  Index Insertion      : 0.00
% 2.58/1.66  Index Deletion       : 0.00
% 2.58/1.66  Index Matching       : 0.00
% 2.58/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
