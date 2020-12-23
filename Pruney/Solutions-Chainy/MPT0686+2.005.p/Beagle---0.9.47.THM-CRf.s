%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:32 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   48 (  63 expanded)
%              Number of leaves         :   26 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  90 expanded)
%              Number of equality atoms :   15 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = k1_xboole_0
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_61,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_53])).

tff(c_193,plain,(
    ! [A_60,B_61,C_62] :
      ( r2_hidden('#skF_1'(A_60,B_61,C_62),B_61)
      | r2_hidden('#skF_2'(A_60,B_61,C_62),C_62)
      | k3_xboole_0(A_60,B_61) = C_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden(A_24,B_25)
      | ~ r1_xboole_0(k1_tarski(A_24),B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_24] : ~ r2_hidden(A_24,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_46])).

tff(c_217,plain,(
    ! [A_60,C_62] :
      ( r2_hidden('#skF_2'(A_60,k1_xboole_0,C_62),C_62)
      | k3_xboole_0(A_60,k1_xboole_0) = C_62 ) ),
    inference(resolution,[status(thm)],[c_193,c_51])).

tff(c_249,plain,(
    ! [A_63,C_64] :
      ( r2_hidden('#skF_2'(A_63,k1_xboole_0,C_64),C_64)
      | k1_xboole_0 = C_64 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_217])).

tff(c_126,plain,(
    ! [A_44,B_45,C_46] :
      ( r2_hidden('#skF_3'(A_44,B_45,C_46),B_45)
      | ~ r2_hidden(A_44,k10_relat_1(C_46,B_45))
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_146,plain,(
    ! [A_44,C_46] :
      ( ~ r2_hidden(A_44,k10_relat_1(C_46,k1_xboole_0))
      | ~ v1_relat_1(C_46) ) ),
    inference(resolution,[status(thm)],[c_126,c_51])).

tff(c_281,plain,(
    ! [C_65] :
      ( ~ v1_relat_1(C_65)
      | k10_relat_1(C_65,k1_xboole_0) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_249,c_146])).

tff(c_285,plain,(
    k10_relat_1('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_281])).

tff(c_40,plain,(
    r1_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_60,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_782,plain,(
    ! [C_96,A_97,B_98] :
      ( k3_xboole_0(k10_relat_1(C_96,A_97),k10_relat_1(C_96,B_98)) = k10_relat_1(C_96,k3_xboole_0(A_97,B_98))
      | ~ v1_funct_1(C_96)
      | ~ v1_relat_1(C_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_66,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k3_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_4','#skF_5'),k10_relat_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_79,plain,(
    k3_xboole_0(k10_relat_1('#skF_4','#skF_5'),k10_relat_1('#skF_4','#skF_6')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_38])).

tff(c_817,plain,
    ( k10_relat_1('#skF_4',k3_xboole_0('#skF_5','#skF_6')) != k1_xboole_0
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_79])).

tff(c_865,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_285,c_60,c_817])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:12:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.36  
% 2.52/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.37  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.52/1.37  
% 2.52/1.37  %Foreground sorts:
% 2.52/1.37  
% 2.52/1.37  
% 2.52/1.37  %Background operators:
% 2.52/1.37  
% 2.52/1.37  
% 2.52/1.37  %Foreground operators:
% 2.52/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.52/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.52/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.52/1.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.52/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.52/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.52/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.52/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.52/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.37  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.52/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.52/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.52/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.52/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.37  
% 2.52/1.38  tff(f_72, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_funct_1)).
% 2.52/1.38  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.52/1.38  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.52/1.38  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.52/1.38  tff(f_45, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.52/1.38  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.52/1.38  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 2.52/1.38  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.38  tff(c_42, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.38  tff(c_24, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.52/1.38  tff(c_53, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=k1_xboole_0 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.52/1.38  tff(c_61, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_53])).
% 2.52/1.38  tff(c_193, plain, (![A_60, B_61, C_62]: (r2_hidden('#skF_1'(A_60, B_61, C_62), B_61) | r2_hidden('#skF_2'(A_60, B_61, C_62), C_62) | k3_xboole_0(A_60, B_61)=C_62)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.52/1.38  tff(c_46, plain, (![A_24, B_25]: (~r2_hidden(A_24, B_25) | ~r1_xboole_0(k1_tarski(A_24), B_25))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.38  tff(c_51, plain, (![A_24]: (~r2_hidden(A_24, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_46])).
% 2.52/1.38  tff(c_217, plain, (![A_60, C_62]: (r2_hidden('#skF_2'(A_60, k1_xboole_0, C_62), C_62) | k3_xboole_0(A_60, k1_xboole_0)=C_62)), inference(resolution, [status(thm)], [c_193, c_51])).
% 2.52/1.38  tff(c_249, plain, (![A_63, C_64]: (r2_hidden('#skF_2'(A_63, k1_xboole_0, C_64), C_64) | k1_xboole_0=C_64)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_217])).
% 2.52/1.38  tff(c_126, plain, (![A_44, B_45, C_46]: (r2_hidden('#skF_3'(A_44, B_45, C_46), B_45) | ~r2_hidden(A_44, k10_relat_1(C_46, B_45)) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.52/1.38  tff(c_146, plain, (![A_44, C_46]: (~r2_hidden(A_44, k10_relat_1(C_46, k1_xboole_0)) | ~v1_relat_1(C_46))), inference(resolution, [status(thm)], [c_126, c_51])).
% 2.52/1.38  tff(c_281, plain, (![C_65]: (~v1_relat_1(C_65) | k10_relat_1(C_65, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_249, c_146])).
% 2.52/1.38  tff(c_285, plain, (k10_relat_1('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_281])).
% 2.52/1.38  tff(c_40, plain, (r1_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.38  tff(c_60, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_53])).
% 2.52/1.38  tff(c_782, plain, (![C_96, A_97, B_98]: (k3_xboole_0(k10_relat_1(C_96, A_97), k10_relat_1(C_96, B_98))=k10_relat_1(C_96, k3_xboole_0(A_97, B_98)) | ~v1_funct_1(C_96) | ~v1_relat_1(C_96))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.52/1.38  tff(c_66, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k3_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.52/1.38  tff(c_38, plain, (~r1_xboole_0(k10_relat_1('#skF_4', '#skF_5'), k10_relat_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.52/1.38  tff(c_79, plain, (k3_xboole_0(k10_relat_1('#skF_4', '#skF_5'), k10_relat_1('#skF_4', '#skF_6'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_66, c_38])).
% 2.52/1.38  tff(c_817, plain, (k10_relat_1('#skF_4', k3_xboole_0('#skF_5', '#skF_6'))!=k1_xboole_0 | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_782, c_79])).
% 2.52/1.38  tff(c_865, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_285, c_60, c_817])).
% 2.52/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.38  
% 2.52/1.38  Inference rules
% 2.52/1.38  ----------------------
% 2.52/1.38  #Ref     : 0
% 2.52/1.38  #Sup     : 192
% 2.52/1.38  #Fact    : 0
% 2.52/1.38  #Define  : 0
% 2.52/1.38  #Split   : 2
% 2.52/1.38  #Chain   : 0
% 2.52/1.38  #Close   : 0
% 2.52/1.38  
% 2.52/1.38  Ordering : KBO
% 2.52/1.38  
% 2.52/1.38  Simplification rules
% 2.52/1.38  ----------------------
% 2.52/1.38  #Subsume      : 58
% 2.52/1.38  #Demod        : 34
% 2.52/1.38  #Tautology    : 63
% 2.52/1.38  #SimpNegUnit  : 12
% 2.52/1.38  #BackRed      : 0
% 2.52/1.38  
% 2.52/1.38  #Partial instantiations: 0
% 2.52/1.38  #Strategies tried      : 1
% 2.52/1.38  
% 2.52/1.38  Timing (in seconds)
% 2.52/1.38  ----------------------
% 2.52/1.38  Preprocessing        : 0.29
% 2.52/1.38  Parsing              : 0.15
% 2.52/1.38  CNF conversion       : 0.02
% 2.52/1.38  Main loop            : 0.33
% 2.52/1.38  Inferencing          : 0.13
% 2.52/1.38  Reduction            : 0.08
% 2.52/1.38  Demodulation         : 0.05
% 2.52/1.38  BG Simplification    : 0.02
% 2.52/1.38  Subsumption          : 0.07
% 2.52/1.38  Abstraction          : 0.02
% 2.52/1.38  MUC search           : 0.00
% 2.52/1.38  Cooper               : 0.00
% 2.52/1.38  Total                : 0.64
% 2.52/1.38  Index Insertion      : 0.00
% 2.52/1.38  Index Deletion       : 0.00
% 2.52/1.38  Index Matching       : 0.00
% 2.52/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
