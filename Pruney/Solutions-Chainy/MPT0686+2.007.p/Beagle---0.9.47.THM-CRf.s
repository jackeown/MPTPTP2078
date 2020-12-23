%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:32 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   53 (  74 expanded)
%              Number of leaves         :   25 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 128 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_funct_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_34,plain,(
    ! [A_24,B_25] :
      ( k3_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_41,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_34])).

tff(c_587,plain,(
    ! [C_116,A_117,B_118] :
      ( k3_xboole_0(k10_relat_1(C_116,A_117),k10_relat_1(C_116,B_118)) = k10_relat_1(C_116,k3_xboole_0(A_117,B_118))
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_54,plain,(
    ! [A_27,B_28] :
      ( r1_xboole_0(A_27,B_28)
      | k3_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_3','#skF_4'),k10_relat_1('#skF_3','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    k3_xboole_0(k10_relat_1('#skF_3','#skF_4'),k10_relat_1('#skF_3','#skF_5')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_26])).

tff(c_620,plain,
    ( k10_relat_1('#skF_3',k3_xboole_0('#skF_4','#skF_5')) != k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_62])).

tff(c_646,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_41,c_620])).

tff(c_75,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_1'(A_33,B_34),A_33)
      | r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_63,plain,(
    ! [A_29,C_30,B_31] :
      ( ~ r2_hidden(A_29,C_30)
      | ~ r1_xboole_0(k2_tarski(A_29,B_31),C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_73,plain,(
    ! [A_29] : ~ r2_hidden(A_29,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_12,c_63])).

tff(c_81,plain,(
    ! [B_35] : r1_xboole_0(k1_xboole_0,B_35) ),
    inference(resolution,[status(thm)],[c_75,c_73])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_85,plain,(
    ! [B_35] : k3_xboole_0(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_178,plain,(
    ! [A_54,B_55,C_56] :
      ( r2_hidden('#skF_2'(A_54,B_55,C_56),B_55)
      | ~ r2_hidden(A_54,k10_relat_1(C_56,B_55))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_192,plain,(
    ! [A_57,C_58] :
      ( ~ r2_hidden(A_57,k10_relat_1(C_58,k1_xboole_0))
      | ~ v1_relat_1(C_58) ) ),
    inference(resolution,[status(thm)],[c_178,c_73])).

tff(c_233,plain,(
    ! [C_65,B_66] :
      ( ~ v1_relat_1(C_65)
      | r1_xboole_0(k10_relat_1(C_65,k1_xboole_0),B_66) ) ),
    inference(resolution,[status(thm)],[c_10,c_192])).

tff(c_240,plain,(
    ! [C_65,B_66] :
      ( k3_xboole_0(k10_relat_1(C_65,k1_xboole_0),B_66) = k1_xboole_0
      | ~ v1_relat_1(C_65) ) ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_610,plain,(
    ! [C_116,B_118] :
      ( k10_relat_1(C_116,k3_xboole_0(k1_xboole_0,B_118)) = k1_xboole_0
      | ~ v1_relat_1(C_116)
      | ~ v1_funct_1(C_116)
      | ~ v1_relat_1(C_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_240])).

tff(c_650,plain,(
    ! [C_119] :
      ( k10_relat_1(C_119,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_119)
      | ~ v1_funct_1(C_119)
      | ~ v1_relat_1(C_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_610])).

tff(c_652,plain,
    ( k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_650])).

tff(c_655,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_652])).

tff(c_657,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_646,c_655])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:49:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.34  
% 2.66/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.34  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_2 > #skF_4 > #skF_1
% 2.66/1.34  
% 2.66/1.34  %Foreground sorts:
% 2.66/1.34  
% 2.66/1.34  
% 2.66/1.34  %Background operators:
% 2.66/1.34  
% 2.66/1.34  
% 2.66/1.34  %Foreground operators:
% 2.66/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.66/1.34  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.66/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.66/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.66/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.66/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.34  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.66/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.66/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.66/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.66/1.35  
% 2.66/1.36  tff(f_81, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_funct_1)).
% 2.66/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.66/1.36  tff(f_71, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_funct_1)).
% 2.66/1.36  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.66/1.36  tff(f_49, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.66/1.36  tff(f_54, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.66/1.36  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.66/1.36  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.66/1.36  tff(c_30, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.66/1.36  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.66/1.36  tff(c_34, plain, (![A_24, B_25]: (k3_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.36  tff(c_41, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_34])).
% 2.66/1.36  tff(c_587, plain, (![C_116, A_117, B_118]: (k3_xboole_0(k10_relat_1(C_116, A_117), k10_relat_1(C_116, B_118))=k10_relat_1(C_116, k3_xboole_0(A_117, B_118)) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.66/1.36  tff(c_54, plain, (![A_27, B_28]: (r1_xboole_0(A_27, B_28) | k3_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.36  tff(c_26, plain, (~r1_xboole_0(k10_relat_1('#skF_3', '#skF_4'), k10_relat_1('#skF_3', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.66/1.36  tff(c_62, plain, (k3_xboole_0(k10_relat_1('#skF_3', '#skF_4'), k10_relat_1('#skF_3', '#skF_5'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_26])).
% 2.66/1.36  tff(c_620, plain, (k10_relat_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5'))!=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_587, c_62])).
% 2.66/1.36  tff(c_646, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_41, c_620])).
% 2.66/1.36  tff(c_75, plain, (![A_33, B_34]: (r2_hidden('#skF_1'(A_33, B_34), A_33) | r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.36  tff(c_12, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.66/1.36  tff(c_63, plain, (![A_29, C_30, B_31]: (~r2_hidden(A_29, C_30) | ~r1_xboole_0(k2_tarski(A_29, B_31), C_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.66/1.36  tff(c_73, plain, (![A_29]: (~r2_hidden(A_29, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_63])).
% 2.66/1.36  tff(c_81, plain, (![B_35]: (r1_xboole_0(k1_xboole_0, B_35))), inference(resolution, [status(thm)], [c_75, c_73])).
% 2.66/1.36  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.36  tff(c_85, plain, (![B_35]: (k3_xboole_0(k1_xboole_0, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.66/1.36  tff(c_10, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.66/1.36  tff(c_178, plain, (![A_54, B_55, C_56]: (r2_hidden('#skF_2'(A_54, B_55, C_56), B_55) | ~r2_hidden(A_54, k10_relat_1(C_56, B_55)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.66/1.36  tff(c_192, plain, (![A_57, C_58]: (~r2_hidden(A_57, k10_relat_1(C_58, k1_xboole_0)) | ~v1_relat_1(C_58))), inference(resolution, [status(thm)], [c_178, c_73])).
% 2.66/1.36  tff(c_233, plain, (![C_65, B_66]: (~v1_relat_1(C_65) | r1_xboole_0(k10_relat_1(C_65, k1_xboole_0), B_66))), inference(resolution, [status(thm)], [c_10, c_192])).
% 2.66/1.36  tff(c_240, plain, (![C_65, B_66]: (k3_xboole_0(k10_relat_1(C_65, k1_xboole_0), B_66)=k1_xboole_0 | ~v1_relat_1(C_65))), inference(resolution, [status(thm)], [c_233, c_2])).
% 2.66/1.36  tff(c_610, plain, (![C_116, B_118]: (k10_relat_1(C_116, k3_xboole_0(k1_xboole_0, B_118))=k1_xboole_0 | ~v1_relat_1(C_116) | ~v1_funct_1(C_116) | ~v1_relat_1(C_116))), inference(superposition, [status(thm), theory('equality')], [c_587, c_240])).
% 2.66/1.36  tff(c_650, plain, (![C_119]: (k10_relat_1(C_119, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_119) | ~v1_funct_1(C_119) | ~v1_relat_1(C_119))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_610])).
% 2.66/1.36  tff(c_652, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0 | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_650])).
% 2.66/1.36  tff(c_655, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_652])).
% 2.66/1.36  tff(c_657, plain, $false, inference(negUnitSimplification, [status(thm)], [c_646, c_655])).
% 2.66/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.36  
% 2.66/1.36  Inference rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Ref     : 0
% 2.66/1.36  #Sup     : 143
% 2.66/1.36  #Fact    : 0
% 2.66/1.36  #Define  : 0
% 2.66/1.36  #Split   : 2
% 2.66/1.36  #Chain   : 0
% 2.66/1.36  #Close   : 0
% 2.66/1.36  
% 2.66/1.36  Ordering : KBO
% 2.66/1.36  
% 2.66/1.36  Simplification rules
% 2.66/1.36  ----------------------
% 2.66/1.36  #Subsume      : 33
% 2.66/1.36  #Demod        : 22
% 2.66/1.36  #Tautology    : 47
% 2.66/1.36  #SimpNegUnit  : 1
% 2.66/1.36  #BackRed      : 0
% 2.66/1.36  
% 2.66/1.36  #Partial instantiations: 0
% 2.66/1.36  #Strategies tried      : 1
% 2.66/1.36  
% 2.66/1.36  Timing (in seconds)
% 2.66/1.36  ----------------------
% 2.66/1.36  Preprocessing        : 0.28
% 2.66/1.36  Parsing              : 0.16
% 2.66/1.36  CNF conversion       : 0.02
% 2.66/1.36  Main loop            : 0.32
% 2.66/1.36  Inferencing          : 0.13
% 2.66/1.36  Reduction            : 0.08
% 2.66/1.36  Demodulation         : 0.05
% 2.66/1.36  BG Simplification    : 0.01
% 2.66/1.36  Subsumption          : 0.08
% 2.66/1.36  Abstraction          : 0.01
% 2.66/1.36  MUC search           : 0.00
% 2.66/1.36  Cooper               : 0.00
% 2.66/1.36  Total                : 0.64
% 2.66/1.36  Index Insertion      : 0.00
% 2.66/1.36  Index Deletion       : 0.00
% 2.66/1.36  Index Matching       : 0.00
% 2.66/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
