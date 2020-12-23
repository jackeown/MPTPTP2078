%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:15 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 123 expanded)
%              Number of leaves         :   21 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 284 expanded)
%              Number of equality atoms :   26 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v2_funct_1(A)
        <=> ! [B] :
            ? [C] : r1_tarski(k10_relat_1(A,k1_tarski(B)),k1_tarski(C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t159_funct_1)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( ! [B] :
            ~ ( r2_hidden(B,k2_relat_1(A))
              & ! [C] : k10_relat_1(A,k1_tarski(B)) != k1_tarski(C) )
      <=> v2_funct_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(k1_xboole_0,k1_tarski(B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [B_2] : r1_tarski(k1_tarski(B_2),k1_tarski(B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_18,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_22,plain,(
    ! [C_23] :
      ( ~ r1_tarski(k10_relat_1('#skF_3',k1_tarski('#skF_4')),k1_tarski(C_23))
      | ~ v2_funct_1('#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_31,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,(
    ! [B_24] :
      ( v2_funct_1('#skF_3')
      | r1_tarski(k10_relat_1('#skF_3',k1_tarski(B_24)),k1_tarski('#skF_5'(B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ! [B_30] : r1_tarski(k10_relat_1('#skF_3',k1_tarski(B_30)),k1_tarski('#skF_5'(B_30))) ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_28])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_tarski(B_2) = A_1
      | k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_tarski(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [B_30] :
      ( k10_relat_1('#skF_3',k1_tarski(B_30)) = k1_tarski('#skF_5'(B_30))
      | k10_relat_1('#skF_3',k1_tarski(B_30)) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_113,plain,(
    ! [C_39,A_40] :
      ( k1_tarski(C_39) != k10_relat_1(A_40,k1_tarski('#skF_1'(A_40)))
      | v2_funct_1(A_40)
      | ~ v1_funct_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_121,plain,(
    ! [C_39] :
      ( k1_tarski(C_39) != k1_tarski('#skF_5'('#skF_1'('#skF_3')))
      | v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | k10_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_113])).

tff(c_126,plain,(
    ! [C_39] :
      ( k1_tarski(C_39) != k1_tarski('#skF_5'('#skF_1'('#skF_3')))
      | v2_funct_1('#skF_3')
      | k10_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_121])).

tff(c_127,plain,(
    ! [C_39] :
      ( k1_tarski(C_39) != k1_tarski('#skF_5'('#skF_1'('#skF_3')))
      | k10_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_126])).

tff(c_128,plain,(
    ! [C_39] : k1_tarski(C_39) != k1_tarski('#skF_5'('#skF_1'('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_132,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_128])).

tff(c_133,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_1'('#skF_3'))) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_56,plain,(
    ! [A_35] :
      ( r2_hidden('#skF_1'(A_35),k2_relat_1(A_35))
      | v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( k10_relat_1(B_4,k1_tarski(A_3)) != k1_xboole_0
      | ~ r2_hidden(A_3,k2_relat_1(B_4))
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [A_35] :
      ( k10_relat_1(A_35,k1_tarski('#skF_1'(A_35))) != k1_xboole_0
      | v2_funct_1(A_35)
      | ~ v1_funct_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(resolution,[status(thm)],[c_56,c_10])).

tff(c_146,plain,
    ( v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_60])).

tff(c_165,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_146])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_31,c_165])).

tff(c_169,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,k2_relat_1(B_4))
      | k10_relat_1(B_4,k1_tarski(A_3)) = k1_xboole_0
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_196,plain,(
    ! [A_52,B_53] :
      ( k10_relat_1(A_52,k1_tarski(B_53)) = k1_tarski('#skF_2'(A_52,B_53))
      | ~ r2_hidden(B_53,k2_relat_1(A_52))
      | ~ v2_funct_1(A_52)
      | ~ v1_funct_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_209,plain,(
    ! [B_54,A_55] :
      ( k10_relat_1(B_54,k1_tarski(A_55)) = k1_tarski('#skF_2'(B_54,A_55))
      | ~ v2_funct_1(B_54)
      | ~ v1_funct_1(B_54)
      | k10_relat_1(B_54,k1_tarski(A_55)) = k1_xboole_0
      | ~ v1_relat_1(B_54) ) ),
    inference(resolution,[status(thm)],[c_8,c_196])).

tff(c_168,plain,(
    ! [C_23] : ~ r1_tarski(k10_relat_1('#skF_3',k1_tarski('#skF_4')),k1_tarski(C_23)) ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_223,plain,(
    ! [C_23] :
      ( ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_tarski(C_23))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | k10_relat_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_168])).

tff(c_229,plain,(
    ! [C_23] :
      ( ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_tarski(C_23))
      | k10_relat_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_169,c_223])).

tff(c_232,plain,(
    ! [C_56] : ~ r1_tarski(k1_tarski('#skF_2'('#skF_3','#skF_4')),k1_tarski(C_56)) ),
    inference(splitLeft,[status(thm)],[c_229])).

tff(c_237,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_4,c_232])).

tff(c_238,plain,(
    k10_relat_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_229])).

tff(c_239,plain,(
    ! [C_23] : ~ r1_tarski(k1_xboole_0,k1_tarski(C_23)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_168])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_239])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:04:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  
% 1.90/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.18  %$ r2_hidden > r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.90/1.18  
% 1.90/1.18  %Foreground sorts:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Background operators:
% 1.90/1.18  
% 1.90/1.18  
% 1.90/1.18  %Foreground operators:
% 1.90/1.18  tff('#skF_5', type, '#skF_5': $i > $i).
% 1.90/1.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.90/1.18  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.90/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.90/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.18  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.90/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.18  
% 1.90/1.19  tff(f_31, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.90/1.19  tff(f_63, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) <=> (![B]: (?[C]: r1_tarski(k10_relat_1(A, k1_tarski(B)), k1_tarski(C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t159_funct_1)).
% 1.90/1.19  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((![B]: ~(r2_hidden(B, k2_relat_1(A)) & (![C]: ~(k10_relat_1(A, k1_tarski(B)) = k1_tarski(C))))) <=> v2_funct_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_funct_1)).
% 1.90/1.19  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 1.90/1.19  tff(c_6, plain, (![B_2]: (r1_tarski(k1_xboole_0, k1_tarski(B_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.19  tff(c_4, plain, (![B_2]: (r1_tarski(k1_tarski(B_2), k1_tarski(B_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.19  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.90/1.19  tff(c_18, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.90/1.19  tff(c_22, plain, (![C_23]: (~r1_tarski(k10_relat_1('#skF_3', k1_tarski('#skF_4')), k1_tarski(C_23)) | ~v2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.90/1.19  tff(c_31, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_22])).
% 1.90/1.19  tff(c_28, plain, (![B_24]: (v2_funct_1('#skF_3') | r1_tarski(k10_relat_1('#skF_3', k1_tarski(B_24)), k1_tarski('#skF_5'(B_24))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.90/1.19  tff(c_44, plain, (![B_30]: (r1_tarski(k10_relat_1('#skF_3', k1_tarski(B_30)), k1_tarski('#skF_5'(B_30))))), inference(negUnitSimplification, [status(thm)], [c_31, c_28])).
% 1.90/1.19  tff(c_2, plain, (![B_2, A_1]: (k1_tarski(B_2)=A_1 | k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_tarski(B_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.90/1.19  tff(c_48, plain, (![B_30]: (k10_relat_1('#skF_3', k1_tarski(B_30))=k1_tarski('#skF_5'(B_30)) | k10_relat_1('#skF_3', k1_tarski(B_30))=k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_2])).
% 1.90/1.19  tff(c_113, plain, (![C_39, A_40]: (k1_tarski(C_39)!=k10_relat_1(A_40, k1_tarski('#skF_1'(A_40))) | v2_funct_1(A_40) | ~v1_funct_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.19  tff(c_121, plain, (![C_39]: (k1_tarski(C_39)!=k1_tarski('#skF_5'('#skF_1'('#skF_3'))) | v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | k10_relat_1('#skF_3', k1_tarski('#skF_1'('#skF_3')))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_113])).
% 1.90/1.19  tff(c_126, plain, (![C_39]: (k1_tarski(C_39)!=k1_tarski('#skF_5'('#skF_1'('#skF_3'))) | v2_funct_1('#skF_3') | k10_relat_1('#skF_3', k1_tarski('#skF_1'('#skF_3')))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_121])).
% 1.90/1.19  tff(c_127, plain, (![C_39]: (k1_tarski(C_39)!=k1_tarski('#skF_5'('#skF_1'('#skF_3'))) | k10_relat_1('#skF_3', k1_tarski('#skF_1'('#skF_3')))=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_31, c_126])).
% 1.90/1.19  tff(c_128, plain, (![C_39]: (k1_tarski(C_39)!=k1_tarski('#skF_5'('#skF_1'('#skF_3'))))), inference(splitLeft, [status(thm)], [c_127])).
% 1.90/1.19  tff(c_132, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_128])).
% 1.90/1.19  tff(c_133, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_1'('#skF_3')))=k1_xboole_0), inference(splitRight, [status(thm)], [c_127])).
% 1.90/1.19  tff(c_56, plain, (![A_35]: (r2_hidden('#skF_1'(A_35), k2_relat_1(A_35)) | v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.19  tff(c_10, plain, (![B_4, A_3]: (k10_relat_1(B_4, k1_tarski(A_3))!=k1_xboole_0 | ~r2_hidden(A_3, k2_relat_1(B_4)) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.19  tff(c_60, plain, (![A_35]: (k10_relat_1(A_35, k1_tarski('#skF_1'(A_35)))!=k1_xboole_0 | v2_funct_1(A_35) | ~v1_funct_1(A_35) | ~v1_relat_1(A_35))), inference(resolution, [status(thm)], [c_56, c_10])).
% 1.90/1.19  tff(c_146, plain, (v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_60])).
% 1.90/1.19  tff(c_165, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_146])).
% 1.90/1.19  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_31, c_165])).
% 1.90/1.19  tff(c_169, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 1.90/1.19  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, k2_relat_1(B_4)) | k10_relat_1(B_4, k1_tarski(A_3))=k1_xboole_0 | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.19  tff(c_196, plain, (![A_52, B_53]: (k10_relat_1(A_52, k1_tarski(B_53))=k1_tarski('#skF_2'(A_52, B_53)) | ~r2_hidden(B_53, k2_relat_1(A_52)) | ~v2_funct_1(A_52) | ~v1_funct_1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.90/1.19  tff(c_209, plain, (![B_54, A_55]: (k10_relat_1(B_54, k1_tarski(A_55))=k1_tarski('#skF_2'(B_54, A_55)) | ~v2_funct_1(B_54) | ~v1_funct_1(B_54) | k10_relat_1(B_54, k1_tarski(A_55))=k1_xboole_0 | ~v1_relat_1(B_54))), inference(resolution, [status(thm)], [c_8, c_196])).
% 1.90/1.19  tff(c_168, plain, (![C_23]: (~r1_tarski(k10_relat_1('#skF_3', k1_tarski('#skF_4')), k1_tarski(C_23)))), inference(splitRight, [status(thm)], [c_22])).
% 1.90/1.19  tff(c_223, plain, (![C_23]: (~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_tarski(C_23)) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | k10_relat_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_168])).
% 1.90/1.19  tff(c_229, plain, (![C_23]: (~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_tarski(C_23)) | k10_relat_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_169, c_223])).
% 1.90/1.19  tff(c_232, plain, (![C_56]: (~r1_tarski(k1_tarski('#skF_2'('#skF_3', '#skF_4')), k1_tarski(C_56)))), inference(splitLeft, [status(thm)], [c_229])).
% 1.90/1.19  tff(c_237, plain, $false, inference(resolution, [status(thm)], [c_4, c_232])).
% 1.90/1.19  tff(c_238, plain, (k10_relat_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_229])).
% 1.90/1.19  tff(c_239, plain, (![C_23]: (~r1_tarski(k1_xboole_0, k1_tarski(C_23)))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_168])).
% 1.90/1.19  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_239])).
% 1.90/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  Inference rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Ref     : 1
% 1.90/1.19  #Sup     : 38
% 1.90/1.19  #Fact    : 2
% 1.90/1.19  #Define  : 0
% 1.90/1.19  #Split   : 3
% 1.90/1.19  #Chain   : 0
% 1.90/1.19  #Close   : 0
% 1.90/1.19  
% 1.90/1.19  Ordering : KBO
% 1.90/1.19  
% 1.90/1.19  Simplification rules
% 1.90/1.19  ----------------------
% 1.90/1.19  #Subsume      : 6
% 1.90/1.19  #Demod        : 22
% 1.90/1.19  #Tautology    : 22
% 1.90/1.19  #SimpNegUnit  : 8
% 1.90/1.19  #BackRed      : 1
% 1.90/1.19  
% 1.90/1.19  #Partial instantiations: 0
% 1.90/1.19  #Strategies tried      : 1
% 1.90/1.19  
% 1.90/1.19  Timing (in seconds)
% 1.90/1.19  ----------------------
% 1.90/1.20  Preprocessing        : 0.29
% 1.90/1.20  Parsing              : 0.14
% 1.90/1.20  CNF conversion       : 0.02
% 1.90/1.20  Main loop            : 0.17
% 1.90/1.20  Inferencing          : 0.06
% 1.90/1.20  Reduction            : 0.05
% 1.90/1.20  Demodulation         : 0.03
% 1.90/1.20  BG Simplification    : 0.01
% 1.90/1.20  Subsumption          : 0.03
% 1.90/1.20  Abstraction          : 0.01
% 1.90/1.20  MUC search           : 0.00
% 1.90/1.20  Cooper               : 0.00
% 1.90/1.20  Total                : 0.48
% 1.90/1.20  Index Insertion      : 0.00
% 1.90/1.20  Index Deletion       : 0.00
% 1.90/1.20  Index Matching       : 0.00
% 1.90/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
