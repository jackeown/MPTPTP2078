%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:39 EST 2020

% Result     : Theorem 5.27s
% Output     : CNFRefutation 5.27s
% Verified   : 
% Statistics : Number of formulae       :   51 (  82 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   70 ( 149 expanded)
%              Number of equality atoms :   22 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_71,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_75,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_40])).

tff(c_24,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_64,plain,(
    ! [A_30,B_31] :
      ( ~ r2_hidden(A_30,B_31)
      | ~ r1_xboole_0(k1_tarski(A_30),B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_69,plain,(
    ! [A_30] : ~ r2_hidden(A_30,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [A_61,B_62,C_63] :
      ( ~ r2_hidden('#skF_1'(A_61,B_62,C_63),B_62)
      | r2_hidden('#skF_2'(A_61,B_62,C_63),C_63)
      | k4_xboole_0(A_61,B_62) = C_63 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_168,plain,(
    ! [A_64,C_65] :
      ( r2_hidden('#skF_2'(A_64,A_64,C_65),C_65)
      | k4_xboole_0(A_64,A_64) = C_65 ) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_188,plain,(
    ! [A_64] : k4_xboole_0(A_64,A_64) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_168,c_69])).

tff(c_117,plain,(
    ! [A_58,B_59,C_60] :
      ( r2_hidden('#skF_1'(A_58,B_59,C_60),A_58)
      | r2_hidden('#skF_2'(A_58,B_59,C_60),C_60)
      | k4_xboole_0(A_58,B_59) = C_60 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1540,plain,(
    ! [A_158,B_159,A_160,B_161] :
      ( r2_hidden('#skF_2'(A_158,B_159,k4_xboole_0(A_160,B_161)),A_160)
      | r2_hidden('#skF_1'(A_158,B_159,k4_xboole_0(A_160,B_161)),A_158)
      | k4_xboole_0(A_160,B_161) = k4_xboole_0(A_158,B_159) ) ),
    inference(resolution,[status(thm)],[c_117,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_153,plain,(
    ! [A_58,B_59,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_58,B_59,k4_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_58,B_59,k4_xboole_0(A_1,B_2)),A_58)
      | k4_xboole_0(A_58,B_59) = k4_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_1549,plain,(
    ! [A_158,B_159,A_160] :
      ( r2_hidden('#skF_1'(A_158,B_159,k4_xboole_0(A_160,A_160)),A_158)
      | k4_xboole_0(A_160,A_160) = k4_xboole_0(A_158,B_159) ) ),
    inference(resolution,[status(thm)],[c_1540,c_153])).

tff(c_1635,plain,(
    ! [A_158,B_159] :
      ( r2_hidden('#skF_1'(A_158,B_159,k1_xboole_0),A_158)
      | k4_xboole_0(A_158,B_159) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_188,c_1549])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_22,B_23] :
      ( r2_hidden(A_22,k2_relat_1(B_23))
      | k10_relat_1(B_23,k1_tarski(A_22)) = k1_xboole_0
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5493,plain,(
    ! [A_265,B_266,C_267] :
      ( r2_hidden('#skF_2'(A_265,k2_relat_1(B_266),C_267),C_267)
      | k4_xboole_0(A_265,k2_relat_1(B_266)) = C_267
      | k10_relat_1(B_266,k1_tarski('#skF_1'(A_265,k2_relat_1(B_266),C_267))) = k1_xboole_0
      | ~ v1_relat_1(B_266) ) ),
    inference(resolution,[status(thm)],[c_36,c_155])).

tff(c_42,plain,(
    ! [C_25] :
      ( k10_relat_1('#skF_4',k1_tarski(C_25)) != k1_xboole_0
      | ~ r2_hidden(C_25,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_5543,plain,(
    ! [A_265,C_267] :
      ( ~ r2_hidden('#skF_1'(A_265,k2_relat_1('#skF_4'),C_267),'#skF_3')
      | r2_hidden('#skF_2'(A_265,k2_relat_1('#skF_4'),C_267),C_267)
      | k4_xboole_0(A_265,k2_relat_1('#skF_4')) = C_267
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5493,c_42])).

tff(c_6169,plain,(
    ! [A_276,C_277] :
      ( ~ r2_hidden('#skF_1'(A_276,k2_relat_1('#skF_4'),C_277),'#skF_3')
      | r2_hidden('#skF_2'(A_276,k2_relat_1('#skF_4'),C_277),C_277)
      | k4_xboole_0(A_276,k2_relat_1('#skF_4')) = C_277 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_5543])).

tff(c_6178,plain,
    ( r2_hidden('#skF_2'('#skF_3',k2_relat_1('#skF_4'),k1_xboole_0),k1_xboole_0)
    | k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1635,c_6169])).

tff(c_6193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_75,c_69,c_6178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.27/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/2.06  
% 5.27/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/2.07  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 5.27/2.07  
% 5.27/2.07  %Foreground sorts:
% 5.27/2.07  
% 5.27/2.07  
% 5.27/2.07  %Background operators:
% 5.27/2.07  
% 5.27/2.07  
% 5.27/2.07  %Foreground operators:
% 5.27/2.07  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.27/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.27/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.27/2.07  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.27/2.07  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.27/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.27/2.07  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.27/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.27/2.07  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.27/2.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.27/2.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.27/2.07  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.27/2.07  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.27/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.27/2.07  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.27/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.27/2.07  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.27/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.27/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.27/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.27/2.07  
% 5.27/2.08  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.27/2.08  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_funct_1)).
% 5.27/2.08  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 5.27/2.08  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 5.27/2.08  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.27/2.08  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 5.27/2.08  tff(c_71, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.27/2.08  tff(c_40, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.27/2.08  tff(c_75, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_40])).
% 5.27/2.08  tff(c_24, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.27/2.08  tff(c_64, plain, (![A_30, B_31]: (~r2_hidden(A_30, B_31) | ~r1_xboole_0(k1_tarski(A_30), B_31))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.27/2.08  tff(c_69, plain, (![A_30]: (~r2_hidden(A_30, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_64])).
% 5.27/2.08  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.27/2.08  tff(c_155, plain, (![A_61, B_62, C_63]: (~r2_hidden('#skF_1'(A_61, B_62, C_63), B_62) | r2_hidden('#skF_2'(A_61, B_62, C_63), C_63) | k4_xboole_0(A_61, B_62)=C_63)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.27/2.08  tff(c_168, plain, (![A_64, C_65]: (r2_hidden('#skF_2'(A_64, A_64, C_65), C_65) | k4_xboole_0(A_64, A_64)=C_65)), inference(resolution, [status(thm)], [c_18, c_155])).
% 5.27/2.08  tff(c_188, plain, (![A_64]: (k4_xboole_0(A_64, A_64)=k1_xboole_0)), inference(resolution, [status(thm)], [c_168, c_69])).
% 5.27/2.08  tff(c_117, plain, (![A_58, B_59, C_60]: (r2_hidden('#skF_1'(A_58, B_59, C_60), A_58) | r2_hidden('#skF_2'(A_58, B_59, C_60), C_60) | k4_xboole_0(A_58, B_59)=C_60)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.27/2.08  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.27/2.08  tff(c_1540, plain, (![A_158, B_159, A_160, B_161]: (r2_hidden('#skF_2'(A_158, B_159, k4_xboole_0(A_160, B_161)), A_160) | r2_hidden('#skF_1'(A_158, B_159, k4_xboole_0(A_160, B_161)), A_158) | k4_xboole_0(A_160, B_161)=k4_xboole_0(A_158, B_159))), inference(resolution, [status(thm)], [c_117, c_6])).
% 5.27/2.08  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.27/2.08  tff(c_153, plain, (![A_58, B_59, A_1, B_2]: (~r2_hidden('#skF_2'(A_58, B_59, k4_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_58, B_59, k4_xboole_0(A_1, B_2)), A_58) | k4_xboole_0(A_58, B_59)=k4_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_117, c_4])).
% 5.27/2.08  tff(c_1549, plain, (![A_158, B_159, A_160]: (r2_hidden('#skF_1'(A_158, B_159, k4_xboole_0(A_160, A_160)), A_158) | k4_xboole_0(A_160, A_160)=k4_xboole_0(A_158, B_159))), inference(resolution, [status(thm)], [c_1540, c_153])).
% 5.27/2.08  tff(c_1635, plain, (![A_158, B_159]: (r2_hidden('#skF_1'(A_158, B_159, k1_xboole_0), A_158) | k4_xboole_0(A_158, B_159)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_188, c_1549])).
% 5.27/2.08  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.27/2.08  tff(c_36, plain, (![A_22, B_23]: (r2_hidden(A_22, k2_relat_1(B_23)) | k10_relat_1(B_23, k1_tarski(A_22))=k1_xboole_0 | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.27/2.08  tff(c_5493, plain, (![A_265, B_266, C_267]: (r2_hidden('#skF_2'(A_265, k2_relat_1(B_266), C_267), C_267) | k4_xboole_0(A_265, k2_relat_1(B_266))=C_267 | k10_relat_1(B_266, k1_tarski('#skF_1'(A_265, k2_relat_1(B_266), C_267)))=k1_xboole_0 | ~v1_relat_1(B_266))), inference(resolution, [status(thm)], [c_36, c_155])).
% 5.27/2.08  tff(c_42, plain, (![C_25]: (k10_relat_1('#skF_4', k1_tarski(C_25))!=k1_xboole_0 | ~r2_hidden(C_25, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.27/2.08  tff(c_5543, plain, (![A_265, C_267]: (~r2_hidden('#skF_1'(A_265, k2_relat_1('#skF_4'), C_267), '#skF_3') | r2_hidden('#skF_2'(A_265, k2_relat_1('#skF_4'), C_267), C_267) | k4_xboole_0(A_265, k2_relat_1('#skF_4'))=C_267 | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5493, c_42])).
% 5.27/2.08  tff(c_6169, plain, (![A_276, C_277]: (~r2_hidden('#skF_1'(A_276, k2_relat_1('#skF_4'), C_277), '#skF_3') | r2_hidden('#skF_2'(A_276, k2_relat_1('#skF_4'), C_277), C_277) | k4_xboole_0(A_276, k2_relat_1('#skF_4'))=C_277)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_5543])).
% 5.27/2.08  tff(c_6178, plain, (r2_hidden('#skF_2'('#skF_3', k2_relat_1('#skF_4'), k1_xboole_0), k1_xboole_0) | k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1635, c_6169])).
% 5.27/2.08  tff(c_6193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_75, c_69, c_6178])).
% 5.27/2.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.27/2.08  
% 5.27/2.08  Inference rules
% 5.27/2.08  ----------------------
% 5.27/2.08  #Ref     : 0
% 5.27/2.08  #Sup     : 1462
% 5.27/2.08  #Fact    : 0
% 5.27/2.08  #Define  : 0
% 5.27/2.08  #Split   : 0
% 5.27/2.08  #Chain   : 0
% 5.27/2.08  #Close   : 0
% 5.27/2.08  
% 5.27/2.08  Ordering : KBO
% 5.27/2.08  
% 5.27/2.08  Simplification rules
% 5.27/2.08  ----------------------
% 5.27/2.08  #Subsume      : 491
% 5.27/2.08  #Demod        : 1263
% 5.27/2.08  #Tautology    : 507
% 5.27/2.08  #SimpNegUnit  : 41
% 5.27/2.08  #BackRed      : 2
% 5.27/2.08  
% 5.27/2.08  #Partial instantiations: 0
% 5.27/2.08  #Strategies tried      : 1
% 5.27/2.08  
% 5.27/2.08  Timing (in seconds)
% 5.27/2.08  ----------------------
% 5.27/2.08  Preprocessing        : 0.30
% 5.27/2.08  Parsing              : 0.16
% 5.27/2.08  CNF conversion       : 0.02
% 5.27/2.08  Main loop            : 1.00
% 5.27/2.08  Inferencing          : 0.35
% 5.27/2.08  Reduction            : 0.35
% 5.27/2.08  Demodulation         : 0.26
% 5.27/2.08  BG Simplification    : 0.04
% 5.27/2.08  Subsumption          : 0.20
% 5.27/2.08  Abstraction          : 0.06
% 5.27/2.08  MUC search           : 0.00
% 5.27/2.08  Cooper               : 0.00
% 5.27/2.08  Total                : 1.32
% 5.27/2.08  Index Insertion      : 0.00
% 5.27/2.08  Index Deletion       : 0.00
% 5.27/2.08  Index Matching       : 0.00
% 5.27/2.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
