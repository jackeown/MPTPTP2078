%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:39 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.79s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( ! [C] :
              ~ ( r2_hidden(C,A)
                & k10_relat_1(B,k1_tarski(C)) = k1_xboole_0 )
         => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,k2_relat_1(B))
      <=> k10_relat_1(B,k1_tarski(A)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_1)).

tff(c_65,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,B_34)
      | k4_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_73,plain,(
    k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_40])).

tff(c_24,plain,(
    ! [A_9] : r1_xboole_0(A_9,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    ! [A_42,C_43,B_44] :
      ( ~ r2_hidden(A_42,C_43)
      | ~ r1_xboole_0(k2_tarski(A_42,B_44),C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    ! [A_42] : ~ r2_hidden(A_42,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_135,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_1'(A_65,B_66,C_67),A_65)
      | r2_hidden('#skF_2'(A_65,B_66,C_67),C_67)
      | k4_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_68,C_69] :
      ( r2_hidden('#skF_2'(A_68,A_68,C_69),C_69)
      | k4_xboole_0(A_68,A_68) = C_69 ) ),
    inference(resolution,[status(thm)],[c_135,c_16])).

tff(c_195,plain,(
    ! [A_68] : k4_xboole_0(A_68,A_68) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_177,c_85])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1686,plain,(
    ! [A_166,B_167,A_168,B_169] :
      ( r2_hidden('#skF_2'(A_166,B_167,k4_xboole_0(A_168,B_169)),A_168)
      | r2_hidden('#skF_1'(A_166,B_167,k4_xboole_0(A_168,B_169)),A_166)
      | k4_xboole_0(A_168,B_169) = k4_xboole_0(A_166,B_167) ) ),
    inference(resolution,[status(thm)],[c_135,c_6])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_176,plain,(
    ! [A_65,B_66,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_65,B_66,k4_xboole_0(A_1,B_2)),B_2)
      | r2_hidden('#skF_1'(A_65,B_66,k4_xboole_0(A_1,B_2)),A_65)
      | k4_xboole_0(A_65,B_66) = k4_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_135,c_4])).

tff(c_1701,plain,(
    ! [A_166,B_167,A_168] :
      ( r2_hidden('#skF_1'(A_166,B_167,k4_xboole_0(A_168,A_168)),A_166)
      | k4_xboole_0(A_168,A_168) = k4_xboole_0(A_166,B_167) ) ),
    inference(resolution,[status(thm)],[c_1686,c_176])).

tff(c_1787,plain,(
    ! [A_166,B_167] :
      ( r2_hidden('#skF_1'(A_166,B_167,k1_xboole_0),A_166)
      | k4_xboole_0(A_166,B_167) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_195,c_1701])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_36,plain,(
    ! [A_23,B_24] :
      ( r2_hidden(A_23,k2_relat_1(B_24))
      | k10_relat_1(B_24,k1_tarski(A_23)) = k1_xboole_0
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_126,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63,C_64),B_63)
      | r2_hidden('#skF_2'(A_62,B_63,C_64),C_64)
      | k4_xboole_0(A_62,B_63) = C_64 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3742,plain,(
    ! [A_239,B_240,C_241] :
      ( r2_hidden('#skF_2'(A_239,k2_relat_1(B_240),C_241),C_241)
      | k4_xboole_0(A_239,k2_relat_1(B_240)) = C_241
      | k10_relat_1(B_240,k1_tarski('#skF_1'(A_239,k2_relat_1(B_240),C_241))) = k1_xboole_0
      | ~ v1_relat_1(B_240) ) ),
    inference(resolution,[status(thm)],[c_36,c_126])).

tff(c_42,plain,(
    ! [C_26] :
      ( k10_relat_1('#skF_4',k1_tarski(C_26)) != k1_xboole_0
      | ~ r2_hidden(C_26,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_3788,plain,(
    ! [A_239,C_241] :
      ( ~ r2_hidden('#skF_1'(A_239,k2_relat_1('#skF_4'),C_241),'#skF_3')
      | r2_hidden('#skF_2'(A_239,k2_relat_1('#skF_4'),C_241),C_241)
      | k4_xboole_0(A_239,k2_relat_1('#skF_4')) = C_241
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3742,c_42])).

tff(c_4379,plain,(
    ! [A_250,C_251] :
      ( ~ r2_hidden('#skF_1'(A_250,k2_relat_1('#skF_4'),C_251),'#skF_3')
      | r2_hidden('#skF_2'(A_250,k2_relat_1('#skF_4'),C_251),C_251)
      | k4_xboole_0(A_250,k2_relat_1('#skF_4')) = C_251 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3788])).

tff(c_4385,plain,
    ( r2_hidden('#skF_2'('#skF_3',k2_relat_1('#skF_4'),k1_xboole_0),k1_xboole_0)
    | k4_xboole_0('#skF_3',k2_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1787,c_4379])).

tff(c_4402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_73,c_85,c_4385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:53:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.86  
% 4.47/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.86  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 4.47/1.86  
% 4.47/1.86  %Foreground sorts:
% 4.47/1.86  
% 4.47/1.86  
% 4.47/1.86  %Background operators:
% 4.47/1.86  
% 4.47/1.86  
% 4.47/1.86  %Foreground operators:
% 4.47/1.86  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.47/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.86  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.47/1.86  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.47/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.47/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.47/1.86  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.47/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.86  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.47/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.47/1.86  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.47/1.86  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.47/1.86  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.47/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.86  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.47/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.86  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.47/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.47/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.86  
% 4.79/1.87  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.79/1.87  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((![C]: ~(r2_hidden(C, A) & (k10_relat_1(B, k1_tarski(C)) = k1_xboole_0))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_funct_1)).
% 4.79/1.87  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.79/1.87  tff(f_54, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 4.79/1.87  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.79/1.87  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, k2_relat_1(B)) <=> ~(k10_relat_1(B, k1_tarski(A)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_1)).
% 4.79/1.87  tff(c_65, plain, (![A_33, B_34]: (r1_tarski(A_33, B_34) | k4_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.79/1.87  tff(c_40, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.79/1.87  tff(c_73, plain, (k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_40])).
% 4.79/1.87  tff(c_24, plain, (![A_9]: (r1_xboole_0(A_9, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.79/1.87  tff(c_77, plain, (![A_42, C_43, B_44]: (~r2_hidden(A_42, C_43) | ~r1_xboole_0(k2_tarski(A_42, B_44), C_43))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.79/1.87  tff(c_85, plain, (![A_42]: (~r2_hidden(A_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_77])).
% 4.79/1.87  tff(c_135, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_1'(A_65, B_66, C_67), A_65) | r2_hidden('#skF_2'(A_65, B_66, C_67), C_67) | k4_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.79/1.87  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.79/1.87  tff(c_177, plain, (![A_68, C_69]: (r2_hidden('#skF_2'(A_68, A_68, C_69), C_69) | k4_xboole_0(A_68, A_68)=C_69)), inference(resolution, [status(thm)], [c_135, c_16])).
% 4.79/1.87  tff(c_195, plain, (![A_68]: (k4_xboole_0(A_68, A_68)=k1_xboole_0)), inference(resolution, [status(thm)], [c_177, c_85])).
% 4.79/1.87  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.79/1.87  tff(c_1686, plain, (![A_166, B_167, A_168, B_169]: (r2_hidden('#skF_2'(A_166, B_167, k4_xboole_0(A_168, B_169)), A_168) | r2_hidden('#skF_1'(A_166, B_167, k4_xboole_0(A_168, B_169)), A_166) | k4_xboole_0(A_168, B_169)=k4_xboole_0(A_166, B_167))), inference(resolution, [status(thm)], [c_135, c_6])).
% 4.79/1.87  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.79/1.87  tff(c_176, plain, (![A_65, B_66, A_1, B_2]: (~r2_hidden('#skF_2'(A_65, B_66, k4_xboole_0(A_1, B_2)), B_2) | r2_hidden('#skF_1'(A_65, B_66, k4_xboole_0(A_1, B_2)), A_65) | k4_xboole_0(A_65, B_66)=k4_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_135, c_4])).
% 4.79/1.87  tff(c_1701, plain, (![A_166, B_167, A_168]: (r2_hidden('#skF_1'(A_166, B_167, k4_xboole_0(A_168, A_168)), A_166) | k4_xboole_0(A_168, A_168)=k4_xboole_0(A_166, B_167))), inference(resolution, [status(thm)], [c_1686, c_176])).
% 4.79/1.87  tff(c_1787, plain, (![A_166, B_167]: (r2_hidden('#skF_1'(A_166, B_167, k1_xboole_0), A_166) | k4_xboole_0(A_166, B_167)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_195, c_1701])).
% 4.79/1.87  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.79/1.87  tff(c_36, plain, (![A_23, B_24]: (r2_hidden(A_23, k2_relat_1(B_24)) | k10_relat_1(B_24, k1_tarski(A_23))=k1_xboole_0 | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.79/1.87  tff(c_126, plain, (![A_62, B_63, C_64]: (~r2_hidden('#skF_1'(A_62, B_63, C_64), B_63) | r2_hidden('#skF_2'(A_62, B_63, C_64), C_64) | k4_xboole_0(A_62, B_63)=C_64)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.79/1.87  tff(c_3742, plain, (![A_239, B_240, C_241]: (r2_hidden('#skF_2'(A_239, k2_relat_1(B_240), C_241), C_241) | k4_xboole_0(A_239, k2_relat_1(B_240))=C_241 | k10_relat_1(B_240, k1_tarski('#skF_1'(A_239, k2_relat_1(B_240), C_241)))=k1_xboole_0 | ~v1_relat_1(B_240))), inference(resolution, [status(thm)], [c_36, c_126])).
% 4.79/1.87  tff(c_42, plain, (![C_26]: (k10_relat_1('#skF_4', k1_tarski(C_26))!=k1_xboole_0 | ~r2_hidden(C_26, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.79/1.87  tff(c_3788, plain, (![A_239, C_241]: (~r2_hidden('#skF_1'(A_239, k2_relat_1('#skF_4'), C_241), '#skF_3') | r2_hidden('#skF_2'(A_239, k2_relat_1('#skF_4'), C_241), C_241) | k4_xboole_0(A_239, k2_relat_1('#skF_4'))=C_241 | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3742, c_42])).
% 4.79/1.87  tff(c_4379, plain, (![A_250, C_251]: (~r2_hidden('#skF_1'(A_250, k2_relat_1('#skF_4'), C_251), '#skF_3') | r2_hidden('#skF_2'(A_250, k2_relat_1('#skF_4'), C_251), C_251) | k4_xboole_0(A_250, k2_relat_1('#skF_4'))=C_251)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3788])).
% 4.79/1.87  tff(c_4385, plain, (r2_hidden('#skF_2'('#skF_3', k2_relat_1('#skF_4'), k1_xboole_0), k1_xboole_0) | k4_xboole_0('#skF_3', k2_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1787, c_4379])).
% 4.79/1.87  tff(c_4402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_73, c_85, c_4385])).
% 4.79/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.79/1.87  
% 4.79/1.87  Inference rules
% 4.79/1.87  ----------------------
% 4.79/1.87  #Ref     : 0
% 4.79/1.87  #Sup     : 1011
% 4.79/1.87  #Fact    : 0
% 4.79/1.87  #Define  : 0
% 4.79/1.87  #Split   : 0
% 4.79/1.87  #Chain   : 0
% 4.79/1.87  #Close   : 0
% 4.79/1.87  
% 4.79/1.87  Ordering : KBO
% 4.79/1.87  
% 4.79/1.87  Simplification rules
% 4.79/1.87  ----------------------
% 4.79/1.87  #Subsume      : 355
% 4.79/1.87  #Demod        : 834
% 4.79/1.87  #Tautology    : 338
% 4.79/1.87  #SimpNegUnit  : 33
% 4.79/1.87  #BackRed      : 3
% 4.79/1.87  
% 4.79/1.87  #Partial instantiations: 0
% 4.79/1.87  #Strategies tried      : 1
% 4.79/1.87  
% 4.79/1.87  Timing (in seconds)
% 4.79/1.87  ----------------------
% 4.79/1.87  Preprocessing        : 0.30
% 4.79/1.87  Parsing              : 0.16
% 4.79/1.87  CNF conversion       : 0.02
% 4.79/1.87  Main loop            : 0.81
% 4.79/1.87  Inferencing          : 0.29
% 4.79/1.87  Reduction            : 0.28
% 4.79/1.87  Demodulation         : 0.20
% 4.79/1.87  BG Simplification    : 0.03
% 4.79/1.87  Subsumption          : 0.16
% 4.79/1.87  Abstraction          : 0.05
% 4.79/1.87  MUC search           : 0.00
% 4.79/1.87  Cooper               : 0.00
% 4.79/1.87  Total                : 1.13
% 4.79/1.87  Index Insertion      : 0.00
% 4.79/1.87  Index Deletion       : 0.00
% 4.79/1.87  Index Matching       : 0.00
% 4.79/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
