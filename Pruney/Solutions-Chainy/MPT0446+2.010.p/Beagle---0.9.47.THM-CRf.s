%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:27 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   67 (  83 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 ( 122 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r2_hidden(k4_tarski(A,B),C)
         => ( r2_hidden(A,k3_relat_1(C))
            & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(B,k2_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_50,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(c_40,plain,
    ( ~ r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_88,plain,(
    ~ r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_44,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_175,plain,(
    ! [A_84] :
      ( k2_xboole_0(k1_relat_1(A_84),k2_relat_1(A_84)) = k3_relat_1(A_84)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_190,plain,(
    ! [A_84] :
      ( r1_tarski(k1_relat_1(A_84),k3_relat_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_8])).

tff(c_42,plain,(
    r2_hidden(k4_tarski('#skF_2','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_887,plain,(
    ! [A_170,C_171,B_172] :
      ( r2_hidden(A_170,k1_relat_1(C_171))
      | ~ r2_hidden(k4_tarski(A_170,B_172),C_171)
      | ~ v1_relat_1(C_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_957,plain,
    ( r2_hidden('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_887])).

tff(c_977,plain,(
    r2_hidden('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_957])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1003,plain,(
    ! [B_176] :
      ( r2_hidden('#skF_2',B_176)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_176) ) ),
    inference(resolution,[status(thm)],[c_977,c_2])).

tff(c_1011,plain,
    ( r2_hidden('#skF_2',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_190,c_1003])).

tff(c_1035,plain,(
    r2_hidden('#skF_2',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1011])).

tff(c_1037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_1035])).

tff(c_1038,plain,(
    ~ r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_34,plain,(
    ! [A_37] :
      ( k2_xboole_0(k1_relat_1(A_37),k2_relat_1(A_37)) = k3_relat_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_22,plain,(
    ! [A_30,B_31] : k3_tarski(k2_tarski(A_30,B_31)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_32] : r1_tarski(A_32,k1_zfmisc_1(k3_tarski(A_32))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1085,plain,(
    ! [B_194,C_195,A_196] :
      ( r2_hidden(B_194,C_195)
      | ~ r1_tarski(k2_tarski(A_196,B_194),C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1097,plain,(
    ! [B_194,A_196] : r2_hidden(B_194,k1_zfmisc_1(k3_tarski(k2_tarski(A_196,B_194)))) ),
    inference(resolution,[status(thm)],[c_24,c_1085])).

tff(c_1123,plain,(
    ! [B_200,A_201] : r2_hidden(B_200,k1_zfmisc_1(k2_xboole_0(A_201,B_200))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_1097])).

tff(c_32,plain,(
    ! [A_36] : k3_tarski(k1_zfmisc_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_69,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,k3_tarski(B_49))
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_72,plain,(
    ! [A_48,A_36] :
      ( r1_tarski(A_48,A_36)
      | ~ r2_hidden(A_48,k1_zfmisc_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_69])).

tff(c_1131,plain,(
    ! [B_202,A_203] : r1_tarski(B_202,k2_xboole_0(A_203,B_202)) ),
    inference(resolution,[status(thm)],[c_1123,c_72])).

tff(c_1142,plain,(
    ! [A_37] :
      ( r1_tarski(k2_relat_1(A_37),k3_relat_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1131])).

tff(c_1526,plain,(
    ! [B_241,C_242,A_243] :
      ( r2_hidden(B_241,k2_relat_1(C_242))
      | ~ r2_hidden(k4_tarski(A_243,B_241),C_242)
      | ~ v1_relat_1(C_242) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1564,plain,
    ( r2_hidden('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_1526])).

tff(c_1576,plain,(
    r2_hidden('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1564])).

tff(c_1580,plain,(
    ! [B_244] :
      ( r2_hidden('#skF_3',B_244)
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_244) ) ),
    inference(resolution,[status(thm)],[c_1576,c_2])).

tff(c_1584,plain,
    ( r2_hidden('#skF_3',k3_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1142,c_1580])).

tff(c_1607,plain,(
    r2_hidden('#skF_3',k3_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_1584])).

tff(c_1609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1038,c_1607])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.55  
% 3.50/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.55  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.50/1.55  
% 3.50/1.55  %Foreground sorts:
% 3.50/1.55  
% 3.50/1.55  
% 3.50/1.55  %Background operators:
% 3.50/1.55  
% 3.50/1.55  
% 3.50/1.55  %Foreground operators:
% 3.50/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.50/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.50/1.55  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.50/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.50/1.55  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.50/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.50/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.55  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.50/1.55  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.50/1.55  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.50/1.55  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.50/1.55  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.50/1.55  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.50/1.55  
% 3.50/1.56  tff(f_81, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 3.50/1.56  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 3.50/1.56  tff(f_34, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.50/1.56  tff(f_72, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k1_relat_1(C)) & r2_hidden(B, k2_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_relat_1)).
% 3.50/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.50/1.56  tff(f_50, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.50/1.56  tff(f_52, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 3.50/1.56  tff(f_58, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.50/1.56  tff(f_60, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 3.50/1.56  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 3.50/1.56  tff(c_40, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.56  tff(c_88, plain, (~r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_40])).
% 3.50/1.56  tff(c_44, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.56  tff(c_175, plain, (![A_84]: (k2_xboole_0(k1_relat_1(A_84), k2_relat_1(A_84))=k3_relat_1(A_84) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.50/1.56  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.50/1.56  tff(c_190, plain, (![A_84]: (r1_tarski(k1_relat_1(A_84), k3_relat_1(A_84)) | ~v1_relat_1(A_84))), inference(superposition, [status(thm), theory('equality')], [c_175, c_8])).
% 3.50/1.56  tff(c_42, plain, (r2_hidden(k4_tarski('#skF_2', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.50/1.56  tff(c_887, plain, (![A_170, C_171, B_172]: (r2_hidden(A_170, k1_relat_1(C_171)) | ~r2_hidden(k4_tarski(A_170, B_172), C_171) | ~v1_relat_1(C_171))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.50/1.56  tff(c_957, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_887])).
% 3.50/1.56  tff(c_977, plain, (r2_hidden('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_957])).
% 3.50/1.56  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.50/1.56  tff(c_1003, plain, (![B_176]: (r2_hidden('#skF_2', B_176) | ~r1_tarski(k1_relat_1('#skF_4'), B_176))), inference(resolution, [status(thm)], [c_977, c_2])).
% 3.50/1.56  tff(c_1011, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_190, c_1003])).
% 3.50/1.56  tff(c_1035, plain, (r2_hidden('#skF_2', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1011])).
% 3.50/1.56  tff(c_1037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_1035])).
% 3.50/1.56  tff(c_1038, plain, (~r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_40])).
% 3.50/1.56  tff(c_34, plain, (![A_37]: (k2_xboole_0(k1_relat_1(A_37), k2_relat_1(A_37))=k3_relat_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.50/1.56  tff(c_22, plain, (![A_30, B_31]: (k3_tarski(k2_tarski(A_30, B_31))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.50/1.56  tff(c_24, plain, (![A_32]: (r1_tarski(A_32, k1_zfmisc_1(k3_tarski(A_32))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.50/1.56  tff(c_1085, plain, (![B_194, C_195, A_196]: (r2_hidden(B_194, C_195) | ~r1_tarski(k2_tarski(A_196, B_194), C_195))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.56  tff(c_1097, plain, (![B_194, A_196]: (r2_hidden(B_194, k1_zfmisc_1(k3_tarski(k2_tarski(A_196, B_194)))))), inference(resolution, [status(thm)], [c_24, c_1085])).
% 3.50/1.56  tff(c_1123, plain, (![B_200, A_201]: (r2_hidden(B_200, k1_zfmisc_1(k2_xboole_0(A_201, B_200))))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_1097])).
% 3.50/1.56  tff(c_32, plain, (![A_36]: (k3_tarski(k1_zfmisc_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.50/1.56  tff(c_69, plain, (![A_48, B_49]: (r1_tarski(A_48, k3_tarski(B_49)) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.50/1.56  tff(c_72, plain, (![A_48, A_36]: (r1_tarski(A_48, A_36) | ~r2_hidden(A_48, k1_zfmisc_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_69])).
% 3.50/1.56  tff(c_1131, plain, (![B_202, A_203]: (r1_tarski(B_202, k2_xboole_0(A_203, B_202)))), inference(resolution, [status(thm)], [c_1123, c_72])).
% 3.50/1.56  tff(c_1142, plain, (![A_37]: (r1_tarski(k2_relat_1(A_37), k3_relat_1(A_37)) | ~v1_relat_1(A_37))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1131])).
% 3.50/1.56  tff(c_1526, plain, (![B_241, C_242, A_243]: (r2_hidden(B_241, k2_relat_1(C_242)) | ~r2_hidden(k4_tarski(A_243, B_241), C_242) | ~v1_relat_1(C_242))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.50/1.56  tff(c_1564, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_1526])).
% 3.50/1.56  tff(c_1576, plain, (r2_hidden('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1564])).
% 3.50/1.56  tff(c_1580, plain, (![B_244]: (r2_hidden('#skF_3', B_244) | ~r1_tarski(k2_relat_1('#skF_4'), B_244))), inference(resolution, [status(thm)], [c_1576, c_2])).
% 3.50/1.56  tff(c_1584, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1142, c_1580])).
% 3.50/1.56  tff(c_1607, plain, (r2_hidden('#skF_3', k3_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_1584])).
% 3.50/1.56  tff(c_1609, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1038, c_1607])).
% 3.50/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.56  
% 3.50/1.56  Inference rules
% 3.50/1.56  ----------------------
% 3.50/1.56  #Ref     : 0
% 3.50/1.56  #Sup     : 325
% 3.50/1.56  #Fact    : 0
% 3.50/1.56  #Define  : 0
% 3.50/1.56  #Split   : 1
% 3.50/1.56  #Chain   : 0
% 3.50/1.56  #Close   : 0
% 3.50/1.56  
% 3.50/1.56  Ordering : KBO
% 3.50/1.56  
% 3.50/1.56  Simplification rules
% 3.50/1.56  ----------------------
% 3.50/1.56  #Subsume      : 9
% 3.50/1.56  #Demod        : 83
% 3.50/1.56  #Tautology    : 61
% 3.50/1.56  #SimpNegUnit  : 2
% 3.50/1.56  #BackRed      : 0
% 3.50/1.56  
% 3.50/1.56  #Partial instantiations: 0
% 3.50/1.56  #Strategies tried      : 1
% 3.50/1.56  
% 3.50/1.56  Timing (in seconds)
% 3.50/1.56  ----------------------
% 3.50/1.56  Preprocessing        : 0.31
% 3.50/1.56  Parsing              : 0.16
% 3.50/1.56  CNF conversion       : 0.02
% 3.50/1.56  Main loop            : 0.50
% 3.50/1.56  Inferencing          : 0.19
% 3.50/1.56  Reduction            : 0.16
% 3.50/1.56  Demodulation         : 0.12
% 3.50/1.57  BG Simplification    : 0.02
% 3.50/1.57  Subsumption          : 0.09
% 3.50/1.57  Abstraction          : 0.02
% 3.50/1.57  MUC search           : 0.00
% 3.50/1.57  Cooper               : 0.00
% 3.50/1.57  Total                : 0.83
% 3.50/1.57  Index Insertion      : 0.00
% 3.50/1.57  Index Deletion       : 0.00
% 3.50/1.57  Index Matching       : 0.00
% 3.50/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
