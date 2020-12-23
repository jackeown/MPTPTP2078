%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:38 EST 2020

% Result     : Theorem 16.89s
% Output     : CNFRefutation 16.99s
% Verified   : 
% Statistics : Number of formulae       :   67 (  98 expanded)
%              Number of leaves         :   32 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   98 ( 173 expanded)
%              Number of equality atoms :   18 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1 > #skF_12 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_87,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(c_66,plain,
    ( k10_relat_1('#skF_12','#skF_11') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_111,plain,(
    r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_60,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11')
    | k10_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_114,plain,(
    k10_relat_1('#skF_12','#skF_11') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_60])).

tff(c_54,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_906,plain,(
    ! [A_200,B_201] :
      ( r2_hidden(k4_tarski('#skF_7'(A_200,B_201),'#skF_6'(A_200,B_201)),A_200)
      | r2_hidden('#skF_8'(A_200,B_201),B_201)
      | k2_relat_1(A_200) = B_201 ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_97,plain,(
    ! [A_79,B_80] : ~ r2_hidden(A_79,k2_zfmisc_1(A_79,B_80)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_100,plain,(
    ! [A_6] : ~ r2_hidden(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_979,plain,(
    ! [B_201] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_201),B_201)
      | k2_relat_1(k1_xboole_0) = B_201 ) ),
    inference(resolution,[status(thm)],[c_906,c_100])).

tff(c_1000,plain,(
    ! [B_202] :
      ( r2_hidden('#skF_8'(k1_xboole_0,B_202),B_202)
      | k1_xboole_0 = B_202 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_979])).

tff(c_58,plain,(
    v1_relat_1('#skF_12') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_10'(A_71,B_72,C_73),B_72)
      | ~ r2_hidden(A_71,k10_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_292,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden('#skF_10'(A_126,B_127,C_128),k2_relat_1(C_128))
      | ~ r2_hidden(A_126,k10_relat_1(C_128,B_127))
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_133,plain,(
    ! [A_90,B_91,C_92] :
      ( ~ r1_xboole_0(A_90,B_91)
      | ~ r2_hidden(C_92,B_91)
      | ~ r2_hidden(C_92,A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_141,plain,(
    ! [C_92] :
      ( ~ r2_hidden(C_92,'#skF_11')
      | ~ r2_hidden(C_92,k2_relat_1('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_111,c_133])).

tff(c_304,plain,(
    ! [A_126,B_127] :
      ( ~ r2_hidden('#skF_10'(A_126,B_127,'#skF_12'),'#skF_11')
      | ~ r2_hidden(A_126,k10_relat_1('#skF_12',B_127))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_292,c_141])).

tff(c_350,plain,(
    ! [A_136,B_137] :
      ( ~ r2_hidden('#skF_10'(A_136,B_137,'#skF_12'),'#skF_11')
      | ~ r2_hidden(A_136,k10_relat_1('#skF_12',B_137)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_304])).

tff(c_354,plain,(
    ! [A_71] :
      ( ~ r2_hidden(A_71,k10_relat_1('#skF_12','#skF_11'))
      | ~ v1_relat_1('#skF_12') ) ),
    inference(resolution,[status(thm)],[c_48,c_350])).

tff(c_357,plain,(
    ! [A_71] : ~ r2_hidden(A_71,k10_relat_1('#skF_12','#skF_11')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_354])).

tff(c_1046,plain,(
    k10_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1000,c_357])).

tff(c_1085,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_1046])).

tff(c_1086,plain,(
    k10_relat_1('#skF_12','#skF_11') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_1094,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_60])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_34,plain,(
    ! [A_52,C_67] :
      ( r2_hidden(k4_tarski('#skF_9'(A_52,k2_relat_1(A_52),C_67),C_67),A_52)
      | ~ r2_hidden(C_67,k2_relat_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1308,plain,(
    ! [D_253,A_254,B_255,E_256] :
      ( r2_hidden(D_253,k10_relat_1(A_254,B_255))
      | ~ r2_hidden(E_256,B_255)
      | ~ r2_hidden(k4_tarski(D_253,E_256),A_254)
      | ~ v1_relat_1(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3925,plain,(
    ! [D_413,A_414,B_415,A_416] :
      ( r2_hidden(D_413,k10_relat_1(A_414,B_415))
      | ~ r2_hidden(k4_tarski(D_413,'#skF_1'(A_416,B_415)),A_414)
      | ~ v1_relat_1(A_414)
      | r1_xboole_0(A_416,B_415) ) ),
    inference(resolution,[status(thm)],[c_4,c_1308])).

tff(c_35462,plain,(
    ! [A_9601,A_9602,B_9603] :
      ( r2_hidden('#skF_9'(A_9601,k2_relat_1(A_9601),'#skF_1'(A_9602,B_9603)),k10_relat_1(A_9601,B_9603))
      | ~ v1_relat_1(A_9601)
      | r1_xboole_0(A_9602,B_9603)
      | ~ r2_hidden('#skF_1'(A_9602,B_9603),k2_relat_1(A_9601)) ) ),
    inference(resolution,[status(thm)],[c_34,c_3925])).

tff(c_35745,plain,(
    ! [A_9602] :
      ( r2_hidden('#skF_9'('#skF_12',k2_relat_1('#skF_12'),'#skF_1'(A_9602,'#skF_11')),k1_xboole_0)
      | ~ v1_relat_1('#skF_12')
      | r1_xboole_0(A_9602,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_9602,'#skF_11'),k2_relat_1('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_35462])).

tff(c_35777,plain,(
    ! [A_9602] :
      ( r2_hidden('#skF_9'('#skF_12',k2_relat_1('#skF_12'),'#skF_1'(A_9602,'#skF_11')),k1_xboole_0)
      | r1_xboole_0(A_9602,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_9602,'#skF_11'),k2_relat_1('#skF_12')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_35745])).

tff(c_35780,plain,(
    ! [A_9639] :
      ( r1_xboole_0(A_9639,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_9639,'#skF_11'),k2_relat_1('#skF_12')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_100,c_35777])).

tff(c_35787,plain,(
    r1_xboole_0(k2_relat_1('#skF_12'),'#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_35780])).

tff(c_35791,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1094,c_1094,c_35787])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:45:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.89/9.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.99/9.27  
% 16.99/9.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.99/9.27  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_4 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1 > #skF_12 > #skF_10
% 16.99/9.27  
% 16.99/9.27  %Foreground sorts:
% 16.99/9.27  
% 16.99/9.27  
% 16.99/9.27  %Background operators:
% 16.99/9.27  
% 16.99/9.27  
% 16.99/9.27  %Foreground operators:
% 16.99/9.27  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.99/9.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.99/9.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.99/9.27  tff('#skF_11', type, '#skF_11': $i).
% 16.99/9.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.99/9.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.99/9.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 16.99/9.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.99/9.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.99/9.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.99/9.27  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 16.99/9.27  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 16.99/9.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.99/9.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 16.99/9.27  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 16.99/9.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.99/9.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.99/9.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.99/9.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.99/9.27  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.99/9.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.99/9.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.99/9.27  tff('#skF_12', type, '#skF_12': $i).
% 16.99/9.27  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 16.99/9.27  
% 16.99/9.29  tff(f_94, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 16.99/9.29  tff(f_87, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 16.99/9.29  tff(f_73, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 16.99/9.29  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 16.99/9.29  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 16.99/9.29  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 16.99/9.29  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 16.99/9.29  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 16.99/9.29  tff(c_66, plain, (k10_relat_1('#skF_12', '#skF_11')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.99/9.29  tff(c_111, plain, (r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(splitLeft, [status(thm)], [c_66])).
% 16.99/9.29  tff(c_60, plain, (~r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11') | k10_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.99/9.29  tff(c_114, plain, (k10_relat_1('#skF_12', '#skF_11')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_111, c_60])).
% 16.99/9.29  tff(c_54, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.99/9.29  tff(c_906, plain, (![A_200, B_201]: (r2_hidden(k4_tarski('#skF_7'(A_200, B_201), '#skF_6'(A_200, B_201)), A_200) | r2_hidden('#skF_8'(A_200, B_201), B_201) | k2_relat_1(A_200)=B_201)), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.99/9.29  tff(c_10, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 16.99/9.29  tff(c_97, plain, (![A_79, B_80]: (~r2_hidden(A_79, k2_zfmisc_1(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.99/9.29  tff(c_100, plain, (![A_6]: (~r2_hidden(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_97])).
% 16.99/9.29  tff(c_979, plain, (![B_201]: (r2_hidden('#skF_8'(k1_xboole_0, B_201), B_201) | k2_relat_1(k1_xboole_0)=B_201)), inference(resolution, [status(thm)], [c_906, c_100])).
% 16.99/9.29  tff(c_1000, plain, (![B_202]: (r2_hidden('#skF_8'(k1_xboole_0, B_202), B_202) | k1_xboole_0=B_202)), inference(demodulation, [status(thm), theory('equality')], [c_54, c_979])).
% 16.99/9.29  tff(c_58, plain, (v1_relat_1('#skF_12')), inference(cnfTransformation, [status(thm)], [f_94])).
% 16.99/9.29  tff(c_48, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_10'(A_71, B_72, C_73), B_72) | ~r2_hidden(A_71, k10_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.99/9.29  tff(c_292, plain, (![A_126, B_127, C_128]: (r2_hidden('#skF_10'(A_126, B_127, C_128), k2_relat_1(C_128)) | ~r2_hidden(A_126, k10_relat_1(C_128, B_127)) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_84])).
% 16.99/9.29  tff(c_133, plain, (![A_90, B_91, C_92]: (~r1_xboole_0(A_90, B_91) | ~r2_hidden(C_92, B_91) | ~r2_hidden(C_92, A_90))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.99/9.29  tff(c_141, plain, (![C_92]: (~r2_hidden(C_92, '#skF_11') | ~r2_hidden(C_92, k2_relat_1('#skF_12')))), inference(resolution, [status(thm)], [c_111, c_133])).
% 16.99/9.29  tff(c_304, plain, (![A_126, B_127]: (~r2_hidden('#skF_10'(A_126, B_127, '#skF_12'), '#skF_11') | ~r2_hidden(A_126, k10_relat_1('#skF_12', B_127)) | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_292, c_141])).
% 16.99/9.29  tff(c_350, plain, (![A_136, B_137]: (~r2_hidden('#skF_10'(A_136, B_137, '#skF_12'), '#skF_11') | ~r2_hidden(A_136, k10_relat_1('#skF_12', B_137)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_304])).
% 16.99/9.29  tff(c_354, plain, (![A_71]: (~r2_hidden(A_71, k10_relat_1('#skF_12', '#skF_11')) | ~v1_relat_1('#skF_12'))), inference(resolution, [status(thm)], [c_48, c_350])).
% 16.99/9.29  tff(c_357, plain, (![A_71]: (~r2_hidden(A_71, k10_relat_1('#skF_12', '#skF_11')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_354])).
% 16.99/9.29  tff(c_1046, plain, (k10_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_1000, c_357])).
% 16.99/9.29  tff(c_1085, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_1046])).
% 16.99/9.29  tff(c_1086, plain, (k10_relat_1('#skF_12', '#skF_11')=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 16.99/9.29  tff(c_1094, plain, (~r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_60])).
% 16.99/9.29  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.99/9.29  tff(c_34, plain, (![A_52, C_67]: (r2_hidden(k4_tarski('#skF_9'(A_52, k2_relat_1(A_52), C_67), C_67), A_52) | ~r2_hidden(C_67, k2_relat_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.99/9.29  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 16.99/9.29  tff(c_1308, plain, (![D_253, A_254, B_255, E_256]: (r2_hidden(D_253, k10_relat_1(A_254, B_255)) | ~r2_hidden(E_256, B_255) | ~r2_hidden(k4_tarski(D_253, E_256), A_254) | ~v1_relat_1(A_254))), inference(cnfTransformation, [status(thm)], [f_65])).
% 16.99/9.29  tff(c_3925, plain, (![D_413, A_414, B_415, A_416]: (r2_hidden(D_413, k10_relat_1(A_414, B_415)) | ~r2_hidden(k4_tarski(D_413, '#skF_1'(A_416, B_415)), A_414) | ~v1_relat_1(A_414) | r1_xboole_0(A_416, B_415))), inference(resolution, [status(thm)], [c_4, c_1308])).
% 16.99/9.29  tff(c_35462, plain, (![A_9601, A_9602, B_9603]: (r2_hidden('#skF_9'(A_9601, k2_relat_1(A_9601), '#skF_1'(A_9602, B_9603)), k10_relat_1(A_9601, B_9603)) | ~v1_relat_1(A_9601) | r1_xboole_0(A_9602, B_9603) | ~r2_hidden('#skF_1'(A_9602, B_9603), k2_relat_1(A_9601)))), inference(resolution, [status(thm)], [c_34, c_3925])).
% 16.99/9.29  tff(c_35745, plain, (![A_9602]: (r2_hidden('#skF_9'('#skF_12', k2_relat_1('#skF_12'), '#skF_1'(A_9602, '#skF_11')), k1_xboole_0) | ~v1_relat_1('#skF_12') | r1_xboole_0(A_9602, '#skF_11') | ~r2_hidden('#skF_1'(A_9602, '#skF_11'), k2_relat_1('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_1086, c_35462])).
% 16.99/9.29  tff(c_35777, plain, (![A_9602]: (r2_hidden('#skF_9'('#skF_12', k2_relat_1('#skF_12'), '#skF_1'(A_9602, '#skF_11')), k1_xboole_0) | r1_xboole_0(A_9602, '#skF_11') | ~r2_hidden('#skF_1'(A_9602, '#skF_11'), k2_relat_1('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_35745])).
% 16.99/9.29  tff(c_35780, plain, (![A_9639]: (r1_xboole_0(A_9639, '#skF_11') | ~r2_hidden('#skF_1'(A_9639, '#skF_11'), k2_relat_1('#skF_12')))), inference(negUnitSimplification, [status(thm)], [c_100, c_35777])).
% 16.99/9.29  tff(c_35787, plain, (r1_xboole_0(k2_relat_1('#skF_12'), '#skF_11')), inference(resolution, [status(thm)], [c_6, c_35780])).
% 16.99/9.29  tff(c_35791, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1094, c_1094, c_35787])).
% 16.99/9.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.99/9.29  
% 16.99/9.29  Inference rules
% 16.99/9.29  ----------------------
% 16.99/9.29  #Ref     : 0
% 16.99/9.29  #Sup     : 7527
% 16.99/9.29  #Fact    : 0
% 16.99/9.29  #Define  : 0
% 16.99/9.29  #Split   : 25
% 16.99/9.29  #Chain   : 0
% 16.99/9.29  #Close   : 0
% 16.99/9.29  
% 16.99/9.29  Ordering : KBO
% 16.99/9.29  
% 16.99/9.29  Simplification rules
% 16.99/9.29  ----------------------
% 16.99/9.29  #Subsume      : 3435
% 16.99/9.29  #Demod        : 2214
% 16.99/9.29  #Tautology    : 716
% 16.99/9.29  #SimpNegUnit  : 348
% 16.99/9.29  #BackRed      : 0
% 16.99/9.29  
% 16.99/9.29  #Partial instantiations: 4518
% 16.99/9.29  #Strategies tried      : 1
% 16.99/9.29  
% 16.99/9.29  Timing (in seconds)
% 16.99/9.29  ----------------------
% 17.08/9.29  Preprocessing        : 0.69
% 17.08/9.29  Parsing              : 0.35
% 17.08/9.29  CNF conversion       : 0.09
% 17.08/9.29  Main loop            : 7.51
% 17.08/9.29  Inferencing          : 1.09
% 17.08/9.29  Reduction            : 0.96
% 17.08/9.29  Demodulation         : 0.61
% 17.08/9.29  BG Simplification    : 0.12
% 17.08/9.29  Subsumption          : 5.14
% 17.08/9.29  Abstraction          : 0.15
% 17.08/9.29  MUC search           : 0.00
% 17.08/9.29  Cooper               : 0.00
% 17.08/9.29  Total                : 8.25
% 17.08/9.29  Index Insertion      : 0.00
% 17.08/9.29  Index Deletion       : 0.00
% 17.08/9.29  Index Matching       : 0.00
% 17.08/9.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
