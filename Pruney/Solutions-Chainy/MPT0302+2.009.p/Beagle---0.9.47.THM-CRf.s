%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:47 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.97s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 135 expanded)
%              Number of leaves         :   29 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   87 ( 256 expanded)
%              Number of equality atoms :   17 (  71 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_64,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_490,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( r2_hidden(k4_tarski(A_138,B_139),k2_zfmisc_1(C_140,D_141))
      | ~ r2_hidden(B_139,D_141)
      | ~ r2_hidden(A_138,C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    k2_zfmisc_1('#skF_11','#skF_10') = k2_zfmisc_1('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_372,plain,(
    ! [A_115,C_116,B_117,D_118] :
      ( r2_hidden(A_115,C_116)
      | ~ r2_hidden(k4_tarski(A_115,B_117),k2_zfmisc_1(C_116,D_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_375,plain,(
    ! [A_115,B_117] :
      ( r2_hidden(A_115,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_115,B_117),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_372])).

tff(c_519,plain,(
    ! [A_138,B_139] :
      ( r2_hidden(A_138,'#skF_11')
      | ~ r2_hidden(B_139,'#skF_11')
      | ~ r2_hidden(A_138,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_490,c_375])).

tff(c_529,plain,(
    ! [B_142] : ~ r2_hidden(B_142,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_549,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_529])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_556,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_549,c_12])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_556])).

tff(c_588,plain,(
    ! [A_145] :
      ( r2_hidden(A_145,'#skF_11')
      | ~ r2_hidden(A_145,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_602,plain,(
    ! [A_146] :
      ( r1_tarski(A_146,'#skF_11')
      | ~ r2_hidden('#skF_2'(A_146,'#skF_11'),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_588,c_8])).

tff(c_612,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_602])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( B_17 = A_16
      | ~ r1_tarski(B_17,A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_622,plain,
    ( '#skF_11' = '#skF_10'
    | ~ r1_tarski('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_612,c_18])).

tff(c_629,plain,(
    ~ r1_tarski('#skF_11','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_622])).

tff(c_630,plain,(
    ! [A_147,B_148,D_149] :
      ( r2_hidden('#skF_9'(A_147,B_148,k2_zfmisc_1(A_147,B_148),D_149),B_148)
      | ~ r2_hidden(D_149,k2_zfmisc_1(A_147,B_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_681,plain,(
    ! [B_151,D_152,A_153] :
      ( ~ v1_xboole_0(B_151)
      | ~ r2_hidden(D_152,k2_zfmisc_1(A_153,B_151)) ) ),
    inference(resolution,[status(thm)],[c_630,c_2])).

tff(c_710,plain,(
    ! [D_152] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(D_152,k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_681])).

tff(c_726,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_710])).

tff(c_361,plain,(
    ! [B_111,D_112,A_113,C_114] :
      ( r2_hidden(B_111,D_112)
      | ~ r2_hidden(k4_tarski(A_113,B_111),k2_zfmisc_1(C_114,D_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_364,plain,(
    ! [B_111,A_113] :
      ( r2_hidden(B_111,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_113,B_111),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_361])).

tff(c_520,plain,(
    ! [B_139,A_138] :
      ( r2_hidden(B_139,'#skF_10')
      | ~ r2_hidden(B_139,'#skF_11')
      | ~ r2_hidden(A_138,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_490,c_364])).

tff(c_953,plain,(
    ! [A_174] : ~ r2_hidden(A_174,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_520])).

tff(c_977,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_953])).

tff(c_986,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_726,c_977])).

tff(c_988,plain,(
    ! [B_175] :
      ( r2_hidden(B_175,'#skF_10')
      | ~ r2_hidden(B_175,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_520])).

tff(c_1292,plain,(
    ! [B_194] :
      ( r2_hidden('#skF_2'('#skF_11',B_194),'#skF_10')
      | r1_tarski('#skF_11',B_194) ) ),
    inference(resolution,[status(thm)],[c_10,c_988])).

tff(c_1302,plain,(
    r1_tarski('#skF_11','#skF_10') ),
    inference(resolution,[status(thm)],[c_1292,c_8])).

tff(c_1312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_629,c_629,c_1302])).

tff(c_1314,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_710])).

tff(c_1358,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1314,c_12])).

tff(c_1364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1358])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:53:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.96  
% 3.82/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.97  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_2
% 3.82/1.97  
% 3.82/1.97  %Foreground sorts:
% 3.82/1.97  
% 3.82/1.97  
% 3.82/1.97  %Background operators:
% 3.82/1.97  
% 3.82/1.97  
% 3.82/1.97  %Foreground operators:
% 3.82/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.82/1.97  tff('#skF_11', type, '#skF_11': $i).
% 3.82/1.97  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.82/1.97  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.82/1.97  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.82/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.97  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 3.82/1.97  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.82/1.97  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.82/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.97  tff('#skF_10', type, '#skF_10': $i).
% 3.82/1.97  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.82/1.97  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.82/1.97  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.82/1.97  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.82/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.82/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.97  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.82/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.82/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.82/1.97  
% 3.97/1.99  tff(f_99, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 3.97/1.99  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.97/1.99  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.97/1.99  tff(f_84, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.97/1.99  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.97/1.99  tff(f_62, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.97/1.99  tff(f_78, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.97/1.99  tff(c_68, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.97/1.99  tff(c_64, plain, ('#skF_11'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.97/1.99  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.97/1.99  tff(c_66, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.97/1.99  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.97/1.99  tff(c_490, plain, (![A_138, B_139, C_140, D_141]: (r2_hidden(k4_tarski(A_138, B_139), k2_zfmisc_1(C_140, D_141)) | ~r2_hidden(B_139, D_141) | ~r2_hidden(A_138, C_140))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.97/1.99  tff(c_70, plain, (k2_zfmisc_1('#skF_11', '#skF_10')=k2_zfmisc_1('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.97/1.99  tff(c_372, plain, (![A_115, C_116, B_117, D_118]: (r2_hidden(A_115, C_116) | ~r2_hidden(k4_tarski(A_115, B_117), k2_zfmisc_1(C_116, D_118)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.97/1.99  tff(c_375, plain, (![A_115, B_117]: (r2_hidden(A_115, '#skF_11') | ~r2_hidden(k4_tarski(A_115, B_117), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_372])).
% 3.97/1.99  tff(c_519, plain, (![A_138, B_139]: (r2_hidden(A_138, '#skF_11') | ~r2_hidden(B_139, '#skF_11') | ~r2_hidden(A_138, '#skF_10'))), inference(resolution, [status(thm)], [c_490, c_375])).
% 3.97/1.99  tff(c_529, plain, (![B_142]: (~r2_hidden(B_142, '#skF_11'))), inference(splitLeft, [status(thm)], [c_519])).
% 3.97/1.99  tff(c_549, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_529])).
% 3.97/1.99  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.97/1.99  tff(c_556, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_549, c_12])).
% 3.97/1.99  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_556])).
% 3.97/1.99  tff(c_588, plain, (![A_145]: (r2_hidden(A_145, '#skF_11') | ~r2_hidden(A_145, '#skF_10'))), inference(splitRight, [status(thm)], [c_519])).
% 3.97/1.99  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.97/1.99  tff(c_602, plain, (![A_146]: (r1_tarski(A_146, '#skF_11') | ~r2_hidden('#skF_2'(A_146, '#skF_11'), '#skF_10'))), inference(resolution, [status(thm)], [c_588, c_8])).
% 3.97/1.99  tff(c_612, plain, (r1_tarski('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_10, c_602])).
% 3.97/1.99  tff(c_18, plain, (![B_17, A_16]: (B_17=A_16 | ~r1_tarski(B_17, A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.97/1.99  tff(c_622, plain, ('#skF_11'='#skF_10' | ~r1_tarski('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_612, c_18])).
% 3.97/1.99  tff(c_629, plain, (~r1_tarski('#skF_11', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_64, c_622])).
% 3.97/1.99  tff(c_630, plain, (![A_147, B_148, D_149]: (r2_hidden('#skF_9'(A_147, B_148, k2_zfmisc_1(A_147, B_148), D_149), B_148) | ~r2_hidden(D_149, k2_zfmisc_1(A_147, B_148)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.97/1.99  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.97/1.99  tff(c_681, plain, (![B_151, D_152, A_153]: (~v1_xboole_0(B_151) | ~r2_hidden(D_152, k2_zfmisc_1(A_153, B_151)))), inference(resolution, [status(thm)], [c_630, c_2])).
% 3.97/1.99  tff(c_710, plain, (![D_152]: (~v1_xboole_0('#skF_10') | ~r2_hidden(D_152, k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_681])).
% 3.97/1.99  tff(c_726, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_710])).
% 3.97/1.99  tff(c_361, plain, (![B_111, D_112, A_113, C_114]: (r2_hidden(B_111, D_112) | ~r2_hidden(k4_tarski(A_113, B_111), k2_zfmisc_1(C_114, D_112)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.97/1.99  tff(c_364, plain, (![B_111, A_113]: (r2_hidden(B_111, '#skF_10') | ~r2_hidden(k4_tarski(A_113, B_111), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_70, c_361])).
% 3.97/1.99  tff(c_520, plain, (![B_139, A_138]: (r2_hidden(B_139, '#skF_10') | ~r2_hidden(B_139, '#skF_11') | ~r2_hidden(A_138, '#skF_10'))), inference(resolution, [status(thm)], [c_490, c_364])).
% 3.97/1.99  tff(c_953, plain, (![A_174]: (~r2_hidden(A_174, '#skF_10'))), inference(splitLeft, [status(thm)], [c_520])).
% 3.97/1.99  tff(c_977, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_953])).
% 3.97/1.99  tff(c_986, plain, $false, inference(negUnitSimplification, [status(thm)], [c_726, c_977])).
% 3.97/1.99  tff(c_988, plain, (![B_175]: (r2_hidden(B_175, '#skF_10') | ~r2_hidden(B_175, '#skF_11'))), inference(splitRight, [status(thm)], [c_520])).
% 3.97/1.99  tff(c_1292, plain, (![B_194]: (r2_hidden('#skF_2'('#skF_11', B_194), '#skF_10') | r1_tarski('#skF_11', B_194))), inference(resolution, [status(thm)], [c_10, c_988])).
% 3.97/1.99  tff(c_1302, plain, (r1_tarski('#skF_11', '#skF_10')), inference(resolution, [status(thm)], [c_1292, c_8])).
% 3.97/1.99  tff(c_1312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_629, c_629, c_1302])).
% 3.97/1.99  tff(c_1314, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_710])).
% 3.97/1.99  tff(c_1358, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_1314, c_12])).
% 3.97/1.99  tff(c_1364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_1358])).
% 3.97/1.99  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.99  
% 3.97/1.99  Inference rules
% 3.97/1.99  ----------------------
% 3.97/1.99  #Ref     : 0
% 3.97/1.99  #Sup     : 286
% 3.97/1.99  #Fact    : 0
% 3.97/1.99  #Define  : 0
% 3.97/1.99  #Split   : 4
% 3.97/1.99  #Chain   : 0
% 3.97/1.99  #Close   : 0
% 3.97/1.99  
% 3.97/1.99  Ordering : KBO
% 3.97/1.99  
% 3.97/1.99  Simplification rules
% 3.97/1.99  ----------------------
% 3.97/1.99  #Subsume      : 95
% 3.97/1.99  #Demod        : 57
% 3.97/1.99  #Tautology    : 58
% 3.97/1.99  #SimpNegUnit  : 19
% 3.97/1.99  #BackRed      : 2
% 3.97/1.99  
% 3.97/1.99  #Partial instantiations: 0
% 3.97/1.99  #Strategies tried      : 1
% 3.97/1.99  
% 3.97/1.99  Timing (in seconds)
% 3.97/1.99  ----------------------
% 3.97/1.99  Preprocessing        : 0.48
% 3.97/1.99  Parsing              : 0.23
% 3.97/1.99  CNF conversion       : 0.04
% 3.97/1.99  Main loop            : 0.62
% 3.97/1.99  Inferencing          : 0.22
% 3.97/1.99  Reduction            : 0.17
% 3.97/1.99  Demodulation         : 0.12
% 3.97/2.00  BG Simplification    : 0.03
% 3.97/2.00  Subsumption          : 0.14
% 3.97/2.00  Abstraction          : 0.03
% 3.97/2.00  MUC search           : 0.00
% 3.97/2.00  Cooper               : 0.00
% 3.97/2.00  Total                : 1.15
% 3.97/2.00  Index Insertion      : 0.00
% 3.97/2.00  Index Deletion       : 0.00
% 3.97/2.00  Index Matching       : 0.00
% 3.97/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
