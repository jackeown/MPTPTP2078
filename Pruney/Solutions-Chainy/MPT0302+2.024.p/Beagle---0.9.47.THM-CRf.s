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
% DateTime   : Thu Dec  3 09:53:49 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 113 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 201 expanded)
%              Number of equality atoms :   20 (  55 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_77,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_54,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_283,plain,(
    ! [A_99,B_100,C_101,D_102] :
      ( r2_hidden(k4_tarski(A_99,B_100),k2_zfmisc_1(C_101,D_102))
      | ~ r2_hidden(B_100,D_102)
      | ~ r2_hidden(A_99,C_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,(
    k2_zfmisc_1('#skF_7','#skF_8') = k2_zfmisc_1('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_202,plain,(
    ! [B_76,D_77,A_78,C_79] :
      ( r2_hidden(B_76,D_77)
      | ~ r2_hidden(k4_tarski(A_78,B_76),k2_zfmisc_1(C_79,D_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_205,plain,(
    ! [B_76,A_78] :
      ( r2_hidden(B_76,'#skF_8')
      | ~ r2_hidden(k4_tarski(A_78,B_76),k2_zfmisc_1('#skF_8','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_202])).

tff(c_305,plain,(
    ! [B_100,A_99] :
      ( r2_hidden(B_100,'#skF_8')
      | ~ r2_hidden(B_100,'#skF_7')
      | ~ r2_hidden(A_99,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_283,c_205])).

tff(c_313,plain,(
    ! [A_103] : ~ r2_hidden(A_103,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_340,plain,(
    ! [B_105] : r1_tarski('#skF_8',B_105) ),
    inference(resolution,[status(thm)],[c_6,c_313])).

tff(c_152,plain,(
    ! [A_62,B_63] :
      ( r2_xboole_0(A_62,B_63)
      | B_63 = A_62
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_130,plain,(
    ! [B_58,A_59] :
      ( ~ r2_hidden(B_58,A_59)
      | k4_xboole_0(A_59,k1_tarski(B_58)) != A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_140,plain,(
    ! [B_60] : ~ r2_hidden(B_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_130])).

tff(c_149,plain,(
    ! [A_8] : ~ r2_xboole_0(A_8,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_164,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_152,c_149])).

tff(c_349,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_340,c_164])).

tff(c_355,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_349])).

tff(c_357,plain,(
    ! [B_106] :
      ( r2_hidden(B_106,'#skF_8')
      | ~ r2_hidden(B_106,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_441,plain,(
    ! [B_111] :
      ( r2_hidden('#skF_1'('#skF_7',B_111),'#skF_8')
      | r1_tarski('#skF_7',B_111) ) ),
    inference(resolution,[status(thm)],[c_6,c_357])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_452,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_441,c_4])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_457,plain,(
    ! [A_112,B_113] :
      ( r2_hidden(k4_tarski(A_112,B_113),k2_zfmisc_1('#skF_8','#skF_7'))
      | ~ r2_hidden(B_113,'#skF_8')
      | ~ r2_hidden(A_112,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_283])).

tff(c_44,plain,(
    ! [B_35,D_37,A_34,C_36] :
      ( r2_hidden(B_35,D_37)
      | ~ r2_hidden(k4_tarski(A_34,B_35),k2_zfmisc_1(C_36,D_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_476,plain,(
    ! [B_113,A_112] :
      ( r2_hidden(B_113,'#skF_7')
      | ~ r2_hidden(B_113,'#skF_8')
      | ~ r2_hidden(A_112,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_457,c_44])).

tff(c_495,plain,(
    ! [A_114] : ~ r2_hidden(A_114,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_539,plain,(
    ! [B_118] : r1_tarski('#skF_7',B_118) ),
    inference(resolution,[status(thm)],[c_6,c_495])).

tff(c_548,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_539,c_164])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_548])).

tff(c_556,plain,(
    ! [B_119] :
      ( r2_hidden(B_119,'#skF_7')
      | ~ r2_hidden(B_119,'#skF_8') ) ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( ~ r2_hidden('#skF_2'(A_8,B_9),A_8)
      | ~ r2_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_832,plain,(
    ! [B_138] :
      ( ~ r2_xboole_0('#skF_7',B_138)
      | ~ r2_hidden('#skF_2'('#skF_7',B_138),'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_556,c_14])).

tff(c_847,plain,(
    ~ r2_xboole_0('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_16,c_832])).

tff(c_850,plain,
    ( '#skF_7' = '#skF_8'
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_8,c_847])).

tff(c_853,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_850])).

tff(c_855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_853])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:31:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.95  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.96  
% 3.38/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.38/1.96  %$ r2_xboole_0 > r2_hidden > r1_tarski > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 3.38/1.96  
% 3.38/1.96  %Foreground sorts:
% 3.38/1.96  
% 3.38/1.96  
% 3.38/1.96  %Background operators:
% 3.38/1.96  
% 3.38/1.96  
% 3.38/1.96  %Foreground operators:
% 3.38/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.96  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.96  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.38/1.96  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.96  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.96  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.38/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.96  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.96  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.38/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.96  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.96  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.96  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.38/1.96  tff('#skF_8', type, '#skF_8': $i).
% 3.38/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.96  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.38/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.38/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.96  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.96  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.96  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.38/1.96  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.38/1.96  
% 3.60/1.98  tff(f_86, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 3.60/1.98  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.60/1.98  tff(f_71, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.60/1.98  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.60/1.98  tff(f_49, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.60/1.98  tff(f_51, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.60/1.98  tff(f_77, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.60/1.98  tff(c_54, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.60/1.98  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.98  tff(c_56, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.60/1.98  tff(c_283, plain, (![A_99, B_100, C_101, D_102]: (r2_hidden(k4_tarski(A_99, B_100), k2_zfmisc_1(C_101, D_102)) | ~r2_hidden(B_100, D_102) | ~r2_hidden(A_99, C_101))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.60/1.98  tff(c_60, plain, (k2_zfmisc_1('#skF_7', '#skF_8')=k2_zfmisc_1('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.60/1.98  tff(c_202, plain, (![B_76, D_77, A_78, C_79]: (r2_hidden(B_76, D_77) | ~r2_hidden(k4_tarski(A_78, B_76), k2_zfmisc_1(C_79, D_77)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.60/1.98  tff(c_205, plain, (![B_76, A_78]: (r2_hidden(B_76, '#skF_8') | ~r2_hidden(k4_tarski(A_78, B_76), k2_zfmisc_1('#skF_8', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_202])).
% 3.60/1.98  tff(c_305, plain, (![B_100, A_99]: (r2_hidden(B_100, '#skF_8') | ~r2_hidden(B_100, '#skF_7') | ~r2_hidden(A_99, '#skF_8'))), inference(resolution, [status(thm)], [c_283, c_205])).
% 3.60/1.98  tff(c_313, plain, (![A_103]: (~r2_hidden(A_103, '#skF_8'))), inference(splitLeft, [status(thm)], [c_305])).
% 3.60/1.98  tff(c_340, plain, (![B_105]: (r1_tarski('#skF_8', B_105))), inference(resolution, [status(thm)], [c_6, c_313])).
% 3.60/1.98  tff(c_152, plain, (![A_62, B_63]: (r2_xboole_0(A_62, B_63) | B_63=A_62 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.60/1.98  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.60/1.98  tff(c_18, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.60/1.98  tff(c_130, plain, (![B_58, A_59]: (~r2_hidden(B_58, A_59) | k4_xboole_0(A_59, k1_tarski(B_58))!=A_59)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.60/1.98  tff(c_140, plain, (![B_60]: (~r2_hidden(B_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_130])).
% 3.60/1.98  tff(c_149, plain, (![A_8]: (~r2_xboole_0(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_140])).
% 3.60/1.98  tff(c_164, plain, (![A_62]: (k1_xboole_0=A_62 | ~r1_tarski(A_62, k1_xboole_0))), inference(resolution, [status(thm)], [c_152, c_149])).
% 3.60/1.98  tff(c_349, plain, (k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_340, c_164])).
% 3.60/1.98  tff(c_355, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_349])).
% 3.60/1.98  tff(c_357, plain, (![B_106]: (r2_hidden(B_106, '#skF_8') | ~r2_hidden(B_106, '#skF_7'))), inference(splitRight, [status(thm)], [c_305])).
% 3.60/1.98  tff(c_441, plain, (![B_111]: (r2_hidden('#skF_1'('#skF_7', B_111), '#skF_8') | r1_tarski('#skF_7', B_111))), inference(resolution, [status(thm)], [c_6, c_357])).
% 3.60/1.98  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.60/1.98  tff(c_452, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_441, c_4])).
% 3.60/1.98  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.60/1.98  tff(c_58, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.60/1.98  tff(c_457, plain, (![A_112, B_113]: (r2_hidden(k4_tarski(A_112, B_113), k2_zfmisc_1('#skF_8', '#skF_7')) | ~r2_hidden(B_113, '#skF_8') | ~r2_hidden(A_112, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_60, c_283])).
% 3.60/1.98  tff(c_44, plain, (![B_35, D_37, A_34, C_36]: (r2_hidden(B_35, D_37) | ~r2_hidden(k4_tarski(A_34, B_35), k2_zfmisc_1(C_36, D_37)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.60/1.98  tff(c_476, plain, (![B_113, A_112]: (r2_hidden(B_113, '#skF_7') | ~r2_hidden(B_113, '#skF_8') | ~r2_hidden(A_112, '#skF_7'))), inference(resolution, [status(thm)], [c_457, c_44])).
% 3.60/1.98  tff(c_495, plain, (![A_114]: (~r2_hidden(A_114, '#skF_7'))), inference(splitLeft, [status(thm)], [c_476])).
% 3.60/1.98  tff(c_539, plain, (![B_118]: (r1_tarski('#skF_7', B_118))), inference(resolution, [status(thm)], [c_6, c_495])).
% 3.60/1.98  tff(c_548, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_539, c_164])).
% 3.60/1.98  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_548])).
% 3.60/1.98  tff(c_556, plain, (![B_119]: (r2_hidden(B_119, '#skF_7') | ~r2_hidden(B_119, '#skF_8'))), inference(splitRight, [status(thm)], [c_476])).
% 3.60/1.98  tff(c_14, plain, (![A_8, B_9]: (~r2_hidden('#skF_2'(A_8, B_9), A_8) | ~r2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.60/1.98  tff(c_832, plain, (![B_138]: (~r2_xboole_0('#skF_7', B_138) | ~r2_hidden('#skF_2'('#skF_7', B_138), '#skF_8'))), inference(resolution, [status(thm)], [c_556, c_14])).
% 3.60/1.98  tff(c_847, plain, (~r2_xboole_0('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_16, c_832])).
% 3.60/1.98  tff(c_850, plain, ('#skF_7'='#skF_8' | ~r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_8, c_847])).
% 3.60/1.98  tff(c_853, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_452, c_850])).
% 3.60/1.98  tff(c_855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_853])).
% 3.60/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.60/1.98  
% 3.60/1.98  Inference rules
% 3.60/1.98  ----------------------
% 3.60/1.98  #Ref     : 0
% 3.60/1.98  #Sup     : 176
% 3.60/1.98  #Fact    : 0
% 3.60/1.98  #Define  : 0
% 3.60/1.98  #Split   : 6
% 3.60/1.98  #Chain   : 0
% 3.60/1.98  #Close   : 0
% 3.60/1.98  
% 3.60/1.98  Ordering : KBO
% 3.60/1.98  
% 3.60/1.98  Simplification rules
% 3.60/1.98  ----------------------
% 3.60/1.98  #Subsume      : 29
% 3.60/1.98  #Demod        : 21
% 3.60/1.98  #Tautology    : 38
% 3.60/1.98  #SimpNegUnit  : 9
% 3.60/1.98  #BackRed      : 2
% 3.60/1.98  
% 3.60/1.98  #Partial instantiations: 0
% 3.60/1.98  #Strategies tried      : 1
% 3.60/1.98  
% 3.60/1.98  Timing (in seconds)
% 3.60/1.98  ----------------------
% 3.60/1.99  Preprocessing        : 0.49
% 3.60/1.99  Parsing              : 0.24
% 3.60/1.99  CNF conversion       : 0.04
% 3.60/1.99  Main loop            : 0.55
% 3.60/1.99  Inferencing          : 0.20
% 3.60/1.99  Reduction            : 0.14
% 3.60/1.99  Demodulation         : 0.09
% 3.60/1.99  BG Simplification    : 0.03
% 3.60/1.99  Subsumption          : 0.13
% 3.60/1.99  Abstraction          : 0.02
% 3.60/1.99  MUC search           : 0.00
% 3.60/1.99  Cooper               : 0.00
% 3.60/1.99  Total                : 1.08
% 3.60/1.99  Index Insertion      : 0.00
% 3.60/1.99  Index Deletion       : 0.00
% 3.60/1.99  Index Matching       : 0.00
% 3.60/1.99  BG Taut test         : 0.00
%------------------------------------------------------------------------------
