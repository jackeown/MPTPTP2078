%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:48 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 143 expanded)
%              Number of leaves         :   29 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 274 expanded)
%              Number of equality atoms :   19 (  65 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_2

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

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k2_zfmisc_1(B,A)
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t114_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_46,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_54,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( r2_hidden(k4_tarski(A_49,B_50),k2_zfmisc_1(C_51,D_52))
      | ~ r2_hidden(B_50,D_52)
      | ~ r2_hidden(A_49,C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_60,plain,(
    k2_zfmisc_1('#skF_11','#skF_10') = k2_zfmisc_1('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_160,plain,(
    ! [A_86,C_87,B_88,D_89] :
      ( r2_hidden(A_86,C_87)
      | ~ r2_hidden(k4_tarski(A_86,B_88),k2_zfmisc_1(C_87,D_89)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_187,plain,(
    ! [A_98,B_99] :
      ( r2_hidden(A_98,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_98,B_99),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_160])).

tff(c_192,plain,(
    ! [A_49,B_50] :
      ( r2_hidden(A_49,'#skF_11')
      | ~ r2_hidden(B_50,'#skF_11')
      | ~ r2_hidden(A_49,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_48,c_187])).

tff(c_195,plain,(
    ! [B_100] : ~ r2_hidden(B_100,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_192])).

tff(c_215,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_195])).

tff(c_18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,(
    ! [A_69,B_70] :
      ( r2_hidden('#skF_2'(A_69,B_70),A_69)
      | r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_118,plain,(
    ! [A_74,B_75] :
      ( ~ v1_xboole_0(A_74)
      | r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_96,c_2])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_85,plain,(
    ! [A_63,B_64] :
      ( r2_hidden('#skF_3'(A_63,B_64),B_64)
      | ~ r2_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_90,plain,(
    ! [B_65,A_66] :
      ( ~ v1_xboole_0(B_65)
      | ~ r2_xboole_0(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_85,c_2])).

tff(c_94,plain,(
    ! [B_11,A_10] :
      ( ~ v1_xboole_0(B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_123,plain,(
    ! [B_76,A_77] :
      ( ~ v1_xboole_0(B_76)
      | B_76 = A_77
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_118,c_94])).

tff(c_126,plain,(
    ! [A_77] :
      ( k1_xboole_0 = A_77
      | ~ v1_xboole_0(A_77) ) ),
    inference(resolution,[status(thm)],[c_18,c_123])).

tff(c_224,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_215,c_126])).

tff(c_230,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_224])).

tff(c_232,plain,(
    ! [A_103] :
      ( r2_hidden(A_103,'#skF_11')
      | ~ r2_hidden(A_103,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_192])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1064,plain,(
    ! [A_168] :
      ( r1_tarski(A_168,'#skF_11')
      | ~ r2_hidden('#skF_2'(A_168,'#skF_11'),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_232,c_8])).

tff(c_1069,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_10,c_1064])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r2_hidden('#skF_3'(A_12,B_13),B_13)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_257,plain,(
    ! [A_105,B_106,D_107] :
      ( r2_hidden('#skF_9'(A_105,B_106,k2_zfmisc_1(A_105,B_106),D_107),B_106)
      | ~ r2_hidden(D_107,k2_zfmisc_1(A_105,B_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_279,plain,(
    ! [B_108,D_109,A_110] :
      ( ~ v1_xboole_0(B_108)
      | ~ r2_hidden(D_109,k2_zfmisc_1(A_110,B_108)) ) ),
    inference(resolution,[status(thm)],[c_257,c_2])).

tff(c_301,plain,(
    ! [D_109] :
      ( ~ v1_xboole_0('#skF_10')
      | ~ r2_hidden(D_109,k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_279])).

tff(c_312,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_164,plain,(
    ! [B_90,D_91,A_92,C_93] :
      ( r2_hidden(B_90,D_91)
      | ~ r2_hidden(k4_tarski(A_92,B_90),k2_zfmisc_1(C_93,D_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_449,plain,(
    ! [B_123,A_124] :
      ( r2_hidden(B_123,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_124,B_123),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_164])).

tff(c_454,plain,(
    ! [B_50,A_49] :
      ( r2_hidden(B_50,'#skF_10')
      | ~ r2_hidden(B_50,'#skF_11')
      | ~ r2_hidden(A_49,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_48,c_449])).

tff(c_873,plain,(
    ! [A_157] : ~ r2_hidden(A_157,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_454])).

tff(c_909,plain,(
    v1_xboole_0('#skF_10') ),
    inference(resolution,[status(thm)],[c_4,c_873])).

tff(c_920,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_312,c_909])).

tff(c_922,plain,(
    ! [B_158] :
      ( r2_hidden(B_158,'#skF_10')
      | ~ r2_hidden(B_158,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_454])).

tff(c_1155,plain,(
    ! [A_178] :
      ( r2_hidden('#skF_3'(A_178,'#skF_11'),'#skF_10')
      | ~ r2_xboole_0(A_178,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_22,c_922])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( ~ r2_hidden('#skF_3'(A_12,B_13),A_12)
      | ~ r2_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1171,plain,(
    ~ r2_xboole_0('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_1155,c_20])).

tff(c_1175,plain,
    ( '#skF_11' = '#skF_10'
    | ~ r1_tarski('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_12,c_1171])).

tff(c_1178,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_1175])).

tff(c_1180,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1178])).

tff(c_1182,plain,(
    v1_xboole_0('#skF_10') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_1191,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_1182,c_126])).

tff(c_1197,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:48:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.48  
% 3.01/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.48  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_1 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_2
% 3.01/1.48  
% 3.01/1.48  %Foreground sorts:
% 3.01/1.48  
% 3.01/1.48  
% 3.01/1.48  %Background operators:
% 3.01/1.48  
% 3.01/1.48  
% 3.01/1.48  %Foreground operators:
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.01/1.48  tff('#skF_11', type, '#skF_11': $i).
% 3.01/1.48  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.01/1.48  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.01/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.48  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 3.01/1.48  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.01/1.48  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.01/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.48  tff('#skF_10', type, '#skF_10': $i).
% 3.01/1.48  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.01/1.48  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.01/1.48  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.01/1.48  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.01/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.01/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.48  
% 3.01/1.50  tff(f_83, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 3.01/1.50  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.01/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.01/1.50  tff(f_74, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.01/1.50  tff(f_46, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.01/1.50  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.01/1.50  tff(f_56, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 3.01/1.50  tff(f_68, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.01/1.50  tff(c_58, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.01/1.50  tff(c_54, plain, ('#skF_11'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.01/1.50  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.01/1.50  tff(c_56, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.01/1.50  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.01/1.50  tff(c_48, plain, (![A_49, B_50, C_51, D_52]: (r2_hidden(k4_tarski(A_49, B_50), k2_zfmisc_1(C_51, D_52)) | ~r2_hidden(B_50, D_52) | ~r2_hidden(A_49, C_51))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.50  tff(c_60, plain, (k2_zfmisc_1('#skF_11', '#skF_10')=k2_zfmisc_1('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.01/1.50  tff(c_160, plain, (![A_86, C_87, B_88, D_89]: (r2_hidden(A_86, C_87) | ~r2_hidden(k4_tarski(A_86, B_88), k2_zfmisc_1(C_87, D_89)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.50  tff(c_187, plain, (![A_98, B_99]: (r2_hidden(A_98, '#skF_11') | ~r2_hidden(k4_tarski(A_98, B_99), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_160])).
% 3.01/1.50  tff(c_192, plain, (![A_49, B_50]: (r2_hidden(A_49, '#skF_11') | ~r2_hidden(B_50, '#skF_11') | ~r2_hidden(A_49, '#skF_10'))), inference(resolution, [status(thm)], [c_48, c_187])).
% 3.01/1.50  tff(c_195, plain, (![B_100]: (~r2_hidden(B_100, '#skF_11'))), inference(splitLeft, [status(thm)], [c_192])).
% 3.01/1.50  tff(c_215, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_195])).
% 3.01/1.50  tff(c_18, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.01/1.50  tff(c_96, plain, (![A_69, B_70]: (r2_hidden('#skF_2'(A_69, B_70), A_69) | r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.01/1.50  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.01/1.50  tff(c_118, plain, (![A_74, B_75]: (~v1_xboole_0(A_74) | r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_96, c_2])).
% 3.01/1.50  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.01/1.50  tff(c_85, plain, (![A_63, B_64]: (r2_hidden('#skF_3'(A_63, B_64), B_64) | ~r2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.01/1.50  tff(c_90, plain, (![B_65, A_66]: (~v1_xboole_0(B_65) | ~r2_xboole_0(A_66, B_65))), inference(resolution, [status(thm)], [c_85, c_2])).
% 3.01/1.50  tff(c_94, plain, (![B_11, A_10]: (~v1_xboole_0(B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(resolution, [status(thm)], [c_12, c_90])).
% 3.01/1.50  tff(c_123, plain, (![B_76, A_77]: (~v1_xboole_0(B_76) | B_76=A_77 | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_118, c_94])).
% 3.01/1.50  tff(c_126, plain, (![A_77]: (k1_xboole_0=A_77 | ~v1_xboole_0(A_77))), inference(resolution, [status(thm)], [c_18, c_123])).
% 3.01/1.50  tff(c_224, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_215, c_126])).
% 3.01/1.50  tff(c_230, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_224])).
% 3.01/1.50  tff(c_232, plain, (![A_103]: (r2_hidden(A_103, '#skF_11') | ~r2_hidden(A_103, '#skF_10'))), inference(splitRight, [status(thm)], [c_192])).
% 3.01/1.50  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.01/1.50  tff(c_1064, plain, (![A_168]: (r1_tarski(A_168, '#skF_11') | ~r2_hidden('#skF_2'(A_168, '#skF_11'), '#skF_10'))), inference(resolution, [status(thm)], [c_232, c_8])).
% 3.01/1.50  tff(c_1069, plain, (r1_tarski('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_10, c_1064])).
% 3.01/1.50  tff(c_22, plain, (![A_12, B_13]: (r2_hidden('#skF_3'(A_12, B_13), B_13) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.01/1.50  tff(c_257, plain, (![A_105, B_106, D_107]: (r2_hidden('#skF_9'(A_105, B_106, k2_zfmisc_1(A_105, B_106), D_107), B_106) | ~r2_hidden(D_107, k2_zfmisc_1(A_105, B_106)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.01/1.50  tff(c_279, plain, (![B_108, D_109, A_110]: (~v1_xboole_0(B_108) | ~r2_hidden(D_109, k2_zfmisc_1(A_110, B_108)))), inference(resolution, [status(thm)], [c_257, c_2])).
% 3.01/1.50  tff(c_301, plain, (![D_109]: (~v1_xboole_0('#skF_10') | ~r2_hidden(D_109, k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_279])).
% 3.01/1.50  tff(c_312, plain, (~v1_xboole_0('#skF_10')), inference(splitLeft, [status(thm)], [c_301])).
% 3.01/1.50  tff(c_164, plain, (![B_90, D_91, A_92, C_93]: (r2_hidden(B_90, D_91) | ~r2_hidden(k4_tarski(A_92, B_90), k2_zfmisc_1(C_93, D_91)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.01/1.50  tff(c_449, plain, (![B_123, A_124]: (r2_hidden(B_123, '#skF_10') | ~r2_hidden(k4_tarski(A_124, B_123), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_164])).
% 3.01/1.50  tff(c_454, plain, (![B_50, A_49]: (r2_hidden(B_50, '#skF_10') | ~r2_hidden(B_50, '#skF_11') | ~r2_hidden(A_49, '#skF_10'))), inference(resolution, [status(thm)], [c_48, c_449])).
% 3.01/1.50  tff(c_873, plain, (![A_157]: (~r2_hidden(A_157, '#skF_10'))), inference(splitLeft, [status(thm)], [c_454])).
% 3.01/1.50  tff(c_909, plain, (v1_xboole_0('#skF_10')), inference(resolution, [status(thm)], [c_4, c_873])).
% 3.01/1.50  tff(c_920, plain, $false, inference(negUnitSimplification, [status(thm)], [c_312, c_909])).
% 3.01/1.50  tff(c_922, plain, (![B_158]: (r2_hidden(B_158, '#skF_10') | ~r2_hidden(B_158, '#skF_11'))), inference(splitRight, [status(thm)], [c_454])).
% 3.01/1.50  tff(c_1155, plain, (![A_178]: (r2_hidden('#skF_3'(A_178, '#skF_11'), '#skF_10') | ~r2_xboole_0(A_178, '#skF_11'))), inference(resolution, [status(thm)], [c_22, c_922])).
% 3.01/1.50  tff(c_20, plain, (![A_12, B_13]: (~r2_hidden('#skF_3'(A_12, B_13), A_12) | ~r2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.01/1.50  tff(c_1171, plain, (~r2_xboole_0('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_1155, c_20])).
% 3.01/1.50  tff(c_1175, plain, ('#skF_11'='#skF_10' | ~r1_tarski('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_12, c_1171])).
% 3.01/1.50  tff(c_1178, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_1175])).
% 3.01/1.50  tff(c_1180, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_1178])).
% 3.01/1.50  tff(c_1182, plain, (v1_xboole_0('#skF_10')), inference(splitRight, [status(thm)], [c_301])).
% 3.01/1.50  tff(c_1191, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_1182, c_126])).
% 3.01/1.50  tff(c_1197, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1191])).
% 3.01/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.50  
% 3.01/1.50  Inference rules
% 3.01/1.50  ----------------------
% 3.01/1.50  #Ref     : 0
% 3.01/1.50  #Sup     : 246
% 3.01/1.50  #Fact    : 0
% 3.01/1.50  #Define  : 0
% 3.01/1.50  #Split   : 4
% 3.01/1.50  #Chain   : 0
% 3.01/1.50  #Close   : 0
% 3.01/1.50  
% 3.01/1.50  Ordering : KBO
% 3.01/1.50  
% 3.01/1.50  Simplification rules
% 3.01/1.50  ----------------------
% 3.01/1.50  #Subsume      : 73
% 3.01/1.50  #Demod        : 61
% 3.01/1.50  #Tautology    : 43
% 3.01/1.50  #SimpNegUnit  : 13
% 3.01/1.50  #BackRed      : 4
% 3.01/1.50  
% 3.01/1.50  #Partial instantiations: 0
% 3.01/1.50  #Strategies tried      : 1
% 3.01/1.50  
% 3.01/1.50  Timing (in seconds)
% 3.01/1.50  ----------------------
% 3.01/1.50  Preprocessing        : 0.31
% 3.01/1.50  Parsing              : 0.16
% 3.01/1.50  CNF conversion       : 0.03
% 3.01/1.50  Main loop            : 0.38
% 3.01/1.50  Inferencing          : 0.14
% 3.01/1.50  Reduction            : 0.10
% 3.01/1.50  Demodulation         : 0.06
% 3.01/1.50  BG Simplification    : 0.03
% 3.01/1.50  Subsumption          : 0.09
% 3.01/1.50  Abstraction          : 0.02
% 3.01/1.50  MUC search           : 0.00
% 3.01/1.50  Cooper               : 0.00
% 3.01/1.50  Total                : 0.73
% 3.01/1.50  Index Insertion      : 0.00
% 3.01/1.50  Index Deletion       : 0.00
% 3.01/1.50  Index Matching       : 0.00
% 3.01/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
