%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:49 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 119 expanded)
%              Number of leaves         :   30 (  54 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 211 expanded)
%              Number of equality atoms :   17 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_2 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_100,negated_conjecture,(
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

tff(f_85,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(f_67,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_65,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_62,plain,(
    '#skF_11' != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_294,plain,(
    ! [A_117,B_118,C_119,D_120] :
      ( r2_hidden(k4_tarski(A_117,B_118),k2_zfmisc_1(C_119,D_120))
      | ~ r2_hidden(B_118,D_120)
      | ~ r2_hidden(A_117,C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_68,plain,(
    k2_zfmisc_1('#skF_11','#skF_10') = k2_zfmisc_1('#skF_10','#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_253,plain,(
    ! [A_104,C_105,B_106,D_107] :
      ( r2_hidden(A_104,C_105)
      | ~ r2_hidden(k4_tarski(A_104,B_106),k2_zfmisc_1(C_105,D_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_256,plain,(
    ! [A_104,B_106] :
      ( r2_hidden(A_104,'#skF_11')
      | ~ r2_hidden(k4_tarski(A_104,B_106),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_253])).

tff(c_320,plain,(
    ! [A_117,B_118] :
      ( r2_hidden(A_117,'#skF_11')
      | ~ r2_hidden(B_118,'#skF_11')
      | ~ r2_hidden(A_117,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_294,c_256])).

tff(c_375,plain,(
    ! [B_127] : ~ r2_hidden(B_127,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_320])).

tff(c_397,plain,(
    ! [B_129] : r1_tarski('#skF_11',B_129) ),
    inference(resolution,[status(thm)],[c_6,c_375])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_xboole_0(A_6,B_7)
      | B_7 = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_3'(A_13,B_14),B_14)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_146,plain,(
    ! [A_78,B_79,C_80] :
      ( ~ r1_xboole_0(A_78,B_79)
      | ~ r2_hidden(C_80,k3_xboole_0(A_78,B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_157,plain,(
    ! [A_16,C_80] :
      ( ~ r1_xboole_0(A_16,k1_xboole_0)
      | ~ r2_hidden(C_80,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_146])).

tff(c_169,plain,(
    ! [C_84] : ~ r2_hidden(C_84,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_157])).

tff(c_180,plain,(
    ! [A_85] : ~ r2_xboole_0(A_85,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_169])).

tff(c_185,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_180])).

tff(c_406,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_397,c_185])).

tff(c_412,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_406])).

tff(c_414,plain,(
    ! [A_130] :
      ( r2_hidden(A_130,'#skF_11')
      | ~ r2_hidden(A_130,'#skF_10') ) ),
    inference(splitRight,[status(thm)],[c_320])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_499,plain,(
    ! [A_138] :
      ( r1_tarski(A_138,'#skF_11')
      | ~ r2_hidden('#skF_1'(A_138,'#skF_11'),'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_414,c_4])).

tff(c_504,plain,(
    r1_tarski('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_6,c_499])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_211,plain,(
    ! [B_91,D_92,A_93,C_94] :
      ( r2_hidden(B_91,D_92)
      | ~ r2_hidden(k4_tarski(A_93,B_91),k2_zfmisc_1(C_94,D_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_214,plain,(
    ! [B_91,A_93] :
      ( r2_hidden(B_91,'#skF_10')
      | ~ r2_hidden(k4_tarski(A_93,B_91),k2_zfmisc_1('#skF_10','#skF_11')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_211])).

tff(c_322,plain,(
    ! [B_118,A_117] :
      ( r2_hidden(B_118,'#skF_10')
      | ~ r2_hidden(B_118,'#skF_11')
      | ~ r2_hidden(A_117,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_294,c_214])).

tff(c_555,plain,(
    ! [A_143] : ~ r2_hidden(A_143,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_322])).

tff(c_588,plain,(
    ! [B_145] : r1_tarski('#skF_10',B_145) ),
    inference(resolution,[status(thm)],[c_6,c_555])).

tff(c_600,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_588,c_185])).

tff(c_608,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_600])).

tff(c_662,plain,(
    ! [B_149] :
      ( r2_hidden(B_149,'#skF_10')
      | ~ r2_hidden(B_149,'#skF_11') ) ),
    inference(splitRight,[status(thm)],[c_322])).

tff(c_720,plain,(
    ! [A_153] :
      ( r2_hidden('#skF_3'(A_153,'#skF_11'),'#skF_10')
      | ~ r2_xboole_0(A_153,'#skF_11') ) ),
    inference(resolution,[status(thm)],[c_20,c_662])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden('#skF_3'(A_13,B_14),A_13)
      | ~ r2_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_733,plain,(
    ~ r2_xboole_0('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_720,c_18])).

tff(c_736,plain,
    ( '#skF_11' = '#skF_10'
    | ~ r1_tarski('#skF_10','#skF_11') ),
    inference(resolution,[status(thm)],[c_8,c_733])).

tff(c_739,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_736])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_739])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.35  
% 2.61/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.36  %$ r2_xboole_0 > r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_11 > #skF_6 > #skF_9 > #skF_4 > #skF_3 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_2 > #skF_1
% 2.61/1.36  
% 2.61/1.36  %Foreground sorts:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Background operators:
% 2.61/1.36  
% 2.61/1.36  
% 2.61/1.36  %Foreground operators:
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.36  tff('#skF_11', type, '#skF_11': $i).
% 2.61/1.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.61/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.61/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.36  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.61/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.36  tff('#skF_10', type, '#skF_10': $i).
% 2.61/1.36  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.61/1.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.61/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.61/1.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.61/1.36  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.61/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.61/1.36  
% 2.61/1.37  tff(f_100, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.61/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.61/1.37  tff(f_85, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.61/1.37  tff(f_39, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.61/1.37  tff(f_63, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.61/1.37  tff(f_67, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.61/1.37  tff(f_65, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.61/1.37  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.61/1.37  tff(c_62, plain, ('#skF_11'!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.61/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.37  tff(c_64, plain, (k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.61/1.37  tff(c_294, plain, (![A_117, B_118, C_119, D_120]: (r2_hidden(k4_tarski(A_117, B_118), k2_zfmisc_1(C_119, D_120)) | ~r2_hidden(B_118, D_120) | ~r2_hidden(A_117, C_119))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.37  tff(c_68, plain, (k2_zfmisc_1('#skF_11', '#skF_10')=k2_zfmisc_1('#skF_10', '#skF_11')), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.61/1.37  tff(c_253, plain, (![A_104, C_105, B_106, D_107]: (r2_hidden(A_104, C_105) | ~r2_hidden(k4_tarski(A_104, B_106), k2_zfmisc_1(C_105, D_107)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.37  tff(c_256, plain, (![A_104, B_106]: (r2_hidden(A_104, '#skF_11') | ~r2_hidden(k4_tarski(A_104, B_106), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_253])).
% 2.61/1.37  tff(c_320, plain, (![A_117, B_118]: (r2_hidden(A_117, '#skF_11') | ~r2_hidden(B_118, '#skF_11') | ~r2_hidden(A_117, '#skF_10'))), inference(resolution, [status(thm)], [c_294, c_256])).
% 2.61/1.37  tff(c_375, plain, (![B_127]: (~r2_hidden(B_127, '#skF_11'))), inference(splitLeft, [status(thm)], [c_320])).
% 2.61/1.37  tff(c_397, plain, (![B_129]: (r1_tarski('#skF_11', B_129))), inference(resolution, [status(thm)], [c_6, c_375])).
% 2.61/1.37  tff(c_8, plain, (![A_6, B_7]: (r2_xboole_0(A_6, B_7) | B_7=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.37  tff(c_20, plain, (![A_13, B_14]: (r2_hidden('#skF_3'(A_13, B_14), B_14) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.37  tff(c_24, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.61/1.37  tff(c_22, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.61/1.37  tff(c_146, plain, (![A_78, B_79, C_80]: (~r1_xboole_0(A_78, B_79) | ~r2_hidden(C_80, k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.61/1.37  tff(c_157, plain, (![A_16, C_80]: (~r1_xboole_0(A_16, k1_xboole_0) | ~r2_hidden(C_80, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22, c_146])).
% 2.61/1.37  tff(c_169, plain, (![C_84]: (~r2_hidden(C_84, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_157])).
% 2.61/1.37  tff(c_180, plain, (![A_85]: (~r2_xboole_0(A_85, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_169])).
% 2.61/1.37  tff(c_185, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_180])).
% 2.61/1.37  tff(c_406, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_397, c_185])).
% 2.61/1.37  tff(c_412, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_406])).
% 2.61/1.37  tff(c_414, plain, (![A_130]: (r2_hidden(A_130, '#skF_11') | ~r2_hidden(A_130, '#skF_10'))), inference(splitRight, [status(thm)], [c_320])).
% 2.61/1.37  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.61/1.37  tff(c_499, plain, (![A_138]: (r1_tarski(A_138, '#skF_11') | ~r2_hidden('#skF_1'(A_138, '#skF_11'), '#skF_10'))), inference(resolution, [status(thm)], [c_414, c_4])).
% 2.61/1.37  tff(c_504, plain, (r1_tarski('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_6, c_499])).
% 2.61/1.37  tff(c_66, plain, (k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.61/1.37  tff(c_211, plain, (![B_91, D_92, A_93, C_94]: (r2_hidden(B_91, D_92) | ~r2_hidden(k4_tarski(A_93, B_91), k2_zfmisc_1(C_94, D_92)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.37  tff(c_214, plain, (![B_91, A_93]: (r2_hidden(B_91, '#skF_10') | ~r2_hidden(k4_tarski(A_93, B_91), k2_zfmisc_1('#skF_10', '#skF_11')))), inference(superposition, [status(thm), theory('equality')], [c_68, c_211])).
% 2.61/1.37  tff(c_322, plain, (![B_118, A_117]: (r2_hidden(B_118, '#skF_10') | ~r2_hidden(B_118, '#skF_11') | ~r2_hidden(A_117, '#skF_10'))), inference(resolution, [status(thm)], [c_294, c_214])).
% 2.61/1.37  tff(c_555, plain, (![A_143]: (~r2_hidden(A_143, '#skF_10'))), inference(splitLeft, [status(thm)], [c_322])).
% 2.61/1.37  tff(c_588, plain, (![B_145]: (r1_tarski('#skF_10', B_145))), inference(resolution, [status(thm)], [c_6, c_555])).
% 2.61/1.37  tff(c_600, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_588, c_185])).
% 2.61/1.37  tff(c_608, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_600])).
% 2.61/1.37  tff(c_662, plain, (![B_149]: (r2_hidden(B_149, '#skF_10') | ~r2_hidden(B_149, '#skF_11'))), inference(splitRight, [status(thm)], [c_322])).
% 2.61/1.37  tff(c_720, plain, (![A_153]: (r2_hidden('#skF_3'(A_153, '#skF_11'), '#skF_10') | ~r2_xboole_0(A_153, '#skF_11'))), inference(resolution, [status(thm)], [c_20, c_662])).
% 2.61/1.37  tff(c_18, plain, (![A_13, B_14]: (~r2_hidden('#skF_3'(A_13, B_14), A_13) | ~r2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.61/1.37  tff(c_733, plain, (~r2_xboole_0('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_720, c_18])).
% 2.61/1.37  tff(c_736, plain, ('#skF_11'='#skF_10' | ~r1_tarski('#skF_10', '#skF_11')), inference(resolution, [status(thm)], [c_8, c_733])).
% 2.61/1.37  tff(c_739, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_504, c_736])).
% 2.61/1.37  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_739])).
% 2.61/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.37  
% 2.61/1.37  Inference rules
% 2.61/1.37  ----------------------
% 2.61/1.37  #Ref     : 0
% 2.61/1.37  #Sup     : 137
% 2.61/1.37  #Fact    : 0
% 2.61/1.37  #Define  : 0
% 2.61/1.37  #Split   : 3
% 2.61/1.37  #Chain   : 0
% 2.61/1.37  #Close   : 0
% 2.61/1.37  
% 2.61/1.37  Ordering : KBO
% 2.61/1.37  
% 2.61/1.37  Simplification rules
% 2.61/1.37  ----------------------
% 2.61/1.37  #Subsume      : 39
% 2.61/1.37  #Demod        : 22
% 2.61/1.37  #Tautology    : 30
% 2.61/1.37  #SimpNegUnit  : 22
% 2.61/1.37  #BackRed      : 3
% 2.61/1.37  
% 2.61/1.37  #Partial instantiations: 0
% 2.61/1.37  #Strategies tried      : 1
% 2.61/1.37  
% 2.61/1.37  Timing (in seconds)
% 2.61/1.37  ----------------------
% 2.61/1.37  Preprocessing        : 0.32
% 2.61/1.37  Parsing              : 0.17
% 2.61/1.37  CNF conversion       : 0.03
% 2.61/1.37  Main loop            : 0.29
% 2.61/1.37  Inferencing          : 0.11
% 2.61/1.37  Reduction            : 0.08
% 2.61/1.37  Demodulation         : 0.05
% 2.61/1.37  BG Simplification    : 0.02
% 2.61/1.37  Subsumption          : 0.07
% 2.61/1.37  Abstraction          : 0.01
% 2.61/1.38  MUC search           : 0.00
% 2.61/1.38  Cooper               : 0.00
% 2.61/1.38  Total                : 0.64
% 2.61/1.38  Index Insertion      : 0.00
% 2.61/1.38  Index Deletion       : 0.00
% 2.61/1.38  Index Matching       : 0.00
% 2.61/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
