%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:48 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 120 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   94 ( 231 expanded)
%              Number of equality atoms :   17 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
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

tff(f_69,axiom,(
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

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_xboole_0(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_0)).

tff(c_38,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),A_5)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( r2_hidden(k4_tarski(A_95,B_96),k2_zfmisc_1(C_97,D_98))
      | ~ r2_hidden(B_96,D_98)
      | ~ r2_hidden(A_95,C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_44,plain,(
    k2_zfmisc_1('#skF_7','#skF_6') = k2_zfmisc_1('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_148,plain,(
    ! [A_59,C_60,B_61,D_62] :
      ( r2_hidden(A_59,C_60)
      | ~ r2_hidden(k4_tarski(A_59,B_61),k2_zfmisc_1(C_60,D_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_151,plain,(
    ! [A_59,B_61] :
      ( r2_hidden(A_59,'#skF_7')
      | ~ r2_hidden(k4_tarski(A_59,B_61),k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_148])).

tff(c_304,plain,(
    ! [A_95,B_96] :
      ( r2_hidden(A_95,'#skF_7')
      | ~ r2_hidden(B_96,'#skF_7')
      | ~ r2_hidden(A_95,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_281,c_151])).

tff(c_312,plain,(
    ! [B_99] : ~ r2_hidden(B_99,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_304])).

tff(c_364,plain,(
    v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4,c_312])).

tff(c_18,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_2'(A_32,B_33),A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_78,plain,(
    ! [A_32,B_33] :
      ( ~ v1_xboole_0(A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_69,c_2])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( r2_xboole_0(A_10,B_11)
      | B_11 = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_5'(A_37,B_38),B_38)
      | ~ r2_xboole_0(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,(
    ! [B_41,A_42] :
      ( ~ v1_xboole_0(B_41)
      | ~ r2_xboole_0(A_42,B_41) ) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_97,plain,(
    ! [B_43,A_44] :
      ( ~ v1_xboole_0(B_43)
      | B_43 = A_44
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(resolution,[status(thm)],[c_12,c_92])).

tff(c_107,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_78,c_97])).

tff(c_110,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_18,c_107])).

tff(c_367,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_364,c_110])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_367])).

tff(c_375,plain,(
    ! [A_100] :
      ( r2_hidden(A_100,'#skF_7')
      | ~ r2_hidden(A_100,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_304])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_406,plain,(
    ! [A_105] :
      ( r1_tarski(A_105,'#skF_7')
      | ~ r2_hidden('#skF_2'(A_105,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_375,c_8])).

tff(c_416,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_10,c_406])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( r2_hidden('#skF_5'(A_15,B_16),B_16)
      | ~ r2_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_144,plain,(
    ! [B_55,D_56,A_57,C_58] :
      ( r2_hidden(B_55,D_56)
      | ~ r2_hidden(k4_tarski(A_57,B_55),k2_zfmisc_1(C_58,D_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_147,plain,(
    ! [B_55,A_57] :
      ( r2_hidden(B_55,'#skF_6')
      | ~ r2_hidden(k4_tarski(A_57,B_55),k2_zfmisc_1('#skF_6','#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_144])).

tff(c_305,plain,(
    ! [B_96,A_95] :
      ( r2_hidden(B_96,'#skF_6')
      | ~ r2_hidden(B_96,'#skF_7')
      | ~ r2_hidden(A_95,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_281,c_147])).

tff(c_520,plain,(
    ! [A_112] : ~ r2_hidden(A_112,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_305])).

tff(c_572,plain,(
    v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_4,c_520])).

tff(c_581,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_572,c_110])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_581])).

tff(c_589,plain,(
    ! [B_115] :
      ( r2_hidden(B_115,'#skF_6')
      | ~ r2_hidden(B_115,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_305])).

tff(c_703,plain,(
    ! [A_121] :
      ( r2_hidden('#skF_5'(A_121,'#skF_7'),'#skF_6')
      | ~ r2_xboole_0(A_121,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_30,c_589])).

tff(c_28,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden('#skF_5'(A_15,B_16),A_15)
      | ~ r2_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_719,plain,(
    ~ r2_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_703,c_28])).

tff(c_723,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_12,c_719])).

tff(c_726,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_723])).

tff(c_728,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_726])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:50:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.44  
% 2.90/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.44  %$ r2_xboole_0 > r2_hidden > r1_tarski > v1_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_5 > #skF_4
% 2.90/1.44  
% 2.90/1.44  %Foreground sorts:
% 2.90/1.44  
% 2.90/1.44  
% 2.90/1.44  %Background operators:
% 2.90/1.44  
% 2.90/1.44  
% 2.90/1.44  %Foreground operators:
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.90/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.90/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.90/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.90/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.90/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.90/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.90/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.90/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.90/1.44  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.90/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.90/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.90/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.90/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.90/1.44  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.90/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.90/1.44  
% 2.90/1.46  tff(f_78, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(B, A)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t114_zfmisc_1)).
% 2.90/1.46  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.90/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.90/1.46  tff(f_69, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.90/1.46  tff(f_46, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.90/1.46  tff(f_45, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.90/1.46  tff(f_63, axiom, (![A, B]: ~(r2_xboole_0(A, B) & (![C]: ~(r2_hidden(C, B) & ~r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_0)).
% 2.90/1.46  tff(c_38, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.46  tff(c_10, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), A_5) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.46  tff(c_40, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.46  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.46  tff(c_281, plain, (![A_95, B_96, C_97, D_98]: (r2_hidden(k4_tarski(A_95, B_96), k2_zfmisc_1(C_97, D_98)) | ~r2_hidden(B_96, D_98) | ~r2_hidden(A_95, C_97))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.46  tff(c_44, plain, (k2_zfmisc_1('#skF_7', '#skF_6')=k2_zfmisc_1('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.46  tff(c_148, plain, (![A_59, C_60, B_61, D_62]: (r2_hidden(A_59, C_60) | ~r2_hidden(k4_tarski(A_59, B_61), k2_zfmisc_1(C_60, D_62)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.46  tff(c_151, plain, (![A_59, B_61]: (r2_hidden(A_59, '#skF_7') | ~r2_hidden(k4_tarski(A_59, B_61), k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_148])).
% 2.90/1.46  tff(c_304, plain, (![A_95, B_96]: (r2_hidden(A_95, '#skF_7') | ~r2_hidden(B_96, '#skF_7') | ~r2_hidden(A_95, '#skF_6'))), inference(resolution, [status(thm)], [c_281, c_151])).
% 2.90/1.46  tff(c_312, plain, (![B_99]: (~r2_hidden(B_99, '#skF_7'))), inference(splitLeft, [status(thm)], [c_304])).
% 2.90/1.46  tff(c_364, plain, (v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_4, c_312])).
% 2.90/1.46  tff(c_18, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.90/1.46  tff(c_69, plain, (![A_32, B_33]: (r2_hidden('#skF_2'(A_32, B_33), A_32) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.90/1.46  tff(c_78, plain, (![A_32, B_33]: (~v1_xboole_0(A_32) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_69, c_2])).
% 2.90/1.46  tff(c_12, plain, (![A_10, B_11]: (r2_xboole_0(A_10, B_11) | B_11=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.90/1.46  tff(c_81, plain, (![A_37, B_38]: (r2_hidden('#skF_5'(A_37, B_38), B_38) | ~r2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.90/1.46  tff(c_92, plain, (![B_41, A_42]: (~v1_xboole_0(B_41) | ~r2_xboole_0(A_42, B_41))), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.90/1.46  tff(c_97, plain, (![B_43, A_44]: (~v1_xboole_0(B_43) | B_43=A_44 | ~r1_tarski(A_44, B_43))), inference(resolution, [status(thm)], [c_12, c_92])).
% 2.90/1.46  tff(c_107, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_78, c_97])).
% 2.90/1.46  tff(c_110, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_18, c_107])).
% 2.90/1.46  tff(c_367, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_364, c_110])).
% 2.90/1.46  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_367])).
% 2.90/1.46  tff(c_375, plain, (![A_100]: (r2_hidden(A_100, '#skF_7') | ~r2_hidden(A_100, '#skF_6'))), inference(splitRight, [status(thm)], [c_304])).
% 2.90/1.46  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.90/1.46  tff(c_406, plain, (![A_105]: (r1_tarski(A_105, '#skF_7') | ~r2_hidden('#skF_2'(A_105, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_375, c_8])).
% 2.90/1.46  tff(c_416, plain, (r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_10, c_406])).
% 2.90/1.46  tff(c_30, plain, (![A_15, B_16]: (r2_hidden('#skF_5'(A_15, B_16), B_16) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.90/1.46  tff(c_42, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.90/1.46  tff(c_144, plain, (![B_55, D_56, A_57, C_58]: (r2_hidden(B_55, D_56) | ~r2_hidden(k4_tarski(A_57, B_55), k2_zfmisc_1(C_58, D_56)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.90/1.46  tff(c_147, plain, (![B_55, A_57]: (r2_hidden(B_55, '#skF_6') | ~r2_hidden(k4_tarski(A_57, B_55), k2_zfmisc_1('#skF_6', '#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_44, c_144])).
% 2.90/1.46  tff(c_305, plain, (![B_96, A_95]: (r2_hidden(B_96, '#skF_6') | ~r2_hidden(B_96, '#skF_7') | ~r2_hidden(A_95, '#skF_6'))), inference(resolution, [status(thm)], [c_281, c_147])).
% 2.90/1.46  tff(c_520, plain, (![A_112]: (~r2_hidden(A_112, '#skF_6'))), inference(splitLeft, [status(thm)], [c_305])).
% 2.90/1.46  tff(c_572, plain, (v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_4, c_520])).
% 2.90/1.46  tff(c_581, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_572, c_110])).
% 2.90/1.46  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_581])).
% 2.90/1.46  tff(c_589, plain, (![B_115]: (r2_hidden(B_115, '#skF_6') | ~r2_hidden(B_115, '#skF_7'))), inference(splitRight, [status(thm)], [c_305])).
% 2.90/1.46  tff(c_703, plain, (![A_121]: (r2_hidden('#skF_5'(A_121, '#skF_7'), '#skF_6') | ~r2_xboole_0(A_121, '#skF_7'))), inference(resolution, [status(thm)], [c_30, c_589])).
% 2.90/1.46  tff(c_28, plain, (![A_15, B_16]: (~r2_hidden('#skF_5'(A_15, B_16), A_15) | ~r2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.90/1.46  tff(c_719, plain, (~r2_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_703, c_28])).
% 2.90/1.46  tff(c_723, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_12, c_719])).
% 2.90/1.46  tff(c_726, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_416, c_723])).
% 2.90/1.46  tff(c_728, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_726])).
% 2.90/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.46  
% 2.90/1.46  Inference rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Ref     : 0
% 2.90/1.46  #Sup     : 144
% 2.90/1.46  #Fact    : 0
% 2.90/1.46  #Define  : 0
% 2.90/1.46  #Split   : 3
% 2.90/1.46  #Chain   : 0
% 2.90/1.46  #Close   : 0
% 2.90/1.46  
% 2.90/1.46  Ordering : KBO
% 2.90/1.46  
% 2.90/1.46  Simplification rules
% 2.90/1.46  ----------------------
% 2.90/1.46  #Subsume      : 42
% 2.90/1.46  #Demod        : 5
% 2.90/1.46  #Tautology    : 22
% 2.90/1.46  #SimpNegUnit  : 9
% 2.90/1.46  #BackRed      : 2
% 2.90/1.46  
% 2.90/1.46  #Partial instantiations: 0
% 2.90/1.46  #Strategies tried      : 1
% 2.90/1.46  
% 2.90/1.46  Timing (in seconds)
% 2.90/1.46  ----------------------
% 2.90/1.46  Preprocessing        : 0.31
% 2.90/1.46  Parsing              : 0.16
% 2.90/1.46  CNF conversion       : 0.02
% 2.90/1.46  Main loop            : 0.37
% 2.90/1.46  Inferencing          : 0.15
% 2.90/1.46  Reduction            : 0.09
% 2.90/1.46  Demodulation         : 0.06
% 2.90/1.46  BG Simplification    : 0.02
% 2.90/1.46  Subsumption          : 0.09
% 2.90/1.46  Abstraction          : 0.02
% 2.90/1.46  MUC search           : 0.00
% 2.90/1.46  Cooper               : 0.00
% 2.90/1.46  Total                : 0.72
% 2.90/1.46  Index Insertion      : 0.00
% 2.90/1.46  Index Deletion       : 0.00
% 2.90/1.46  Index Matching       : 0.00
% 2.90/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
