%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:07 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 138 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k9_relat_1(C,A),k9_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(E,D),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_44,plain,(
    ! [A_57,B_58] :
      ( ~ r2_hidden('#skF_1'(A_57,B_58),B_58)
      | r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_44])).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    v1_relat_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    r1_tarski('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_95,plain,(
    ! [A_79,B_80,C_81] :
      ( r2_hidden(k4_tarski('#skF_6'(A_79,B_80,C_81),A_79),C_81)
      | ~ r2_hidden(A_79,k9_relat_1(C_81,B_80))
      | ~ v1_relat_1(C_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_79,B_80,C_81,B_2] :
      ( r2_hidden(k4_tarski('#skF_6'(A_79,B_80,C_81),A_79),B_2)
      | ~ r1_tarski(C_81,B_2)
      | ~ r2_hidden(A_79,k9_relat_1(C_81,B_80))
      | ~ v1_relat_1(C_81) ) ),
    inference(resolution,[status(thm)],[c_95,c_2])).

tff(c_36,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_55,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden('#skF_6'(A_63,B_64,C_65),B_64)
      | ~ r2_hidden(A_63,k9_relat_1(C_65,B_64))
      | ~ v1_relat_1(C_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_202,plain,(
    ! [A_109,B_110,C_111,B_112] :
      ( r2_hidden('#skF_6'(A_109,B_110,C_111),B_112)
      | ~ r1_tarski(B_110,B_112)
      | ~ r2_hidden(A_109,k9_relat_1(C_111,B_110))
      | ~ v1_relat_1(C_111) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_303,plain,(
    ! [B_155,A_154,B_156,B_158,C_157] :
      ( r2_hidden('#skF_6'(A_154,B_155,C_157),B_156)
      | ~ r1_tarski(B_158,B_156)
      | ~ r1_tarski(B_155,B_158)
      | ~ r2_hidden(A_154,k9_relat_1(C_157,B_155))
      | ~ v1_relat_1(C_157) ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_323,plain,(
    ! [A_162,B_163,C_164] :
      ( r2_hidden('#skF_6'(A_162,B_163,C_164),'#skF_8')
      | ~ r1_tarski(B_163,'#skF_7')
      | ~ r2_hidden(A_162,k9_relat_1(C_164,B_163))
      | ~ v1_relat_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_36,c_303])).

tff(c_8,plain,(
    ! [D_44,A_6,B_29,E_47] :
      ( r2_hidden(D_44,k9_relat_1(A_6,B_29))
      | ~ r2_hidden(E_47,B_29)
      | ~ r2_hidden(k4_tarski(E_47,D_44),A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_400,plain,(
    ! [A_207,C_209,B_205,A_208,D_206] :
      ( r2_hidden(D_206,k9_relat_1(A_208,'#skF_8'))
      | ~ r2_hidden(k4_tarski('#skF_6'(A_207,B_205,C_209),D_206),A_208)
      | ~ v1_relat_1(A_208)
      | ~ r1_tarski(B_205,'#skF_7')
      | ~ r2_hidden(A_207,k9_relat_1(C_209,B_205))
      | ~ v1_relat_1(C_209) ) ),
    inference(resolution,[status(thm)],[c_323,c_8])).

tff(c_527,plain,(
    ! [A_218,B_219,B_220,C_221] :
      ( r2_hidden(A_218,k9_relat_1(B_219,'#skF_8'))
      | ~ v1_relat_1(B_219)
      | ~ r1_tarski(B_220,'#skF_7')
      | ~ r1_tarski(C_221,B_219)
      | ~ r2_hidden(A_218,k9_relat_1(C_221,B_220))
      | ~ v1_relat_1(C_221) ) ),
    inference(resolution,[status(thm)],[c_98,c_400])).

tff(c_535,plain,(
    ! [A_218,B_220] :
      ( r2_hidden(A_218,k9_relat_1('#skF_10','#skF_8'))
      | ~ v1_relat_1('#skF_10')
      | ~ r1_tarski(B_220,'#skF_7')
      | ~ r2_hidden(A_218,k9_relat_1('#skF_9',B_220))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_38,c_527])).

tff(c_547,plain,(
    ! [A_222,B_223] :
      ( r2_hidden(A_222,k9_relat_1('#skF_10','#skF_8'))
      | ~ r1_tarski(B_223,'#skF_7')
      | ~ r2_hidden(A_222,k9_relat_1('#skF_9',B_223)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_535])).

tff(c_648,plain,(
    ! [B_228,B_229] :
      ( r2_hidden('#skF_1'(k9_relat_1('#skF_9',B_228),B_229),k9_relat_1('#skF_10','#skF_8'))
      | ~ r1_tarski(B_228,'#skF_7')
      | r1_tarski(k9_relat_1('#skF_9',B_228),B_229) ) ),
    inference(resolution,[status(thm)],[c_6,c_547])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_674,plain,(
    ! [B_235] :
      ( ~ r1_tarski(B_235,'#skF_7')
      | r1_tarski(k9_relat_1('#skF_9',B_235),k9_relat_1('#skF_10','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_648,c_4])).

tff(c_34,plain,(
    ~ r1_tarski(k9_relat_1('#skF_9','#skF_7'),k9_relat_1('#skF_10','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_693,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_674,c_34])).

tff(c_705,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_693])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:54:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.49  
% 3.17/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.50  %$ r2_hidden > r1_tarski > v1_relat_1 > k9_relat_1 > k4_tarski > #nlpp > k1_relat_1 > #skF_6 > #skF_4 > #skF_7 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 3.17/1.50  
% 3.17/1.50  %Foreground sorts:
% 3.17/1.50  
% 3.17/1.50  
% 3.17/1.50  %Background operators:
% 3.17/1.50  
% 3.17/1.50  
% 3.17/1.50  %Foreground operators:
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.50  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.17/1.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.17/1.50  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.17/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.17/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.50  tff('#skF_10', type, '#skF_10': $i).
% 3.17/1.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.17/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.17/1.50  tff('#skF_9', type, '#skF_9': $i).
% 3.17/1.50  tff('#skF_8', type, '#skF_8': $i).
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.50  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.17/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.17/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.17/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.50  
% 3.17/1.51  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.17/1.51  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k9_relat_1(C, A), k9_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t158_relat_1)).
% 3.17/1.51  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 3.17/1.51  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(E, D), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_relat_1)).
% 3.17/1.51  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.51  tff(c_44, plain, (![A_57, B_58]: (~r2_hidden('#skF_1'(A_57, B_58), B_58) | r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.51  tff(c_49, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_44])).
% 3.17/1.51  tff(c_42, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.17/1.51  tff(c_40, plain, (v1_relat_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.17/1.51  tff(c_38, plain, (r1_tarski('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.17/1.51  tff(c_95, plain, (![A_79, B_80, C_81]: (r2_hidden(k4_tarski('#skF_6'(A_79, B_80, C_81), A_79), C_81) | ~r2_hidden(A_79, k9_relat_1(C_81, B_80)) | ~v1_relat_1(C_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.51  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.51  tff(c_98, plain, (![A_79, B_80, C_81, B_2]: (r2_hidden(k4_tarski('#skF_6'(A_79, B_80, C_81), A_79), B_2) | ~r1_tarski(C_81, B_2) | ~r2_hidden(A_79, k9_relat_1(C_81, B_80)) | ~v1_relat_1(C_81))), inference(resolution, [status(thm)], [c_95, c_2])).
% 3.17/1.51  tff(c_36, plain, (r1_tarski('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.17/1.51  tff(c_55, plain, (![A_63, B_64, C_65]: (r2_hidden('#skF_6'(A_63, B_64, C_65), B_64) | ~r2_hidden(A_63, k9_relat_1(C_65, B_64)) | ~v1_relat_1(C_65))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.17/1.51  tff(c_202, plain, (![A_109, B_110, C_111, B_112]: (r2_hidden('#skF_6'(A_109, B_110, C_111), B_112) | ~r1_tarski(B_110, B_112) | ~r2_hidden(A_109, k9_relat_1(C_111, B_110)) | ~v1_relat_1(C_111))), inference(resolution, [status(thm)], [c_55, c_2])).
% 3.17/1.51  tff(c_303, plain, (![B_155, A_154, B_156, B_158, C_157]: (r2_hidden('#skF_6'(A_154, B_155, C_157), B_156) | ~r1_tarski(B_158, B_156) | ~r1_tarski(B_155, B_158) | ~r2_hidden(A_154, k9_relat_1(C_157, B_155)) | ~v1_relat_1(C_157))), inference(resolution, [status(thm)], [c_202, c_2])).
% 3.17/1.51  tff(c_323, plain, (![A_162, B_163, C_164]: (r2_hidden('#skF_6'(A_162, B_163, C_164), '#skF_8') | ~r1_tarski(B_163, '#skF_7') | ~r2_hidden(A_162, k9_relat_1(C_164, B_163)) | ~v1_relat_1(C_164))), inference(resolution, [status(thm)], [c_36, c_303])).
% 3.17/1.51  tff(c_8, plain, (![D_44, A_6, B_29, E_47]: (r2_hidden(D_44, k9_relat_1(A_6, B_29)) | ~r2_hidden(E_47, B_29) | ~r2_hidden(k4_tarski(E_47, D_44), A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.17/1.51  tff(c_400, plain, (![A_207, C_209, B_205, A_208, D_206]: (r2_hidden(D_206, k9_relat_1(A_208, '#skF_8')) | ~r2_hidden(k4_tarski('#skF_6'(A_207, B_205, C_209), D_206), A_208) | ~v1_relat_1(A_208) | ~r1_tarski(B_205, '#skF_7') | ~r2_hidden(A_207, k9_relat_1(C_209, B_205)) | ~v1_relat_1(C_209))), inference(resolution, [status(thm)], [c_323, c_8])).
% 3.17/1.51  tff(c_527, plain, (![A_218, B_219, B_220, C_221]: (r2_hidden(A_218, k9_relat_1(B_219, '#skF_8')) | ~v1_relat_1(B_219) | ~r1_tarski(B_220, '#skF_7') | ~r1_tarski(C_221, B_219) | ~r2_hidden(A_218, k9_relat_1(C_221, B_220)) | ~v1_relat_1(C_221))), inference(resolution, [status(thm)], [c_98, c_400])).
% 3.17/1.51  tff(c_535, plain, (![A_218, B_220]: (r2_hidden(A_218, k9_relat_1('#skF_10', '#skF_8')) | ~v1_relat_1('#skF_10') | ~r1_tarski(B_220, '#skF_7') | ~r2_hidden(A_218, k9_relat_1('#skF_9', B_220)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_38, c_527])).
% 3.17/1.51  tff(c_547, plain, (![A_222, B_223]: (r2_hidden(A_222, k9_relat_1('#skF_10', '#skF_8')) | ~r1_tarski(B_223, '#skF_7') | ~r2_hidden(A_222, k9_relat_1('#skF_9', B_223)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_535])).
% 3.17/1.51  tff(c_648, plain, (![B_228, B_229]: (r2_hidden('#skF_1'(k9_relat_1('#skF_9', B_228), B_229), k9_relat_1('#skF_10', '#skF_8')) | ~r1_tarski(B_228, '#skF_7') | r1_tarski(k9_relat_1('#skF_9', B_228), B_229))), inference(resolution, [status(thm)], [c_6, c_547])).
% 3.17/1.51  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.17/1.51  tff(c_674, plain, (![B_235]: (~r1_tarski(B_235, '#skF_7') | r1_tarski(k9_relat_1('#skF_9', B_235), k9_relat_1('#skF_10', '#skF_8')))), inference(resolution, [status(thm)], [c_648, c_4])).
% 3.17/1.51  tff(c_34, plain, (~r1_tarski(k9_relat_1('#skF_9', '#skF_7'), k9_relat_1('#skF_10', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.17/1.51  tff(c_693, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_674, c_34])).
% 3.17/1.51  tff(c_705, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_49, c_693])).
% 3.17/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.51  
% 3.17/1.51  Inference rules
% 3.17/1.51  ----------------------
% 3.17/1.51  #Ref     : 0
% 3.17/1.51  #Sup     : 172
% 3.17/1.51  #Fact    : 0
% 3.17/1.51  #Define  : 0
% 3.17/1.51  #Split   : 5
% 3.17/1.51  #Chain   : 0
% 3.17/1.51  #Close   : 0
% 3.17/1.51  
% 3.17/1.51  Ordering : KBO
% 3.17/1.51  
% 3.17/1.51  Simplification rules
% 3.17/1.51  ----------------------
% 3.17/1.51  #Subsume      : 25
% 3.17/1.51  #Demod        : 7
% 3.17/1.51  #Tautology    : 2
% 3.17/1.51  #SimpNegUnit  : 0
% 3.17/1.51  #BackRed      : 0
% 3.17/1.51  
% 3.17/1.51  #Partial instantiations: 0
% 3.17/1.51  #Strategies tried      : 1
% 3.17/1.51  
% 3.17/1.51  Timing (in seconds)
% 3.17/1.51  ----------------------
% 3.17/1.51  Preprocessing        : 0.28
% 3.17/1.51  Parsing              : 0.14
% 3.17/1.51  CNF conversion       : 0.03
% 3.17/1.51  Main loop            : 0.45
% 3.17/1.51  Inferencing          : 0.16
% 3.17/1.51  Reduction            : 0.10
% 3.17/1.51  Demodulation         : 0.06
% 3.17/1.51  BG Simplification    : 0.02
% 3.17/1.51  Subsumption          : 0.14
% 3.17/1.51  Abstraction          : 0.02
% 3.17/1.51  MUC search           : 0.00
% 3.17/1.51  Cooper               : 0.00
% 3.17/1.51  Total                : 0.76
% 3.17/1.51  Index Insertion      : 0.00
% 3.17/1.51  Index Deletion       : 0.00
% 3.17/1.51  Index Matching       : 0.00
% 3.17/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
