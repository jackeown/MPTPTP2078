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
% DateTime   : Thu Dec  3 09:45:31 EST 2020

% Result     : Theorem 4.72s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 107 expanded)
%              Number of leaves         :   20 (  45 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 230 expanded)
%              Number of equality atoms :    3 (  10 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,B) )
       => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_62,plain,(
    ! [D_32,A_33,B_34] :
      ( r2_hidden(D_32,A_33)
      | ~ r2_hidden(D_32,k4_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_67,plain,(
    ! [A_33,B_34,B_2] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_33,B_34),B_2),A_33)
      | r1_tarski(k4_xboole_0(A_33,B_34),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_242,plain,(
    ! [A_76,B_77,B_78] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_76,B_77),B_78),A_76)
      | r1_tarski(k4_xboole_0(A_76,B_77),B_78) ) ),
    inference(resolution,[status(thm)],[c_6,c_62])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_275,plain,(
    ! [A_82,B_83] : r1_tarski(k4_xboole_0(A_82,B_83),A_82) ),
    inference(resolution,[status(thm)],[c_242,c_4])).

tff(c_38,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_72,plain,(
    ! [A_38,C_39,B_40] :
      ( r1_tarski(A_38,C_39)
      | ~ r1_tarski(B_40,C_39)
      | ~ r1_tarski(A_38,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_5')
      | ~ r1_tarski(A_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_38,c_72])).

tff(c_68,plain,(
    ! [C_35,B_36,A_37] :
      ( r2_hidden(C_35,B_36)
      | ~ r2_hidden(C_35,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_71,plain,(
    ! [A_1,B_2,B_36] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_36)
      | ~ r1_tarski(A_1,B_36)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_68])).

tff(c_56,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k4_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_214,plain,(
    ! [A_63,B_64,B_65] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_63,B_64),B_65),B_64)
      | r1_tarski(k4_xboole_0(A_63,B_64),B_65) ) ),
    inference(resolution,[status(thm)],[c_6,c_56])).

tff(c_225,plain,(
    ! [A_66,B_67,B_68] :
      ( ~ r1_tarski(k4_xboole_0(A_66,B_67),B_67)
      | r1_tarski(k4_xboole_0(A_66,B_67),B_68) ) ),
    inference(resolution,[status(thm)],[c_71,c_214])).

tff(c_232,plain,(
    ! [A_66,B_68] :
      ( r1_tarski(k4_xboole_0(A_66,'#skF_5'),B_68)
      | ~ r1_tarski(k4_xboole_0(A_66,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_81,c_225])).

tff(c_299,plain,(
    ! [B_68] : r1_tarski(k4_xboole_0('#skF_4','#skF_5'),B_68) ),
    inference(resolution,[status(thm)],[c_275,c_232])).

tff(c_165,plain,(
    ! [D_55,A_56,B_57] :
      ( r2_hidden(D_55,k4_xboole_0(A_56,B_57))
      | r2_hidden(D_55,B_57)
      | ~ r2_hidden(D_55,A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3335,plain,(
    ! [D_234,B_235,A_236,B_237] :
      ( r2_hidden(D_234,B_235)
      | ~ r1_tarski(k4_xboole_0(A_236,B_237),B_235)
      | r2_hidden(D_234,B_237)
      | ~ r2_hidden(D_234,A_236) ) ),
    inference(resolution,[status(thm)],[c_165,c_2])).

tff(c_3437,plain,(
    ! [D_234,B_68] :
      ( r2_hidden(D_234,B_68)
      | r2_hidden(D_234,'#skF_5')
      | ~ r2_hidden(D_234,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_299,c_3335])).

tff(c_3528,plain,(
    ! [D_240] :
      ( ~ r2_hidden(D_240,'#skF_4')
      | r2_hidden(D_240,'#skF_5') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3437])).

tff(c_3593,plain,(
    ! [A_244] :
      ( r1_tarski(A_244,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_244,'#skF_5'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3528,c_4])).

tff(c_3606,plain,(
    ! [B_34] : r1_tarski(k4_xboole_0('#skF_4',B_34),'#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_3593])).

tff(c_36,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,(
    ! [A_38] :
      ( r1_tarski(A_38,'#skF_5')
      | ~ r1_tarski(A_38,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_72])).

tff(c_233,plain,(
    ! [A_66,B_68] :
      ( r1_tarski(k4_xboole_0(A_66,'#skF_5'),B_68)
      | ~ r1_tarski(k4_xboole_0(A_66,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_80,c_225])).

tff(c_298,plain,(
    ! [B_68] : r1_tarski(k4_xboole_0('#skF_6','#skF_5'),B_68) ),
    inference(resolution,[status(thm)],[c_275,c_233])).

tff(c_3438,plain,(
    ! [D_234,B_68] :
      ( r2_hidden(D_234,B_68)
      | r2_hidden(D_234,'#skF_5')
      | ~ r2_hidden(D_234,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_298,c_3335])).

tff(c_4034,plain,(
    ! [D_256] :
      ( ~ r2_hidden(D_256,'#skF_6')
      | r2_hidden(D_256,'#skF_5') ) ),
    inference(factorization,[status(thm),theory(equality)],[c_3438])).

tff(c_4068,plain,(
    ! [A_257] :
      ( r1_tarski(A_257,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_257,'#skF_5'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4034,c_4])).

tff(c_4081,plain,(
    ! [B_34] : r1_tarski(k4_xboole_0('#skF_6',B_34),'#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_4068])).

tff(c_26,plain,(
    ! [A_12,B_13] : k2_xboole_0(k4_xboole_0(A_12,B_13),k4_xboole_0(B_13,A_12)) = k5_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_143,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(k2_xboole_0(A_49,C_50),B_51)
      | ~ r1_tarski(C_50,B_51)
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4322,plain,(
    ! [A_266,B_267,B_268] :
      ( r1_tarski(k5_xboole_0(A_266,B_267),B_268)
      | ~ r1_tarski(k4_xboole_0(B_267,A_266),B_268)
      | ~ r1_tarski(k4_xboole_0(A_266,B_267),B_268) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_143])).

tff(c_34,plain,(
    ~ r1_tarski(k5_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4400,plain,
    ( ~ r1_tarski(k4_xboole_0('#skF_6','#skF_4'),'#skF_5')
    | ~ r1_tarski(k4_xboole_0('#skF_4','#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_4322,c_34])).

tff(c_4435,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3606,c_4081,c_4400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:19:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.72/1.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.83  
% 4.72/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.72/1.84  %$ r2_hidden > r1_tarski > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 4.72/1.84  
% 4.72/1.84  %Foreground sorts:
% 4.72/1.84  
% 4.72/1.84  
% 4.72/1.84  %Background operators:
% 4.72/1.84  
% 4.72/1.84  
% 4.72/1.84  %Foreground operators:
% 4.72/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.72/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.72/1.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.72/1.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.72/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.72/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.72/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.72/1.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.72/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.72/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.72/1.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.72/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.72/1.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.72/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.72/1.84  
% 4.81/1.85  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 4.81/1.85  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.81/1.85  tff(f_65, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 4.81/1.85  tff(f_50, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.81/1.85  tff(f_44, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 4.81/1.85  tff(f_56, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 4.81/1.85  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.85  tff(c_62, plain, (![D_32, A_33, B_34]: (r2_hidden(D_32, A_33) | ~r2_hidden(D_32, k4_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.81/1.85  tff(c_67, plain, (![A_33, B_34, B_2]: (r2_hidden('#skF_1'(k4_xboole_0(A_33, B_34), B_2), A_33) | r1_tarski(k4_xboole_0(A_33, B_34), B_2))), inference(resolution, [status(thm)], [c_6, c_62])).
% 4.81/1.85  tff(c_242, plain, (![A_76, B_77, B_78]: (r2_hidden('#skF_1'(k4_xboole_0(A_76, B_77), B_78), A_76) | r1_tarski(k4_xboole_0(A_76, B_77), B_78))), inference(resolution, [status(thm)], [c_6, c_62])).
% 4.81/1.85  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.85  tff(c_275, plain, (![A_82, B_83]: (r1_tarski(k4_xboole_0(A_82, B_83), A_82))), inference(resolution, [status(thm)], [c_242, c_4])).
% 4.81/1.85  tff(c_38, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.85  tff(c_72, plain, (![A_38, C_39, B_40]: (r1_tarski(A_38, C_39) | ~r1_tarski(B_40, C_39) | ~r1_tarski(A_38, B_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.81/1.85  tff(c_81, plain, (![A_38]: (r1_tarski(A_38, '#skF_5') | ~r1_tarski(A_38, '#skF_4'))), inference(resolution, [status(thm)], [c_38, c_72])).
% 4.81/1.85  tff(c_68, plain, (![C_35, B_36, A_37]: (r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.85  tff(c_71, plain, (![A_1, B_2, B_36]: (r2_hidden('#skF_1'(A_1, B_2), B_36) | ~r1_tarski(A_1, B_36) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_68])).
% 4.81/1.85  tff(c_56, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k4_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.81/1.85  tff(c_214, plain, (![A_63, B_64, B_65]: (~r2_hidden('#skF_1'(k4_xboole_0(A_63, B_64), B_65), B_64) | r1_tarski(k4_xboole_0(A_63, B_64), B_65))), inference(resolution, [status(thm)], [c_6, c_56])).
% 4.81/1.85  tff(c_225, plain, (![A_66, B_67, B_68]: (~r1_tarski(k4_xboole_0(A_66, B_67), B_67) | r1_tarski(k4_xboole_0(A_66, B_67), B_68))), inference(resolution, [status(thm)], [c_71, c_214])).
% 4.81/1.85  tff(c_232, plain, (![A_66, B_68]: (r1_tarski(k4_xboole_0(A_66, '#skF_5'), B_68) | ~r1_tarski(k4_xboole_0(A_66, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_81, c_225])).
% 4.81/1.85  tff(c_299, plain, (![B_68]: (r1_tarski(k4_xboole_0('#skF_4', '#skF_5'), B_68))), inference(resolution, [status(thm)], [c_275, c_232])).
% 4.81/1.85  tff(c_165, plain, (![D_55, A_56, B_57]: (r2_hidden(D_55, k4_xboole_0(A_56, B_57)) | r2_hidden(D_55, B_57) | ~r2_hidden(D_55, A_56))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.81/1.85  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.81/1.85  tff(c_3335, plain, (![D_234, B_235, A_236, B_237]: (r2_hidden(D_234, B_235) | ~r1_tarski(k4_xboole_0(A_236, B_237), B_235) | r2_hidden(D_234, B_237) | ~r2_hidden(D_234, A_236))), inference(resolution, [status(thm)], [c_165, c_2])).
% 4.81/1.85  tff(c_3437, plain, (![D_234, B_68]: (r2_hidden(D_234, B_68) | r2_hidden(D_234, '#skF_5') | ~r2_hidden(D_234, '#skF_4'))), inference(resolution, [status(thm)], [c_299, c_3335])).
% 4.81/1.85  tff(c_3528, plain, (![D_240]: (~r2_hidden(D_240, '#skF_4') | r2_hidden(D_240, '#skF_5'))), inference(factorization, [status(thm), theory('equality')], [c_3437])).
% 4.81/1.85  tff(c_3593, plain, (![A_244]: (r1_tarski(A_244, '#skF_5') | ~r2_hidden('#skF_1'(A_244, '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_3528, c_4])).
% 4.81/1.85  tff(c_3606, plain, (![B_34]: (r1_tarski(k4_xboole_0('#skF_4', B_34), '#skF_5'))), inference(resolution, [status(thm)], [c_67, c_3593])).
% 4.81/1.85  tff(c_36, plain, (r1_tarski('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.85  tff(c_80, plain, (![A_38]: (r1_tarski(A_38, '#skF_5') | ~r1_tarski(A_38, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_72])).
% 4.81/1.85  tff(c_233, plain, (![A_66, B_68]: (r1_tarski(k4_xboole_0(A_66, '#skF_5'), B_68) | ~r1_tarski(k4_xboole_0(A_66, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_80, c_225])).
% 4.81/1.85  tff(c_298, plain, (![B_68]: (r1_tarski(k4_xboole_0('#skF_6', '#skF_5'), B_68))), inference(resolution, [status(thm)], [c_275, c_233])).
% 4.81/1.85  tff(c_3438, plain, (![D_234, B_68]: (r2_hidden(D_234, B_68) | r2_hidden(D_234, '#skF_5') | ~r2_hidden(D_234, '#skF_6'))), inference(resolution, [status(thm)], [c_298, c_3335])).
% 4.81/1.85  tff(c_4034, plain, (![D_256]: (~r2_hidden(D_256, '#skF_6') | r2_hidden(D_256, '#skF_5'))), inference(factorization, [status(thm), theory('equality')], [c_3438])).
% 4.81/1.85  tff(c_4068, plain, (![A_257]: (r1_tarski(A_257, '#skF_5') | ~r2_hidden('#skF_1'(A_257, '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_4034, c_4])).
% 4.81/1.85  tff(c_4081, plain, (![B_34]: (r1_tarski(k4_xboole_0('#skF_6', B_34), '#skF_5'))), inference(resolution, [status(thm)], [c_67, c_4068])).
% 4.81/1.85  tff(c_26, plain, (![A_12, B_13]: (k2_xboole_0(k4_xboole_0(A_12, B_13), k4_xboole_0(B_13, A_12))=k5_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.81/1.85  tff(c_143, plain, (![A_49, C_50, B_51]: (r1_tarski(k2_xboole_0(A_49, C_50), B_51) | ~r1_tarski(C_50, B_51) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.81/1.85  tff(c_4322, plain, (![A_266, B_267, B_268]: (r1_tarski(k5_xboole_0(A_266, B_267), B_268) | ~r1_tarski(k4_xboole_0(B_267, A_266), B_268) | ~r1_tarski(k4_xboole_0(A_266, B_267), B_268))), inference(superposition, [status(thm), theory('equality')], [c_26, c_143])).
% 4.81/1.85  tff(c_34, plain, (~r1_tarski(k5_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.85  tff(c_4400, plain, (~r1_tarski(k4_xboole_0('#skF_6', '#skF_4'), '#skF_5') | ~r1_tarski(k4_xboole_0('#skF_4', '#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_4322, c_34])).
% 4.81/1.85  tff(c_4435, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3606, c_4081, c_4400])).
% 4.81/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.85  
% 4.81/1.85  Inference rules
% 4.81/1.85  ----------------------
% 4.81/1.85  #Ref     : 0
% 4.81/1.85  #Sup     : 956
% 4.81/1.85  #Fact    : 4
% 4.81/1.85  #Define  : 0
% 4.81/1.85  #Split   : 0
% 4.81/1.85  #Chain   : 0
% 4.81/1.85  #Close   : 0
% 4.81/1.85  
% 4.81/1.85  Ordering : KBO
% 4.81/1.85  
% 4.81/1.85  Simplification rules
% 4.81/1.85  ----------------------
% 4.81/1.85  #Subsume      : 165
% 4.81/1.85  #Demod        : 436
% 4.81/1.85  #Tautology    : 444
% 4.81/1.85  #SimpNegUnit  : 0
% 4.81/1.85  #BackRed      : 0
% 4.81/1.85  
% 4.81/1.85  #Partial instantiations: 0
% 4.81/1.85  #Strategies tried      : 1
% 4.81/1.85  
% 4.81/1.85  Timing (in seconds)
% 4.81/1.85  ----------------------
% 4.81/1.85  Preprocessing        : 0.28
% 4.81/1.85  Parsing              : 0.15
% 4.81/1.85  CNF conversion       : 0.02
% 4.81/1.85  Main loop            : 0.81
% 4.81/1.85  Inferencing          : 0.27
% 4.81/1.85  Reduction            : 0.27
% 4.81/1.85  Demodulation         : 0.20
% 4.81/1.85  BG Simplification    : 0.03
% 4.81/1.85  Subsumption          : 0.20
% 4.81/1.85  Abstraction          : 0.04
% 4.81/1.85  MUC search           : 0.00
% 4.81/1.85  Cooper               : 0.00
% 4.81/1.85  Total                : 1.12
% 4.81/1.85  Index Insertion      : 0.00
% 4.81/1.85  Index Deletion       : 0.00
% 4.81/1.85  Index Matching       : 0.00
% 4.81/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
