%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:02 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 157 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 421 expanded)
%              Number of equality atoms :   14 (  41 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_80,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_49,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r2_xboole_0(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

tff(c_30,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45,plain,(
    ! [A_22] :
      ( v1_ordinal1(A_22)
      | ~ v3_ordinal1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_52,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_45])).

tff(c_32,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_xboole_0(A_3,B_4)
      | B_4 = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_37,B_38] :
      ( r2_hidden(A_37,B_38)
      | ~ r2_xboole_0(A_37,B_38)
      | ~ v3_ordinal1(B_38)
      | ~ v1_ordinal1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_103,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | ~ v3_ordinal1(B_43)
      | ~ v1_ordinal1(A_42)
      | B_43 = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_91])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_57,plain,(
    ! [B_27,A_28] :
      ( ~ r2_hidden(B_27,A_28)
      | ~ r2_hidden(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_57])).

tff(c_113,plain,
    ( ~ v3_ordinal1('#skF_3')
    | ~ v1_ordinal1('#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_103,c_63])).

tff(c_123,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_32,c_113])).

tff(c_128,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_34,plain,(
    v1_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_24,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_118,plain,
    ( ~ v3_ordinal1('#skF_4')
    | ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_103,c_24])).

tff(c_127,plain,
    ( '#skF_2' = '#skF_4'
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_118])).

tff(c_129,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_127])).

tff(c_65,plain,(
    ! [B_30,A_31] :
      ( r1_tarski(B_30,A_31)
      | ~ r2_hidden(B_30,A_31)
      | ~ v1_ordinal1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_71,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_65])).

tff(c_75,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_71])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_87,plain,(
    ! [A_34,C_35,B_36] :
      ( r2_xboole_0(A_34,C_35)
      | ~ r2_xboole_0(B_36,C_35)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_96,plain,(
    ! [A_39,B_40,A_41] :
      ( r2_xboole_0(A_39,B_40)
      | ~ r1_tarski(A_39,A_41)
      | B_40 = A_41
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(resolution,[status(thm)],[c_4,c_87])).

tff(c_130,plain,(
    ! [B_44] :
      ( r2_xboole_0('#skF_2',B_44)
      | B_44 = '#skF_3'
      | ~ r1_tarski('#skF_3',B_44) ) ),
    inference(resolution,[status(thm)],[c_28,c_96])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ r2_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_169,plain,(
    ! [B_46] :
      ( r1_tarski('#skF_2',B_46)
      | B_46 = '#skF_3'
      | ~ r1_tarski('#skF_3',B_46) ) ),
    inference(resolution,[status(thm)],[c_130,c_8])).

tff(c_172,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_169,c_129])).

tff(c_177,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_172])).

tff(c_204,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_28])).

tff(c_209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_204])).

tff(c_210,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_127])).

tff(c_213,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_28])).

tff(c_216,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_213])).

tff(c_217,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_223,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_26])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_237,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_223,c_2])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:06:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.24  
% 2.04/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.25  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.04/1.25  
% 2.04/1.25  %Foreground sorts:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Background operators:
% 2.04/1.25  
% 2.04/1.25  
% 2.04/1.25  %Foreground operators:
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.25  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 2.04/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.04/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.25  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 2.04/1.25  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 2.04/1.25  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.25  
% 2.04/1.26  tff(f_80, negated_conjecture, ~(![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 2.04/1.26  tff(f_49, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.04/1.26  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.04/1.26  tff(f_65, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.04/1.26  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 2.04/1.26  tff(f_56, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.04/1.26  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r2_xboole_0(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_xboole_1)).
% 2.04/1.26  tff(c_30, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.26  tff(c_45, plain, (![A_22]: (v1_ordinal1(A_22) | ~v3_ordinal1(A_22))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.04/1.26  tff(c_52, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_45])).
% 2.04/1.26  tff(c_32, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.26  tff(c_4, plain, (![A_3, B_4]: (r2_xboole_0(A_3, B_4) | B_4=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.26  tff(c_91, plain, (![A_37, B_38]: (r2_hidden(A_37, B_38) | ~r2_xboole_0(A_37, B_38) | ~v3_ordinal1(B_38) | ~v1_ordinal1(A_37))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.04/1.26  tff(c_103, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | ~v3_ordinal1(B_43) | ~v1_ordinal1(A_42) | B_43=A_42 | ~r1_tarski(A_42, B_43))), inference(resolution, [status(thm)], [c_4, c_91])).
% 2.04/1.26  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.26  tff(c_57, plain, (![B_27, A_28]: (~r2_hidden(B_27, A_28) | ~r2_hidden(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.04/1.26  tff(c_63, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_57])).
% 2.04/1.26  tff(c_113, plain, (~v3_ordinal1('#skF_3') | ~v1_ordinal1('#skF_4') | '#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_103, c_63])).
% 2.04/1.26  tff(c_123, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_32, c_113])).
% 2.04/1.26  tff(c_128, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_123])).
% 2.04/1.26  tff(c_34, plain, (v1_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.26  tff(c_24, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.26  tff(c_118, plain, (~v3_ordinal1('#skF_4') | ~v1_ordinal1('#skF_2') | '#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_103, c_24])).
% 2.04/1.26  tff(c_127, plain, ('#skF_2'='#skF_4' | ~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_118])).
% 2.04/1.26  tff(c_129, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_127])).
% 2.04/1.26  tff(c_65, plain, (![B_30, A_31]: (r1_tarski(B_30, A_31) | ~r2_hidden(B_30, A_31) | ~v1_ordinal1(A_31))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.26  tff(c_71, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_65])).
% 2.04/1.26  tff(c_75, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_71])).
% 2.04/1.26  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.04/1.26  tff(c_87, plain, (![A_34, C_35, B_36]: (r2_xboole_0(A_34, C_35) | ~r2_xboole_0(B_36, C_35) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.04/1.26  tff(c_96, plain, (![A_39, B_40, A_41]: (r2_xboole_0(A_39, B_40) | ~r1_tarski(A_39, A_41) | B_40=A_41 | ~r1_tarski(A_41, B_40))), inference(resolution, [status(thm)], [c_4, c_87])).
% 2.04/1.26  tff(c_130, plain, (![B_44]: (r2_xboole_0('#skF_2', B_44) | B_44='#skF_3' | ~r1_tarski('#skF_3', B_44))), inference(resolution, [status(thm)], [c_28, c_96])).
% 2.04/1.26  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~r2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.04/1.26  tff(c_169, plain, (![B_46]: (r1_tarski('#skF_2', B_46) | B_46='#skF_3' | ~r1_tarski('#skF_3', B_46))), inference(resolution, [status(thm)], [c_130, c_8])).
% 2.04/1.26  tff(c_172, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_169, c_129])).
% 2.04/1.26  tff(c_177, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_172])).
% 2.04/1.26  tff(c_204, plain, (r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_177, c_28])).
% 2.04/1.26  tff(c_209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_204])).
% 2.04/1.26  tff(c_210, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_127])).
% 2.04/1.26  tff(c_213, plain, (r1_tarski('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_28])).
% 2.04/1.26  tff(c_216, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_213])).
% 2.04/1.26  tff(c_217, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_123])).
% 2.04/1.26  tff(c_223, plain, (r2_hidden('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_26])).
% 2.04/1.26  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.04/1.26  tff(c_237, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_223, c_2])).
% 2.04/1.26  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_237])).
% 2.04/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.26  
% 2.04/1.26  Inference rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Ref     : 0
% 2.04/1.26  #Sup     : 36
% 2.04/1.26  #Fact    : 0
% 2.04/1.26  #Define  : 0
% 2.04/1.26  #Split   : 3
% 2.04/1.26  #Chain   : 0
% 2.04/1.26  #Close   : 0
% 2.04/1.26  
% 2.04/1.26  Ordering : KBO
% 2.04/1.26  
% 2.04/1.26  Simplification rules
% 2.04/1.26  ----------------------
% 2.04/1.26  #Subsume      : 3
% 2.04/1.26  #Demod        : 41
% 2.04/1.26  #Tautology    : 13
% 2.04/1.26  #SimpNegUnit  : 2
% 2.04/1.26  #BackRed      : 22
% 2.04/1.26  
% 2.04/1.26  #Partial instantiations: 0
% 2.04/1.26  #Strategies tried      : 1
% 2.04/1.26  
% 2.04/1.26  Timing (in seconds)
% 2.04/1.26  ----------------------
% 2.04/1.26  Preprocessing        : 0.27
% 2.04/1.26  Parsing              : 0.16
% 2.04/1.26  CNF conversion       : 0.02
% 2.04/1.26  Main loop            : 0.21
% 2.04/1.26  Inferencing          : 0.08
% 2.04/1.26  Reduction            : 0.06
% 2.04/1.26  Demodulation         : 0.04
% 2.04/1.26  BG Simplification    : 0.02
% 2.04/1.26  Subsumption          : 0.05
% 2.04/1.26  Abstraction          : 0.01
% 2.04/1.26  MUC search           : 0.00
% 2.04/1.26  Cooper               : 0.00
% 2.04/1.26  Total                : 0.51
% 2.04/1.26  Index Insertion      : 0.00
% 2.04/1.26  Index Deletion       : 0.00
% 2.04/1.26  Index Matching       : 0.00
% 2.04/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
