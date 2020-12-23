%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:03 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 652 expanded)
%              Number of leaves         :   17 ( 225 expanded)
%              Depth                    :   17
%              Number of atoms          :  154 (1964 expanded)
%              Number of equality atoms :   33 ( 277 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r3_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(r3_xboole_0,type,(
    r3_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] :
      ( r3_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        | r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => r3_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ~ ( ~ r2_hidden(A,B)
              & A != B
              & ~ r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v3_ordinal1(B)
     => ( r2_hidden(A,B)
       => v3_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & r2_hidden(B,C)
        & r2_hidden(C,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_31,plain,(
    ! [A_24,B_25] :
      ( ~ r1_tarski(A_24,B_25)
      | r3_xboole_0(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ~ r3_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_35,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_31,c_24])).

tff(c_36,plain,(
    ! [B_26,A_27] :
      ( ~ r1_tarski(B_26,A_27)
      | r3_xboole_0(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_24])).

tff(c_43,plain,(
    ! [A_32,B_33] :
      ( r2_hidden('#skF_1'(A_32,B_33),A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_32] : r1_tarski(A_32,A_32) ),
    inference(resolution,[status(thm)],[c_43,c_6])).

tff(c_28,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_26,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_20,plain,(
    ! [B_16,A_14] :
      ( r2_hidden(B_16,A_14)
      | B_16 = A_14
      | r2_hidden(A_14,B_16)
      | ~ v3_ordinal1(B_16)
      | ~ v3_ordinal1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( v3_ordinal1(A_12)
      | ~ r2_hidden(A_12,B_13)
      | ~ v3_ordinal1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_54,plain,(
    ! [A_32,B_33] :
      ( v3_ordinal1('#skF_1'(A_32,B_33))
      | ~ v3_ordinal1(A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_43,c_18])).

tff(c_121,plain,(
    ! [B_50,A_51] :
      ( r2_hidden(B_50,A_51)
      | B_50 = A_51
      | r2_hidden(A_51,B_50)
      | ~ v3_ordinal1(B_50)
      | ~ v3_ordinal1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_300,plain,(
    ! [A_92,A_93] :
      ( r1_tarski(A_92,A_93)
      | '#skF_1'(A_92,A_93) = A_93
      | r2_hidden(A_93,'#skF_1'(A_92,A_93))
      | ~ v3_ordinal1('#skF_1'(A_92,A_93))
      | ~ v3_ordinal1(A_93) ) ),
    inference(resolution,[status(thm)],[c_121,c_6])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [C_39,A_40,B_41] :
      ( ~ r2_hidden(C_39,A_40)
      | ~ r2_hidden(B_41,C_39)
      | ~ r2_hidden(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    ! [B_41,A_3,B_4] :
      ( ~ r2_hidden(B_41,'#skF_1'(A_3,B_4))
      | ~ r2_hidden(A_3,B_41)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_346,plain,(
    ! [A_94,A_95] :
      ( ~ r2_hidden(A_94,A_95)
      | r1_tarski(A_94,A_95)
      | '#skF_1'(A_94,A_95) = A_95
      | ~ v3_ordinal1('#skF_1'(A_94,A_95))
      | ~ v3_ordinal1(A_95) ) ),
    inference(resolution,[status(thm)],[c_300,c_75])).

tff(c_351,plain,(
    ! [A_96,B_97] :
      ( ~ r2_hidden(A_96,B_97)
      | '#skF_1'(A_96,B_97) = B_97
      | ~ v3_ordinal1(B_97)
      | ~ v3_ordinal1(A_96)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_54,c_346])).

tff(c_372,plain,(
    ! [B_98,A_99] :
      ( '#skF_1'(B_98,A_99) = A_99
      | r1_tarski(B_98,A_99)
      | B_98 = A_99
      | r2_hidden(A_99,B_98)
      | ~ v3_ordinal1(B_98)
      | ~ v3_ordinal1(A_99) ) ),
    inference(resolution,[status(thm)],[c_20,c_351])).

tff(c_350,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden(A_32,B_33)
      | '#skF_1'(A_32,B_33) = B_33
      | ~ v3_ordinal1(B_33)
      | ~ v3_ordinal1(A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_54,c_346])).

tff(c_606,plain,(
    ! [A_127,B_128] :
      ( '#skF_1'(A_127,B_128) = B_128
      | r1_tarski(A_127,B_128)
      | '#skF_1'(B_128,A_127) = A_127
      | r1_tarski(B_128,A_127)
      | B_128 = A_127
      | ~ v3_ordinal1(B_128)
      | ~ v3_ordinal1(A_127) ) ),
    inference(resolution,[status(thm)],[c_372,c_350])).

tff(c_623,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | '#skF_1'('#skF_3','#skF_2') = '#skF_2'
    | r1_tarski('#skF_3','#skF_2')
    | '#skF_2' = '#skF_3'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_606,c_35])).

tff(c_648,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | '#skF_1'('#skF_3','#skF_2') = '#skF_2'
    | r1_tarski('#skF_3','#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_623])).

tff(c_649,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | '#skF_1'('#skF_3','#skF_2') = '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_648])).

tff(c_659,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_649])).

tff(c_660,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_40])).

tff(c_666,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_660])).

tff(c_667,plain,
    ( '#skF_1'('#skF_3','#skF_2') = '#skF_2'
    | '#skF_1'('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_649])).

tff(c_689,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_742,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_8])).

tff(c_781,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_742])).

tff(c_371,plain,(
    ! [A_3,B_4] :
      ( '#skF_1'('#skF_1'(A_3,B_4),A_3) = A_3
      | ~ v3_ordinal1(A_3)
      | ~ v3_ordinal1('#skF_1'(A_3,B_4))
      | r1_tarski('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_351])).

tff(c_696,plain,
    ( '#skF_1'('#skF_1'('#skF_2','#skF_3'),'#skF_2') = '#skF_2'
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1'('#skF_2','#skF_3'))
    | r1_tarski('#skF_3','#skF_2')
    | r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_371])).

tff(c_752,plain,
    ( '#skF_1'('#skF_3','#skF_2') = '#skF_2'
    | r1_tarski('#skF_3','#skF_2')
    | r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_689,c_28,c_689,c_696])).

tff(c_753,plain,(
    '#skF_1'('#skF_3','#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_40,c_752])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_55,plain,(
    ! [A_32,B_33] :
      ( ~ r2_hidden(A_32,'#skF_1'(A_32,B_33))
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_43,c_2])).

tff(c_907,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_55])).

tff(c_949,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_781,c_907])).

tff(c_951,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_949])).

tff(c_952,plain,(
    '#skF_1'('#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_1006,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_8])).

tff(c_1045,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_1006])).

tff(c_960,plain,
    ( '#skF_1'('#skF_1'('#skF_3','#skF_2'),'#skF_3') = '#skF_3'
    | ~ v3_ordinal1('#skF_3')
    | ~ v3_ordinal1('#skF_1'('#skF_3','#skF_2'))
    | r1_tarski('#skF_2','#skF_3')
    | r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_371])).

tff(c_1016,plain,
    ( '#skF_1'('#skF_2','#skF_3') = '#skF_3'
    | r1_tarski('#skF_2','#skF_3')
    | r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_952,c_26,c_952,c_960])).

tff(c_1017,plain,(
    '#skF_1'('#skF_2','#skF_3') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_35,c_1016])).

tff(c_1247,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r1_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1017,c_55])).

tff(c_1292,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1045,c_1247])).

tff(c_1294,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_1292])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.61  
% 3.51/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.61  %$ r3_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 3.51/1.61  
% 3.51/1.61  %Foreground sorts:
% 3.51/1.61  
% 3.51/1.61  
% 3.51/1.61  %Background operators:
% 3.51/1.61  
% 3.51/1.61  
% 3.51/1.61  %Foreground operators:
% 3.51/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.51/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.51/1.61  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 3.51/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.61  tff(r3_xboole_0, type, r3_xboole_0: ($i * $i) > $o).
% 3.51/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.51/1.61  
% 3.87/1.63  tff(f_43, axiom, (![A, B]: (r3_xboole_0(A, B) <=> (r1_tarski(A, B) | r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_xboole_0)).
% 3.87/1.63  tff(f_81, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => r3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_ordinal1)).
% 3.87/1.63  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.87/1.63  tff(f_66, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_hidden(A, B) & ~(A = B)) & ~r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_ordinal1)).
% 3.87/1.63  tff(f_51, axiom, (![A, B]: (v3_ordinal1(B) => (r2_hidden(A, B) => v3_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_ordinal1)).
% 3.87/1.63  tff(f_73, axiom, (![A, B, C]: ~((r2_hidden(A, B) & r2_hidden(B, C)) & r2_hidden(C, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_ordinal1)).
% 3.87/1.63  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 3.87/1.63  tff(c_31, plain, (![A_24, B_25]: (~r1_tarski(A_24, B_25) | r3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.87/1.63  tff(c_24, plain, (~r3_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.87/1.63  tff(c_35, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_31, c_24])).
% 3.87/1.63  tff(c_36, plain, (![B_26, A_27]: (~r1_tarski(B_26, A_27) | r3_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.87/1.63  tff(c_40, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_24])).
% 3.87/1.63  tff(c_43, plain, (![A_32, B_33]: (r2_hidden('#skF_1'(A_32, B_33), A_32) | r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.63  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.63  tff(c_53, plain, (![A_32]: (r1_tarski(A_32, A_32))), inference(resolution, [status(thm)], [c_43, c_6])).
% 3.87/1.63  tff(c_28, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.87/1.63  tff(c_26, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.87/1.63  tff(c_20, plain, (![B_16, A_14]: (r2_hidden(B_16, A_14) | B_16=A_14 | r2_hidden(A_14, B_16) | ~v3_ordinal1(B_16) | ~v3_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.87/1.63  tff(c_18, plain, (![A_12, B_13]: (v3_ordinal1(A_12) | ~r2_hidden(A_12, B_13) | ~v3_ordinal1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.87/1.63  tff(c_54, plain, (![A_32, B_33]: (v3_ordinal1('#skF_1'(A_32, B_33)) | ~v3_ordinal1(A_32) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_43, c_18])).
% 3.87/1.63  tff(c_121, plain, (![B_50, A_51]: (r2_hidden(B_50, A_51) | B_50=A_51 | r2_hidden(A_51, B_50) | ~v3_ordinal1(B_50) | ~v3_ordinal1(A_51))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.87/1.63  tff(c_300, plain, (![A_92, A_93]: (r1_tarski(A_92, A_93) | '#skF_1'(A_92, A_93)=A_93 | r2_hidden(A_93, '#skF_1'(A_92, A_93)) | ~v3_ordinal1('#skF_1'(A_92, A_93)) | ~v3_ordinal1(A_93))), inference(resolution, [status(thm)], [c_121, c_6])).
% 3.87/1.63  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.87/1.63  tff(c_72, plain, (![C_39, A_40, B_41]: (~r2_hidden(C_39, A_40) | ~r2_hidden(B_41, C_39) | ~r2_hidden(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.87/1.63  tff(c_75, plain, (![B_41, A_3, B_4]: (~r2_hidden(B_41, '#skF_1'(A_3, B_4)) | ~r2_hidden(A_3, B_41) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_72])).
% 3.87/1.63  tff(c_346, plain, (![A_94, A_95]: (~r2_hidden(A_94, A_95) | r1_tarski(A_94, A_95) | '#skF_1'(A_94, A_95)=A_95 | ~v3_ordinal1('#skF_1'(A_94, A_95)) | ~v3_ordinal1(A_95))), inference(resolution, [status(thm)], [c_300, c_75])).
% 3.87/1.63  tff(c_351, plain, (![A_96, B_97]: (~r2_hidden(A_96, B_97) | '#skF_1'(A_96, B_97)=B_97 | ~v3_ordinal1(B_97) | ~v3_ordinal1(A_96) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_54, c_346])).
% 3.87/1.63  tff(c_372, plain, (![B_98, A_99]: ('#skF_1'(B_98, A_99)=A_99 | r1_tarski(B_98, A_99) | B_98=A_99 | r2_hidden(A_99, B_98) | ~v3_ordinal1(B_98) | ~v3_ordinal1(A_99))), inference(resolution, [status(thm)], [c_20, c_351])).
% 3.87/1.63  tff(c_350, plain, (![A_32, B_33]: (~r2_hidden(A_32, B_33) | '#skF_1'(A_32, B_33)=B_33 | ~v3_ordinal1(B_33) | ~v3_ordinal1(A_32) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_54, c_346])).
% 3.87/1.63  tff(c_606, plain, (![A_127, B_128]: ('#skF_1'(A_127, B_128)=B_128 | r1_tarski(A_127, B_128) | '#skF_1'(B_128, A_127)=A_127 | r1_tarski(B_128, A_127) | B_128=A_127 | ~v3_ordinal1(B_128) | ~v3_ordinal1(A_127))), inference(resolution, [status(thm)], [c_372, c_350])).
% 3.87/1.63  tff(c_623, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | '#skF_1'('#skF_3', '#skF_2')='#skF_2' | r1_tarski('#skF_3', '#skF_2') | '#skF_2'='#skF_3' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_606, c_35])).
% 3.87/1.63  tff(c_648, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | '#skF_1'('#skF_3', '#skF_2')='#skF_2' | r1_tarski('#skF_3', '#skF_2') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_623])).
% 3.87/1.63  tff(c_649, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | '#skF_1'('#skF_3', '#skF_2')='#skF_2' | '#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_648])).
% 3.87/1.63  tff(c_659, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_649])).
% 3.87/1.63  tff(c_660, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_659, c_40])).
% 3.87/1.63  tff(c_666, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_53, c_660])).
% 3.87/1.63  tff(c_667, plain, ('#skF_1'('#skF_3', '#skF_2')='#skF_2' | '#skF_1'('#skF_2', '#skF_3')='#skF_3'), inference(splitRight, [status(thm)], [c_649])).
% 3.87/1.63  tff(c_689, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_667])).
% 3.87/1.63  tff(c_742, plain, (r2_hidden('#skF_3', '#skF_2') | r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_689, c_8])).
% 3.87/1.63  tff(c_781, plain, (r2_hidden('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_35, c_742])).
% 3.87/1.63  tff(c_371, plain, (![A_3, B_4]: ('#skF_1'('#skF_1'(A_3, B_4), A_3)=A_3 | ~v3_ordinal1(A_3) | ~v3_ordinal1('#skF_1'(A_3, B_4)) | r1_tarski('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_351])).
% 3.87/1.63  tff(c_696, plain, ('#skF_1'('#skF_1'('#skF_2', '#skF_3'), '#skF_2')='#skF_2' | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1'('#skF_2', '#skF_3')) | r1_tarski('#skF_3', '#skF_2') | r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_689, c_371])).
% 3.87/1.63  tff(c_752, plain, ('#skF_1'('#skF_3', '#skF_2')='#skF_2' | r1_tarski('#skF_3', '#skF_2') | r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_689, c_28, c_689, c_696])).
% 3.87/1.63  tff(c_753, plain, ('#skF_1'('#skF_3', '#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_35, c_40, c_752])).
% 3.87/1.63  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.87/1.63  tff(c_55, plain, (![A_32, B_33]: (~r2_hidden(A_32, '#skF_1'(A_32, B_33)) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_43, c_2])).
% 3.87/1.63  tff(c_907, plain, (~r2_hidden('#skF_3', '#skF_2') | r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_753, c_55])).
% 3.87/1.63  tff(c_949, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_781, c_907])).
% 3.87/1.63  tff(c_951, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_949])).
% 3.87/1.63  tff(c_952, plain, ('#skF_1'('#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_667])).
% 3.87/1.63  tff(c_1006, plain, (r2_hidden('#skF_2', '#skF_3') | r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_952, c_8])).
% 3.87/1.63  tff(c_1045, plain, (r2_hidden('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_40, c_1006])).
% 3.87/1.63  tff(c_960, plain, ('#skF_1'('#skF_1'('#skF_3', '#skF_2'), '#skF_3')='#skF_3' | ~v3_ordinal1('#skF_3') | ~v3_ordinal1('#skF_1'('#skF_3', '#skF_2')) | r1_tarski('#skF_2', '#skF_3') | r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_952, c_371])).
% 3.87/1.63  tff(c_1016, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3' | r1_tarski('#skF_2', '#skF_3') | r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_952, c_26, c_952, c_960])).
% 3.87/1.63  tff(c_1017, plain, ('#skF_1'('#skF_2', '#skF_3')='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_40, c_35, c_1016])).
% 3.87/1.63  tff(c_1247, plain, (~r2_hidden('#skF_2', '#skF_3') | r1_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1017, c_55])).
% 3.87/1.63  tff(c_1292, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1045, c_1247])).
% 3.87/1.63  tff(c_1294, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_1292])).
% 3.87/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.87/1.63  
% 3.87/1.63  Inference rules
% 3.87/1.63  ----------------------
% 3.87/1.63  #Ref     : 0
% 3.87/1.63  #Sup     : 279
% 3.87/1.63  #Fact    : 4
% 3.87/1.63  #Define  : 0
% 3.87/1.63  #Split   : 2
% 3.87/1.63  #Chain   : 0
% 3.87/1.63  #Close   : 0
% 3.87/1.63  
% 3.87/1.63  Ordering : KBO
% 3.87/1.63  
% 3.87/1.63  Simplification rules
% 3.87/1.63  ----------------------
% 3.87/1.63  #Subsume      : 26
% 3.87/1.63  #Demod        : 141
% 3.87/1.63  #Tautology    : 47
% 3.87/1.63  #SimpNegUnit  : 86
% 3.87/1.63  #BackRed      : 4
% 3.87/1.63  
% 3.87/1.63  #Partial instantiations: 0
% 3.87/1.63  #Strategies tried      : 1
% 3.87/1.63  
% 3.87/1.63  Timing (in seconds)
% 3.87/1.63  ----------------------
% 3.87/1.63  Preprocessing        : 0.28
% 3.87/1.63  Parsing              : 0.16
% 3.87/1.63  CNF conversion       : 0.02
% 3.87/1.63  Main loop            : 0.58
% 3.87/1.63  Inferencing          : 0.20
% 3.87/1.63  Reduction            : 0.13
% 3.87/1.63  Demodulation         : 0.09
% 3.87/1.63  BG Simplification    : 0.03
% 3.87/1.63  Subsumption          : 0.18
% 3.87/1.63  Abstraction          : 0.03
% 3.87/1.63  MUC search           : 0.00
% 3.87/1.63  Cooper               : 0.00
% 3.87/1.63  Total                : 0.89
% 3.87/1.63  Index Insertion      : 0.00
% 3.87/1.63  Index Deletion       : 0.00
% 3.87/1.63  Index Matching       : 0.00
% 3.87/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
