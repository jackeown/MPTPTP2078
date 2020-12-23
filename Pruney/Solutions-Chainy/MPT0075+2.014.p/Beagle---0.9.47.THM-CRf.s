%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:31 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :   53 (  86 expanded)
%              Number of leaves         :   21 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 154 expanded)
%              Number of equality atoms :   20 (  42 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_37,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_28,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    k3_xboole_0('#skF_5','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_28,c_64])).

tff(c_56,plain,(
    ! [A_21,B_22] :
      ( r1_xboole_0(A_21,B_22)
      | k3_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(B_9,A_8)
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_81,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | k3_xboole_0(A_26,B_25) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_14])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_122,plain,(
    ! [B_40,A_41] :
      ( k3_xboole_0(B_40,A_41) = k1_xboole_0
      | k3_xboole_0(A_41,B_40) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_126,plain,
    ( k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_122])).

tff(c_138,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_26,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_71,plain,(
    k3_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_26,c_64])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),A_10)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),B_11)
      | r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_98,plain,(
    ! [C_35,B_36,A_37] :
      ( r2_hidden(C_35,B_36)
      | ~ r2_hidden(C_35,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_203,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_2'(A_55,B_56),B_57)
      | ~ r1_tarski(B_56,B_57)
      | r1_xboole_0(A_55,B_56) ) ),
    inference(resolution,[status(thm)],[c_18,c_98])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_139,plain,(
    ! [A_42,B_43,C_44] :
      ( ~ r1_xboole_0(A_42,B_43)
      | ~ r2_hidden(C_44,B_43)
      | ~ r2_hidden(C_44,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_151,plain,(
    ! [C_44] :
      ( ~ r2_hidden(C_44,'#skF_4')
      | ~ r2_hidden(C_44,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_139])).

tff(c_265,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_2'(A_62,B_63),'#skF_4')
      | ~ r1_tarski(B_63,'#skF_3')
      | r1_xboole_0(A_62,B_63) ) ),
    inference(resolution,[status(thm)],[c_203,c_151])).

tff(c_281,plain,(
    ! [B_64] :
      ( ~ r1_tarski(B_64,'#skF_3')
      | r1_xboole_0('#skF_4',B_64) ) ),
    inference(resolution,[status(thm)],[c_20,c_265])).

tff(c_345,plain,(
    ! [B_70] :
      ( k3_xboole_0('#skF_4',B_70) = k1_xboole_0
      | ~ r1_tarski(B_70,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_281,c_8])).

tff(c_355,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_345])).

tff(c_87,plain,(
    ! [B_25,A_26] :
      ( k3_xboole_0(B_25,A_26) = k1_xboole_0
      | k3_xboole_0(A_26,B_25) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_81,c_8])).

tff(c_358,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_355,c_87])).

tff(c_362,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_358])).

tff(c_364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_362])).

tff(c_366,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_374,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_366,c_12])).

tff(c_376,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_374])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.34  
% 2.07/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.34  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.07/1.34  
% 2.07/1.34  %Foreground sorts:
% 2.07/1.34  
% 2.07/1.34  
% 2.07/1.34  %Background operators:
% 2.07/1.34  
% 2.07/1.34  
% 2.07/1.34  %Foreground operators:
% 2.07/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.34  
% 2.44/1.35  tff(f_74, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.44/1.35  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.44/1.35  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.44/1.35  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.44/1.35  tff(f_59, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.44/1.35  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.44/1.35  tff(f_37, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.44/1.35  tff(c_30, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.35  tff(c_28, plain, (r1_tarski('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.35  tff(c_64, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.44/1.35  tff(c_72, plain, (k3_xboole_0('#skF_5', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_28, c_64])).
% 2.44/1.35  tff(c_56, plain, (![A_21, B_22]: (r1_xboole_0(A_21, B_22) | k3_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.44/1.35  tff(c_14, plain, (![B_9, A_8]: (r1_xboole_0(B_9, A_8) | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.44/1.35  tff(c_81, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | k3_xboole_0(A_26, B_25)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_14])).
% 2.44/1.35  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.44/1.35  tff(c_122, plain, (![B_40, A_41]: (k3_xboole_0(B_40, A_41)=k1_xboole_0 | k3_xboole_0(A_41, B_40)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_8])).
% 2.44/1.35  tff(c_126, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0 | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_72, c_122])).
% 2.44/1.35  tff(c_138, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_126])).
% 2.44/1.35  tff(c_26, plain, (r1_tarski('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.35  tff(c_71, plain, (k3_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(resolution, [status(thm)], [c_26, c_64])).
% 2.44/1.35  tff(c_20, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), A_10) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.35  tff(c_18, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), B_11) | r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.35  tff(c_98, plain, (![C_35, B_36, A_37]: (r2_hidden(C_35, B_36) | ~r2_hidden(C_35, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.44/1.35  tff(c_203, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_2'(A_55, B_56), B_57) | ~r1_tarski(B_56, B_57) | r1_xboole_0(A_55, B_56))), inference(resolution, [status(thm)], [c_18, c_98])).
% 2.44/1.35  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.44/1.35  tff(c_139, plain, (![A_42, B_43, C_44]: (~r1_xboole_0(A_42, B_43) | ~r2_hidden(C_44, B_43) | ~r2_hidden(C_44, A_42))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.44/1.35  tff(c_151, plain, (![C_44]: (~r2_hidden(C_44, '#skF_4') | ~r2_hidden(C_44, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_139])).
% 2.44/1.35  tff(c_265, plain, (![A_62, B_63]: (~r2_hidden('#skF_2'(A_62, B_63), '#skF_4') | ~r1_tarski(B_63, '#skF_3') | r1_xboole_0(A_62, B_63))), inference(resolution, [status(thm)], [c_203, c_151])).
% 2.44/1.35  tff(c_281, plain, (![B_64]: (~r1_tarski(B_64, '#skF_3') | r1_xboole_0('#skF_4', B_64))), inference(resolution, [status(thm)], [c_20, c_265])).
% 2.44/1.35  tff(c_345, plain, (![B_70]: (k3_xboole_0('#skF_4', B_70)=k1_xboole_0 | ~r1_tarski(B_70, '#skF_3'))), inference(resolution, [status(thm)], [c_281, c_8])).
% 2.44/1.35  tff(c_355, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_345])).
% 2.44/1.35  tff(c_87, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k1_xboole_0 | k3_xboole_0(A_26, B_25)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_81, c_8])).
% 2.44/1.35  tff(c_358, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_355, c_87])).
% 2.44/1.35  tff(c_362, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_358])).
% 2.44/1.35  tff(c_364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_138, c_362])).
% 2.44/1.35  tff(c_366, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_126])).
% 2.44/1.35  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.44/1.35  tff(c_374, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_366, c_12])).
% 2.44/1.35  tff(c_376, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_374])).
% 2.44/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/1.35  
% 2.44/1.35  Inference rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Ref     : 0
% 2.44/1.35  #Sup     : 84
% 2.44/1.35  #Fact    : 0
% 2.44/1.35  #Define  : 0
% 2.44/1.35  #Split   : 4
% 2.44/1.35  #Chain   : 0
% 2.44/1.35  #Close   : 0
% 2.44/1.35  
% 2.44/1.35  Ordering : KBO
% 2.44/1.35  
% 2.44/1.35  Simplification rules
% 2.44/1.35  ----------------------
% 2.44/1.35  #Subsume      : 8
% 2.44/1.35  #Demod        : 16
% 2.44/1.35  #Tautology    : 20
% 2.44/1.35  #SimpNegUnit  : 2
% 2.44/1.35  #BackRed      : 7
% 2.44/1.35  
% 2.44/1.35  #Partial instantiations: 0
% 2.44/1.35  #Strategies tried      : 1
% 2.44/1.35  
% 2.44/1.35  Timing (in seconds)
% 2.44/1.35  ----------------------
% 2.44/1.36  Preprocessing        : 0.26
% 2.44/1.36  Parsing              : 0.14
% 2.44/1.36  CNF conversion       : 0.02
% 2.44/1.36  Main loop            : 0.27
% 2.44/1.36  Inferencing          : 0.10
% 2.44/1.36  Reduction            : 0.06
% 2.44/1.36  Demodulation         : 0.04
% 2.44/1.36  BG Simplification    : 0.02
% 2.44/1.36  Subsumption          : 0.06
% 2.44/1.36  Abstraction          : 0.01
% 2.44/1.36  MUC search           : 0.00
% 2.44/1.36  Cooper               : 0.00
% 2.44/1.36  Total                : 0.56
% 2.44/1.36  Index Insertion      : 0.00
% 2.44/1.36  Index Deletion       : 0.00
% 2.44/1.36  Index Matching       : 0.00
% 2.44/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
