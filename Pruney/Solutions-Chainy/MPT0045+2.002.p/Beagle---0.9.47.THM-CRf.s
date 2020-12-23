%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:45 EST 2020

% Result     : Theorem 6.21s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :   54 (  65 expanded)
%              Number of leaves         :   29 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 (  91 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_49,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_74,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k4_xboole_0(B,A))
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_90,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_30,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_68,plain,(
    ! [A_34,B_35] :
      ( r2_hidden('#skF_7'(A_34,B_35),B_35)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_72,plain,(
    ! [B_35,A_34] :
      ( ~ v1_xboole_0(B_35)
      | r1_xboole_0(A_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_54,plain,(
    r1_tarski('#skF_9',k4_xboole_0('#skF_10','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    ! [C_70,B_71,A_72] :
      ( r2_hidden(C_70,B_71)
      | ~ r2_hidden(C_70,A_72)
      | ~ r1_tarski(A_72,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_241,plain,(
    ! [A_79,B_80] :
      ( r2_hidden('#skF_1'(A_79),B_80)
      | ~ r1_tarski(A_79,B_80)
      | v1_xboole_0(A_79) ) ),
    inference(resolution,[status(thm)],[c_4,c_203])).

tff(c_14,plain,(
    ! [D_15,B_11,A_10] :
      ( ~ r2_hidden(D_15,B_11)
      | ~ r2_hidden(D_15,k4_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_7682,plain,(
    ! [A_467,B_468,A_469] :
      ( ~ r2_hidden('#skF_1'(A_467),B_468)
      | ~ r1_tarski(A_467,k4_xboole_0(A_469,B_468))
      | v1_xboole_0(A_467) ) ),
    inference(resolution,[status(thm)],[c_241,c_14])).

tff(c_7696,plain,(
    ! [A_470,A_471] :
      ( ~ r1_tarski(A_470,k4_xboole_0(A_471,A_470))
      | v1_xboole_0(A_470) ) ),
    inference(resolution,[status(thm)],[c_4,c_7682])).

tff(c_7754,plain,(
    v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_7696])).

tff(c_617,plain,(
    ! [A_131,B_132] :
      ( r2_hidden('#skF_5'(A_131,B_132),B_132)
      | r2_hidden('#skF_6'(A_131,B_132),A_131)
      | B_132 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ! [A_29] : k3_xboole_0(A_29,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_74,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_85,plain,(
    ! [A_29,C_40] :
      ( ~ r1_xboole_0(A_29,k1_xboole_0)
      | ~ r2_hidden(C_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_74])).

tff(c_99,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_686,plain,(
    ! [B_133] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_133),B_133)
      | k1_xboole_0 = B_133 ) ),
    inference(resolution,[status(thm)],[c_617,c_99])).

tff(c_721,plain,(
    ! [B_133] :
      ( ~ v1_xboole_0(B_133)
      | k1_xboole_0 = B_133 ) ),
    inference(resolution,[status(thm)],[c_686,c_2])).

tff(c_7791,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_7754,c_721])).

tff(c_7812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_7791])).

tff(c_7814,plain,(
    ! [A_472] : ~ r1_xboole_0(A_472,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_7818,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_72,c_7814])).

tff(c_7822,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:32:05 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.21/2.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.27  
% 6.21/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.27  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_6 > #skF_1 > #skF_4 > #skF_10 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_5
% 6.21/2.27  
% 6.21/2.27  %Foreground sorts:
% 6.21/2.27  
% 6.21/2.27  
% 6.21/2.27  %Background operators:
% 6.21/2.27  
% 6.21/2.27  
% 6.21/2.27  %Foreground operators:
% 6.21/2.27  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.21/2.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.21/2.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.21/2.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.21/2.27  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.21/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.21/2.27  tff('#skF_10', type, '#skF_10': $i).
% 6.21/2.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.21/2.27  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 6.21/2.27  tff('#skF_9', type, '#skF_9': $i).
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.27  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.21/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.21/2.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.21/2.27  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 6.21/2.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.21/2.27  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.21/2.27  
% 6.21/2.28  tff(f_49, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.21/2.28  tff(f_74, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.21/2.28  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 6.21/2.28  tff(f_95, negated_conjecture, ~(![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 6.21/2.28  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.21/2.28  tff(f_48, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.21/2.28  tff(f_56, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 6.21/2.28  tff(f_90, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.21/2.28  tff(f_88, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.21/2.28  tff(c_30, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.21/2.28  tff(c_68, plain, (![A_34, B_35]: (r2_hidden('#skF_7'(A_34, B_35), B_35) | r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.21/2.28  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.28  tff(c_72, plain, (![B_35, A_34]: (~v1_xboole_0(B_35) | r1_xboole_0(A_34, B_35))), inference(resolution, [status(thm)], [c_68, c_2])).
% 6.21/2.28  tff(c_52, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.21/2.28  tff(c_54, plain, (r1_tarski('#skF_9', k4_xboole_0('#skF_10', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.21/2.28  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.21/2.28  tff(c_203, plain, (![C_70, B_71, A_72]: (r2_hidden(C_70, B_71) | ~r2_hidden(C_70, A_72) | ~r1_tarski(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.21/2.28  tff(c_241, plain, (![A_79, B_80]: (r2_hidden('#skF_1'(A_79), B_80) | ~r1_tarski(A_79, B_80) | v1_xboole_0(A_79))), inference(resolution, [status(thm)], [c_4, c_203])).
% 6.21/2.28  tff(c_14, plain, (![D_15, B_11, A_10]: (~r2_hidden(D_15, B_11) | ~r2_hidden(D_15, k4_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.21/2.28  tff(c_7682, plain, (![A_467, B_468, A_469]: (~r2_hidden('#skF_1'(A_467), B_468) | ~r1_tarski(A_467, k4_xboole_0(A_469, B_468)) | v1_xboole_0(A_467))), inference(resolution, [status(thm)], [c_241, c_14])).
% 6.21/2.28  tff(c_7696, plain, (![A_470, A_471]: (~r1_tarski(A_470, k4_xboole_0(A_471, A_470)) | v1_xboole_0(A_470))), inference(resolution, [status(thm)], [c_4, c_7682])).
% 6.21/2.28  tff(c_7754, plain, (v1_xboole_0('#skF_9')), inference(resolution, [status(thm)], [c_54, c_7696])).
% 6.21/2.28  tff(c_617, plain, (![A_131, B_132]: (r2_hidden('#skF_5'(A_131, B_132), B_132) | r2_hidden('#skF_6'(A_131, B_132), A_131) | B_132=A_131)), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.21/2.28  tff(c_50, plain, (![A_29]: (k3_xboole_0(A_29, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.21/2.28  tff(c_74, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.21/2.28  tff(c_85, plain, (![A_29, C_40]: (~r1_xboole_0(A_29, k1_xboole_0) | ~r2_hidden(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_74])).
% 6.21/2.28  tff(c_99, plain, (![C_40]: (~r2_hidden(C_40, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_85])).
% 6.21/2.28  tff(c_686, plain, (![B_133]: (r2_hidden('#skF_5'(k1_xboole_0, B_133), B_133) | k1_xboole_0=B_133)), inference(resolution, [status(thm)], [c_617, c_99])).
% 6.21/2.28  tff(c_721, plain, (![B_133]: (~v1_xboole_0(B_133) | k1_xboole_0=B_133)), inference(resolution, [status(thm)], [c_686, c_2])).
% 6.21/2.28  tff(c_7791, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_7754, c_721])).
% 6.21/2.28  tff(c_7812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_7791])).
% 6.21/2.28  tff(c_7814, plain, (![A_472]: (~r1_xboole_0(A_472, k1_xboole_0))), inference(splitRight, [status(thm)], [c_85])).
% 6.21/2.28  tff(c_7818, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_72, c_7814])).
% 6.21/2.28  tff(c_7822, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_7818])).
% 6.21/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.21/2.28  
% 6.21/2.28  Inference rules
% 6.21/2.28  ----------------------
% 6.21/2.28  #Ref     : 0
% 6.21/2.28  #Sup     : 1898
% 6.21/2.28  #Fact    : 0
% 6.21/2.28  #Define  : 0
% 6.21/2.29  #Split   : 2
% 6.21/2.29  #Chain   : 0
% 6.21/2.29  #Close   : 0
% 6.21/2.29  
% 6.21/2.29  Ordering : KBO
% 6.21/2.29  
% 6.21/2.29  Simplification rules
% 6.21/2.29  ----------------------
% 6.21/2.29  #Subsume      : 450
% 6.21/2.29  #Demod        : 950
% 6.21/2.29  #Tautology    : 826
% 6.21/2.29  #SimpNegUnit  : 32
% 6.21/2.29  #BackRed      : 2
% 6.21/2.29  
% 6.21/2.29  #Partial instantiations: 0
% 6.21/2.29  #Strategies tried      : 1
% 6.21/2.29  
% 6.21/2.29  Timing (in seconds)
% 6.21/2.29  ----------------------
% 6.21/2.29  Preprocessing        : 0.31
% 6.21/2.29  Parsing              : 0.16
% 6.21/2.29  CNF conversion       : 0.02
% 6.21/2.29  Main loop            : 1.21
% 6.21/2.29  Inferencing          : 0.40
% 6.21/2.29  Reduction            : 0.32
% 6.21/2.29  Demodulation         : 0.22
% 6.21/2.29  BG Simplification    : 0.04
% 6.21/2.29  Subsumption          : 0.35
% 6.21/2.29  Abstraction          : 0.05
% 6.21/2.29  MUC search           : 0.00
% 6.21/2.29  Cooper               : 0.00
% 6.21/2.29  Total                : 1.55
% 6.21/2.29  Index Insertion      : 0.00
% 6.21/2.29  Index Deletion       : 0.00
% 6.21/2.29  Index Matching       : 0.00
% 6.21/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
