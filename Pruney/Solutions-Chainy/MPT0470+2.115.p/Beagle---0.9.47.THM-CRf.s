%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:17 EST 2020

% Result     : Theorem 9.51s
% Output     : CNFRefutation 9.51s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 124 expanded)
%              Number of leaves         :   27 (  56 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 212 expanded)
%              Number of equality atoms :   23 (  51 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_8 > #skF_1 > #skF_4 > #skF_10

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(c_38,plain,
    ( k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_74,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    v1_relat_1('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_14,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [A_140,B_141,C_142] :
      ( ~ r1_xboole_0(A_140,B_141)
      | ~ r2_hidden(C_142,k3_xboole_0(A_140,B_141)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    ! [A_6,C_142] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_142,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_51])).

tff(c_62,plain,(
    ! [C_143] : ~ r2_hidden(C_143,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_67,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_62])).

tff(c_306,plain,(
    ! [A_205,B_206,C_207] :
      ( r2_hidden(k4_tarski('#skF_6'(A_205,B_206,C_207),'#skF_8'(A_205,B_206,C_207)),A_205)
      | r2_hidden(k4_tarski('#skF_9'(A_205,B_206,C_207),'#skF_10'(A_205,B_206,C_207)),C_207)
      | k5_relat_1(A_205,B_206) = C_207
      | ~ v1_relat_1(C_207)
      | ~ v1_relat_1(B_206)
      | ~ v1_relat_1(A_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_61,plain,(
    ! [C_142] : ~ r2_hidden(C_142,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_58])).

tff(c_342,plain,(
    ! [B_206,C_207] :
      ( r2_hidden(k4_tarski('#skF_9'(k1_xboole_0,B_206,C_207),'#skF_10'(k1_xboole_0,B_206,C_207)),C_207)
      | k5_relat_1(k1_xboole_0,B_206) = C_207
      | ~ v1_relat_1(C_207)
      | ~ v1_relat_1(B_206)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_306,c_61])).

tff(c_408,plain,(
    ! [B_208,C_209] :
      ( r2_hidden(k4_tarski('#skF_9'(k1_xboole_0,B_208,C_209),'#skF_10'(k1_xboole_0,B_208,C_209)),C_209)
      | k5_relat_1(k1_xboole_0,B_208) = C_209
      | ~ v1_relat_1(C_209)
      | ~ v1_relat_1(B_208) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_342])).

tff(c_444,plain,(
    ! [B_208] :
      ( k5_relat_1(k1_xboole_0,B_208) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(B_208) ) ),
    inference(resolution,[status(thm)],[c_408,c_61])).

tff(c_462,plain,(
    ! [B_210] :
      ( k5_relat_1(k1_xboole_0,B_210) = k1_xboole_0
      | ~ v1_relat_1(B_210) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_444])).

tff(c_477,plain,(
    k5_relat_1(k1_xboole_0,'#skF_11') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_462])).

tff(c_485,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_477])).

tff(c_486,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_2030,plain,(
    ! [A_289,B_290,C_291] :
      ( r2_hidden(k4_tarski('#skF_8'(A_289,B_290,C_291),'#skF_7'(A_289,B_290,C_291)),B_290)
      | r2_hidden(k4_tarski('#skF_9'(A_289,B_290,C_291),'#skF_10'(A_289,B_290,C_291)),C_291)
      | k5_relat_1(A_289,B_290) = C_291
      | ~ v1_relat_1(C_291)
      | ~ v1_relat_1(B_290)
      | ~ v1_relat_1(A_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7620,plain,(
    ! [A_411,B_412,A_413,C_414] :
      ( ~ r1_xboole_0(A_411,B_412)
      | r2_hidden(k4_tarski('#skF_9'(A_413,k3_xboole_0(A_411,B_412),C_414),'#skF_10'(A_413,k3_xboole_0(A_411,B_412),C_414)),C_414)
      | k5_relat_1(A_413,k3_xboole_0(A_411,B_412)) = C_414
      | ~ v1_relat_1(C_414)
      | ~ v1_relat_1(k3_xboole_0(A_411,B_412))
      | ~ v1_relat_1(A_413) ) ),
    inference(resolution,[status(thm)],[c_2030,c_4])).

tff(c_7667,plain,(
    ! [A_411,B_412,A_413] :
      ( ~ r1_xboole_0(A_411,B_412)
      | k5_relat_1(A_413,k3_xboole_0(A_411,B_412)) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k3_xboole_0(A_411,B_412))
      | ~ v1_relat_1(A_413) ) ),
    inference(resolution,[status(thm)],[c_7620,c_61])).

tff(c_14986,plain,(
    ! [A_493,B_494,A_495] :
      ( ~ r1_xboole_0(A_493,B_494)
      | k5_relat_1(A_495,k3_xboole_0(A_493,B_494)) = k1_xboole_0
      | ~ v1_relat_1(k3_xboole_0(A_493,B_494))
      | ~ v1_relat_1(A_495) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_7667])).

tff(c_14990,plain,(
    ! [A_6,A_495] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | k5_relat_1(A_495,k3_xboole_0(A_6,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_495) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_14986])).

tff(c_14994,plain,(
    ! [A_496] :
      ( k5_relat_1(A_496,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_496) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_6,c_8,c_14990])).

tff(c_15063,plain,(
    k5_relat_1('#skF_11',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_14994])).

tff(c_15090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_486,c_15063])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:05:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.51/3.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.51/3.30  
% 9.51/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.51/3.30  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k5_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_5 > #skF_3 > #skF_7 > #skF_9 > #skF_8 > #skF_1 > #skF_4 > #skF_10
% 9.51/3.30  
% 9.51/3.30  %Foreground sorts:
% 9.51/3.30  
% 9.51/3.30  
% 9.51/3.30  %Background operators:
% 9.51/3.30  
% 9.51/3.30  
% 9.51/3.30  %Foreground operators:
% 9.51/3.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 9.51/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.51/3.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.51/3.30  tff('#skF_11', type, '#skF_11': $i).
% 9.51/3.30  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 9.51/3.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.51/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.51/3.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.51/3.30  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i * $i) > $i).
% 9.51/3.30  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.51/3.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 9.51/3.30  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.51/3.30  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 9.51/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.51/3.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.51/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.51/3.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.51/3.30  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 9.51/3.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.51/3.30  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.51/3.30  tff('#skF_10', type, '#skF_10': ($i * $i * $i) > $i).
% 9.51/3.30  
% 9.51/3.32  tff(f_94, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 9.51/3.32  tff(f_53, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 9.51/3.32  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 9.51/3.32  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 9.51/3.32  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 9.51/3.32  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 9.51/3.32  tff(c_38, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.51/3.32  tff(c_74, plain, (k5_relat_1(k1_xboole_0, '#skF_11')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 9.51/3.32  tff(c_40, plain, (v1_relat_1('#skF_11')), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.51/3.32  tff(c_14, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.51/3.32  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.51/3.32  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.51/3.32  tff(c_51, plain, (![A_140, B_141, C_142]: (~r1_xboole_0(A_140, B_141) | ~r2_hidden(C_142, k3_xboole_0(A_140, B_141)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.51/3.32  tff(c_58, plain, (![A_6, C_142]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_142, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_51])).
% 9.51/3.32  tff(c_62, plain, (![C_143]: (~r2_hidden(C_143, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_58])).
% 9.51/3.32  tff(c_67, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_62])).
% 9.51/3.32  tff(c_306, plain, (![A_205, B_206, C_207]: (r2_hidden(k4_tarski('#skF_6'(A_205, B_206, C_207), '#skF_8'(A_205, B_206, C_207)), A_205) | r2_hidden(k4_tarski('#skF_9'(A_205, B_206, C_207), '#skF_10'(A_205, B_206, C_207)), C_207) | k5_relat_1(A_205, B_206)=C_207 | ~v1_relat_1(C_207) | ~v1_relat_1(B_206) | ~v1_relat_1(A_205))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.51/3.32  tff(c_61, plain, (![C_142]: (~r2_hidden(C_142, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_58])).
% 9.51/3.32  tff(c_342, plain, (![B_206, C_207]: (r2_hidden(k4_tarski('#skF_9'(k1_xboole_0, B_206, C_207), '#skF_10'(k1_xboole_0, B_206, C_207)), C_207) | k5_relat_1(k1_xboole_0, B_206)=C_207 | ~v1_relat_1(C_207) | ~v1_relat_1(B_206) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_306, c_61])).
% 9.51/3.32  tff(c_408, plain, (![B_208, C_209]: (r2_hidden(k4_tarski('#skF_9'(k1_xboole_0, B_208, C_209), '#skF_10'(k1_xboole_0, B_208, C_209)), C_209) | k5_relat_1(k1_xboole_0, B_208)=C_209 | ~v1_relat_1(C_209) | ~v1_relat_1(B_208))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_342])).
% 9.51/3.32  tff(c_444, plain, (![B_208]: (k5_relat_1(k1_xboole_0, B_208)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(B_208))), inference(resolution, [status(thm)], [c_408, c_61])).
% 9.51/3.32  tff(c_462, plain, (![B_210]: (k5_relat_1(k1_xboole_0, B_210)=k1_xboole_0 | ~v1_relat_1(B_210))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_444])).
% 9.51/3.32  tff(c_477, plain, (k5_relat_1(k1_xboole_0, '#skF_11')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_462])).
% 9.51/3.32  tff(c_485, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_477])).
% 9.51/3.32  tff(c_486, plain, (k5_relat_1('#skF_11', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 9.51/3.32  tff(c_2030, plain, (![A_289, B_290, C_291]: (r2_hidden(k4_tarski('#skF_8'(A_289, B_290, C_291), '#skF_7'(A_289, B_290, C_291)), B_290) | r2_hidden(k4_tarski('#skF_9'(A_289, B_290, C_291), '#skF_10'(A_289, B_290, C_291)), C_291) | k5_relat_1(A_289, B_290)=C_291 | ~v1_relat_1(C_291) | ~v1_relat_1(B_290) | ~v1_relat_1(A_289))), inference(cnfTransformation, [status(thm)], [f_71])).
% 9.51/3.32  tff(c_4, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.51/3.32  tff(c_7620, plain, (![A_411, B_412, A_413, C_414]: (~r1_xboole_0(A_411, B_412) | r2_hidden(k4_tarski('#skF_9'(A_413, k3_xboole_0(A_411, B_412), C_414), '#skF_10'(A_413, k3_xboole_0(A_411, B_412), C_414)), C_414) | k5_relat_1(A_413, k3_xboole_0(A_411, B_412))=C_414 | ~v1_relat_1(C_414) | ~v1_relat_1(k3_xboole_0(A_411, B_412)) | ~v1_relat_1(A_413))), inference(resolution, [status(thm)], [c_2030, c_4])).
% 9.51/3.32  tff(c_7667, plain, (![A_411, B_412, A_413]: (~r1_xboole_0(A_411, B_412) | k5_relat_1(A_413, k3_xboole_0(A_411, B_412))=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(k3_xboole_0(A_411, B_412)) | ~v1_relat_1(A_413))), inference(resolution, [status(thm)], [c_7620, c_61])).
% 9.51/3.32  tff(c_14986, plain, (![A_493, B_494, A_495]: (~r1_xboole_0(A_493, B_494) | k5_relat_1(A_495, k3_xboole_0(A_493, B_494))=k1_xboole_0 | ~v1_relat_1(k3_xboole_0(A_493, B_494)) | ~v1_relat_1(A_495))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_7667])).
% 9.51/3.32  tff(c_14990, plain, (![A_6, A_495]: (~r1_xboole_0(A_6, k1_xboole_0) | k5_relat_1(A_495, k3_xboole_0(A_6, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_495))), inference(superposition, [status(thm), theory('equality')], [c_6, c_14986])).
% 9.51/3.32  tff(c_14994, plain, (![A_496]: (k5_relat_1(A_496, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_496))), inference(demodulation, [status(thm), theory('equality')], [c_67, c_6, c_8, c_14990])).
% 9.51/3.32  tff(c_15063, plain, (k5_relat_1('#skF_11', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_14994])).
% 9.51/3.32  tff(c_15090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_486, c_15063])).
% 9.51/3.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.51/3.32  
% 9.51/3.32  Inference rules
% 9.51/3.32  ----------------------
% 9.51/3.32  #Ref     : 2
% 9.51/3.32  #Sup     : 3417
% 9.51/3.32  #Fact    : 0
% 9.51/3.32  #Define  : 0
% 9.51/3.32  #Split   : 3
% 9.51/3.32  #Chain   : 0
% 9.51/3.32  #Close   : 0
% 9.51/3.32  
% 9.51/3.32  Ordering : KBO
% 9.51/3.32  
% 9.51/3.32  Simplification rules
% 9.51/3.32  ----------------------
% 9.51/3.32  #Subsume      : 1109
% 9.51/3.32  #Demod        : 4416
% 9.51/3.32  #Tautology    : 880
% 9.51/3.32  #SimpNegUnit  : 83
% 9.51/3.32  #BackRed      : 47
% 9.51/3.32  
% 9.51/3.32  #Partial instantiations: 0
% 9.51/3.32  #Strategies tried      : 1
% 9.51/3.32  
% 9.51/3.32  Timing (in seconds)
% 9.51/3.32  ----------------------
% 9.51/3.32  Preprocessing        : 0.32
% 9.51/3.33  Parsing              : 0.17
% 9.51/3.33  CNF conversion       : 0.03
% 9.51/3.33  Main loop            : 2.20
% 9.51/3.33  Inferencing          : 0.67
% 9.51/3.33  Reduction            : 0.68
% 9.51/3.33  Demodulation         : 0.49
% 9.51/3.33  BG Simplification    : 0.08
% 9.51/3.33  Subsumption          : 0.64
% 9.74/3.33  Abstraction          : 0.13
% 9.74/3.33  MUC search           : 0.00
% 9.74/3.33  Cooper               : 0.00
% 9.74/3.33  Total                : 2.55
% 9.74/3.33  Index Insertion      : 0.00
% 9.74/3.33  Index Deletion       : 0.00
% 9.74/3.33  Index Matching       : 0.00
% 9.74/3.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
