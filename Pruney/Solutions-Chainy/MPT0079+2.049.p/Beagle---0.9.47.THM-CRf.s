%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:49 EST 2020

% Result     : Theorem 8.23s
% Output     : CNFRefutation 8.23s
% Verified   : 
% Statistics : Number of formulae       :   59 (  82 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 128 expanded)
%              Number of equality atoms :   30 (  52 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,D)
          & r1_xboole_0(C,A)
          & r1_xboole_0(D,B) )
       => C = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_30,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_36,plain,(
    k2_xboole_0('#skF_3','#skF_4') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    ! [A_23,B_24] : r1_tarski(A_23,k2_xboole_0(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55,plain,(
    r1_tarski('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_26])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_34,plain,(
    r1_xboole_0('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_59,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    k3_xboole_0('#skF_3','#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_59])).

tff(c_255,plain,(
    ! [A_51,B_52] : k4_xboole_0(A_51,k3_xboole_0(A_51,B_52)) = k4_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_284,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_255])).

tff(c_296,plain,(
    k4_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_284])).

tff(c_898,plain,(
    ! [A_74,B_75,C_76] :
      ( r1_tarski(k4_xboole_0(A_74,B_75),C_76)
      | ~ r1_tarski(A_74,k2_xboole_0(B_75,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1484,plain,(
    ! [C_97] :
      ( r1_tarski('#skF_3',C_97)
      | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_1',C_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_898])).

tff(c_1502,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_1484])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k1_xboole_0
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1512,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1502,c_14])).

tff(c_47,plain,(
    ! [A_31,B_32] : r1_tarski(k4_xboole_0(A_31,B_32),A_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_50,plain,(
    ! [A_12] : r1_tarski(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_47])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15] :
      ( r1_tarski(k4_xboole_0(A_13,B_14),C_15)
      | ~ r1_tarski(A_13,k2_xboole_0(B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1276,plain,(
    ! [A_86,B_87,C_88] :
      ( k1_xboole_0 = A_86
      | ~ r1_xboole_0(B_87,C_88)
      | ~ r1_tarski(A_86,C_88)
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1301,plain,(
    ! [A_90] :
      ( k1_xboole_0 = A_90
      | ~ r1_tarski(A_90,'#skF_2')
      | ~ r1_tarski(A_90,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_1276])).

tff(c_2840,plain,(
    ! [B_124] :
      ( k4_xboole_0('#skF_2',B_124) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0('#skF_2',B_124),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_10,c_1301])).

tff(c_16470,plain,(
    ! [B_312] :
      ( k4_xboole_0('#skF_2',B_312) = k1_xboole_0
      | ~ r1_tarski('#skF_2',k2_xboole_0(B_312,'#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_18,c_2840])).

tff(c_16495,plain,
    ( k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0
    | ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_16470])).

tff(c_16907,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_16495])).

tff(c_16922,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_6,c_16907])).

tff(c_16931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16922])).

tff(c_16932,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16495])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | k4_xboole_0(B_7,A_6) != k4_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_17006,plain,
    ( '#skF_2' = '#skF_3'
    | k4_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_16932,c_8])).

tff(c_17055,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1512,c_17006])).

tff(c_17057,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_17055])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.23/3.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.23/3.06  
% 8.23/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.23/3.06  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.23/3.06  
% 8.23/3.06  %Foreground sorts:
% 8.23/3.06  
% 8.23/3.06  
% 8.23/3.06  %Background operators:
% 8.23/3.06  
% 8.23/3.06  
% 8.23/3.06  %Foreground operators:
% 8.23/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.23/3.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 8.23/3.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.23/3.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.23/3.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 8.23/3.06  tff('#skF_2', type, '#skF_2': $i).
% 8.23/3.06  tff('#skF_3', type, '#skF_3': $i).
% 8.23/3.06  tff('#skF_1', type, '#skF_1': $i).
% 8.23/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.23/3.06  tff('#skF_4', type, '#skF_4': $i).
% 8.23/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.23/3.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.23/3.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.23/3.06  
% 8.23/3.08  tff(f_78, negated_conjecture, ~(![A, B, C, D]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, D)) & r1_xboole_0(C, A)) & r1_xboole_0(D, B)) => (C = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_xboole_1)).
% 8.23/3.08  tff(f_63, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.23/3.08  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 8.23/3.08  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 8.23/3.08  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 8.23/3.08  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 8.23/3.08  tff(f_43, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_xboole_1)).
% 8.23/3.08  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 8.23/3.08  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 8.23/3.08  tff(f_61, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 8.23/3.08  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 8.23/3.08  tff(c_30, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.23/3.08  tff(c_36, plain, (k2_xboole_0('#skF_3', '#skF_4')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.23/3.08  tff(c_26, plain, (![A_23, B_24]: (r1_tarski(A_23, k2_xboole_0(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.23/3.08  tff(c_55, plain, (r1_tarski('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_26])).
% 8.23/3.08  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.23/3.08  tff(c_34, plain, (r1_xboole_0('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.23/3.08  tff(c_59, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 8.23/3.08  tff(c_67, plain, (k3_xboole_0('#skF_3', '#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_59])).
% 8.23/3.08  tff(c_255, plain, (![A_51, B_52]: (k4_xboole_0(A_51, k3_xboole_0(A_51, B_52))=k4_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.23/3.08  tff(c_284, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_67, c_255])).
% 8.23/3.08  tff(c_296, plain, (k4_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_284])).
% 8.23/3.08  tff(c_898, plain, (![A_74, B_75, C_76]: (r1_tarski(k4_xboole_0(A_74, B_75), C_76) | ~r1_tarski(A_74, k2_xboole_0(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.23/3.08  tff(c_1484, plain, (![C_97]: (r1_tarski('#skF_3', C_97) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_1', C_97)))), inference(superposition, [status(thm), theory('equality')], [c_296, c_898])).
% 8.23/3.08  tff(c_1502, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_55, c_1484])).
% 8.23/3.08  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k1_xboole_0 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.23/3.08  tff(c_1512, plain, (k4_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1502, c_14])).
% 8.23/3.08  tff(c_47, plain, (![A_31, B_32]: (r1_tarski(k4_xboole_0(A_31, B_32), A_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.23/3.08  tff(c_50, plain, (![A_12]: (r1_tarski(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_16, c_47])).
% 8.23/3.08  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.23/3.08  tff(c_18, plain, (![A_13, B_14, C_15]: (r1_tarski(k4_xboole_0(A_13, B_14), C_15) | ~r1_tarski(A_13, k2_xboole_0(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.23/3.08  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.23/3.08  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 8.23/3.08  tff(c_1276, plain, (![A_86, B_87, C_88]: (k1_xboole_0=A_86 | ~r1_xboole_0(B_87, C_88) | ~r1_tarski(A_86, C_88) | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.23/3.08  tff(c_1301, plain, (![A_90]: (k1_xboole_0=A_90 | ~r1_tarski(A_90, '#skF_2') | ~r1_tarski(A_90, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_1276])).
% 8.23/3.08  tff(c_2840, plain, (![B_124]: (k4_xboole_0('#skF_2', B_124)=k1_xboole_0 | ~r1_tarski(k4_xboole_0('#skF_2', B_124), '#skF_4'))), inference(resolution, [status(thm)], [c_10, c_1301])).
% 8.23/3.08  tff(c_16470, plain, (![B_312]: (k4_xboole_0('#skF_2', B_312)=k1_xboole_0 | ~r1_tarski('#skF_2', k2_xboole_0(B_312, '#skF_4')))), inference(resolution, [status(thm)], [c_18, c_2840])).
% 8.23/3.08  tff(c_16495, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0 | ~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_16470])).
% 8.23/3.08  tff(c_16907, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_16495])).
% 8.23/3.08  tff(c_16922, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_6, c_16907])).
% 8.23/3.08  tff(c_16931, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_16922])).
% 8.23/3.08  tff(c_16932, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16495])).
% 8.23/3.08  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | k4_xboole_0(B_7, A_6)!=k4_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.23/3.08  tff(c_17006, plain, ('#skF_2'='#skF_3' | k4_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_16932, c_8])).
% 8.23/3.08  tff(c_17055, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1512, c_17006])).
% 8.23/3.08  tff(c_17057, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_17055])).
% 8.23/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.23/3.08  
% 8.23/3.08  Inference rules
% 8.23/3.08  ----------------------
% 8.23/3.08  #Ref     : 5
% 8.23/3.08  #Sup     : 4071
% 8.23/3.08  #Fact    : 0
% 8.23/3.08  #Define  : 0
% 8.23/3.08  #Split   : 12
% 8.23/3.08  #Chain   : 0
% 8.23/3.08  #Close   : 0
% 8.23/3.08  
% 8.23/3.08  Ordering : KBO
% 8.23/3.08  
% 8.23/3.08  Simplification rules
% 8.23/3.08  ----------------------
% 8.23/3.08  #Subsume      : 1337
% 8.23/3.08  #Demod        : 2105
% 8.23/3.08  #Tautology    : 1943
% 8.23/3.08  #SimpNegUnit  : 90
% 8.23/3.08  #BackRed      : 2
% 8.23/3.08  
% 8.23/3.08  #Partial instantiations: 0
% 8.23/3.08  #Strategies tried      : 1
% 8.23/3.08  
% 8.23/3.08  Timing (in seconds)
% 8.23/3.08  ----------------------
% 8.23/3.08  Preprocessing        : 0.30
% 8.23/3.08  Parsing              : 0.17
% 8.23/3.08  CNF conversion       : 0.02
% 8.23/3.08  Main loop            : 2.02
% 8.23/3.08  Inferencing          : 0.52
% 8.23/3.08  Reduction            : 0.87
% 8.23/3.08  Demodulation         : 0.67
% 8.23/3.08  BG Simplification    : 0.05
% 8.23/3.08  Subsumption          : 0.47
% 8.23/3.08  Abstraction          : 0.07
% 8.23/3.08  MUC search           : 0.00
% 8.23/3.08  Cooper               : 0.00
% 8.23/3.08  Total                : 2.34
% 8.23/3.08  Index Insertion      : 0.00
% 8.23/3.08  Index Deletion       : 0.00
% 8.23/3.08  Index Matching       : 0.00
% 8.23/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
