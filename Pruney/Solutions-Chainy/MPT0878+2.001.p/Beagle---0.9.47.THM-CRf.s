%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:29 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 252 expanded)
%              Number of leaves         :   13 (  83 expanded)
%              Depth                    :    9
%              Number of atoms          :   89 ( 505 expanded)
%              Number of equality atoms :   84 ( 500 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_zfmisc_1(A,A,A) = k3_zfmisc_1(B,B,B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( k2_zfmisc_1(A,B) = k2_zfmisc_1(C,D)
     => ( A = k1_xboole_0
        | B = k1_xboole_0
        | ( A = C
          & B = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,A) = k2_zfmisc_1(B,B)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_zfmisc_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k3_zfmisc_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_186,plain,(
    ! [D_28,B_29,A_30,C_31] :
      ( D_28 = B_29
      | k1_xboole_0 = B_29
      | k1_xboole_0 = A_30
      | k2_zfmisc_1(C_31,D_28) != k2_zfmisc_1(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_429,plain,(
    ! [C_62,C_63,B_61,A_64,D_60] :
      ( D_60 = C_62
      | k1_xboole_0 = C_62
      | k2_zfmisc_1(A_64,B_61) = k1_xboole_0
      | k3_zfmisc_1(A_64,B_61,C_62) != k2_zfmisc_1(C_63,D_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_186])).

tff(c_447,plain,(
    ! [D_60,C_63] :
      ( D_60 = '#skF_2'
      | k1_xboole_0 = '#skF_2'
      | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
      | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_63,D_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_429])).

tff(c_468,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_60,plain,(
    ! [B_16,A_17] :
      ( B_16 = A_17
      | k2_zfmisc_1(B_16,B_16) != k2_zfmisc_1(A_17,A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [A_17] :
      ( k1_xboole_0 = A_17
      | k2_zfmisc_1(A_17,A_17) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_514,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_468,c_64])).

tff(c_90,plain,(
    ! [A_19,B_20,C_21] : k2_zfmisc_1(k2_zfmisc_1(A_19,B_20),C_21) = k3_zfmisc_1(A_19,B_20,C_21) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_124,plain,(
    ! [B_2,C_21] : k3_zfmisc_1(k1_xboole_0,B_2,C_21) = k2_zfmisc_1(k1_xboole_0,C_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_90])).

tff(c_134,plain,(
    ! [B_2,C_21] : k3_zfmisc_1(k1_xboole_0,B_2,C_21) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_124])).

tff(c_528,plain,(
    ! [B_2,C_21] : k3_zfmisc_1('#skF_2',B_2,C_21) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_514,c_134])).

tff(c_648,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_528,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k1_xboole_0 = B_2
      | k1_xboole_0 = A_1
      | k2_zfmisc_1(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [C_32,A_33,B_34] :
      ( k1_xboole_0 = C_32
      | k2_zfmisc_1(A_33,B_34) = k1_xboole_0
      | k3_zfmisc_1(A_33,B_34,C_32) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_2])).

tff(c_219,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
    | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_207])).

tff(c_253,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_523,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_253])).

tff(c_746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_523])).

tff(c_747,plain,(
    ! [D_60,C_63] :
      ( k1_xboole_0 = '#skF_2'
      | D_60 = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_63,D_60) ) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_779,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_747])).

tff(c_797,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_2',B_2) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_779,c_6])).

tff(c_748,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_781,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_779,c_748])).

tff(c_873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_797,c_781])).

tff(c_876,plain,(
    ! [D_87,C_88] :
      ( D_87 = '#skF_2'
      | k3_zfmisc_1('#skF_1','#skF_1','#skF_1') != k2_zfmisc_1(C_88,D_87) ) ),
    inference(splitRight,[status(thm)],[c_747])).

tff(c_879,plain,(
    ! [C_11,A_9,B_10] :
      ( C_11 = '#skF_2'
      | k3_zfmisc_1(A_9,B_10,C_11) != k3_zfmisc_1('#skF_1','#skF_1','#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_876])).

tff(c_889,plain,(
    '#skF_2' = '#skF_1' ),
    inference(reflexivity,[status(thm),theory(equality)],[c_879])).

tff(c_891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_889])).

tff(c_892,plain,
    ( k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_936,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_893,plain,(
    k3_zfmisc_1('#skF_1','#skF_1','#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_111,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_xboole_0 = C_21
      | k2_zfmisc_1(A_19,B_20) = k1_xboole_0
      | k3_zfmisc_1(A_19,B_20,C_21) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_2])).

tff(c_926,plain,
    ( k1_xboole_0 = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_893,c_111])).

tff(c_1066,plain,
    ( '#skF_2' = '#skF_1'
    | k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_936,c_926])).

tff(c_1067,plain,(
    k2_zfmisc_1('#skF_1','#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1066])).

tff(c_1140,plain,(
    ! [A_106] :
      ( A_106 = '#skF_2'
      | k2_zfmisc_1(A_106,A_106) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_936,c_64])).

tff(c_1143,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1067,c_1140])).

tff(c_1159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_1143])).

tff(c_1161,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_919,plain,(
    k3_zfmisc_1('#skF_2','#skF_2','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_18])).

tff(c_934,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_919,c_111])).

tff(c_1162,plain,(
    k2_zfmisc_1('#skF_2','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_1161,c_934])).

tff(c_1184,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1162,c_64])).

tff(c_1204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1161,c_1184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:50:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.42  %$ k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.91/1.42  
% 2.91/1.42  %Foreground sorts:
% 2.91/1.42  
% 2.91/1.42  
% 2.91/1.42  %Background operators:
% 2.91/1.42  
% 2.91/1.42  
% 2.91/1.42  %Foreground operators:
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.91/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.91/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.91/1.42  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.91/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.42  
% 2.91/1.44  tff(f_52, negated_conjecture, ~(![A, B]: ((k3_zfmisc_1(A, A, A) = k3_zfmisc_1(B, B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_mcart_1)).
% 2.91/1.44  tff(f_47, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.91/1.44  tff(f_45, axiom, (![A, B, C, D]: ((k2_zfmisc_1(A, B) = k2_zfmisc_1(C, D)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | ((A = C) & (B = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t134_zfmisc_1)).
% 2.91/1.44  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.91/1.44  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, A) = k2_zfmisc_1(B, B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_zfmisc_1)).
% 2.91/1.44  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.91/1.44  tff(c_14, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k3_zfmisc_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.44  tff(c_18, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.91/1.44  tff(c_186, plain, (![D_28, B_29, A_30, C_31]: (D_28=B_29 | k1_xboole_0=B_29 | k1_xboole_0=A_30 | k2_zfmisc_1(C_31, D_28)!=k2_zfmisc_1(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.91/1.44  tff(c_429, plain, (![C_62, C_63, B_61, A_64, D_60]: (D_60=C_62 | k1_xboole_0=C_62 | k2_zfmisc_1(A_64, B_61)=k1_xboole_0 | k3_zfmisc_1(A_64, B_61, C_62)!=k2_zfmisc_1(C_63, D_60))), inference(superposition, [status(thm), theory('equality')], [c_14, c_186])).
% 2.91/1.44  tff(c_447, plain, (![D_60, C_63]: (D_60='#skF_2' | k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_63, D_60))), inference(superposition, [status(thm), theory('equality')], [c_18, c_429])).
% 2.91/1.44  tff(c_468, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_447])).
% 2.91/1.44  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.44  tff(c_60, plain, (![B_16, A_17]: (B_16=A_17 | k2_zfmisc_1(B_16, B_16)!=k2_zfmisc_1(A_17, A_17))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.44  tff(c_64, plain, (![A_17]: (k1_xboole_0=A_17 | k2_zfmisc_1(A_17, A_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 2.91/1.44  tff(c_514, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_468, c_64])).
% 2.91/1.44  tff(c_90, plain, (![A_19, B_20, C_21]: (k2_zfmisc_1(k2_zfmisc_1(A_19, B_20), C_21)=k3_zfmisc_1(A_19, B_20, C_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.91/1.44  tff(c_124, plain, (![B_2, C_21]: (k3_zfmisc_1(k1_xboole_0, B_2, C_21)=k2_zfmisc_1(k1_xboole_0, C_21))), inference(superposition, [status(thm), theory('equality')], [c_6, c_90])).
% 2.91/1.44  tff(c_134, plain, (![B_2, C_21]: (k3_zfmisc_1(k1_xboole_0, B_2, C_21)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_124])).
% 2.91/1.44  tff(c_528, plain, (![B_2, C_21]: (k3_zfmisc_1('#skF_2', B_2, C_21)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_514, c_514, c_134])).
% 2.91/1.44  tff(c_648, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_528, c_18])).
% 2.91/1.44  tff(c_2, plain, (![B_2, A_1]: (k1_xboole_0=B_2 | k1_xboole_0=A_1 | k2_zfmisc_1(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.91/1.44  tff(c_207, plain, (![C_32, A_33, B_34]: (k1_xboole_0=C_32 | k2_zfmisc_1(A_33, B_34)=k1_xboole_0 | k3_zfmisc_1(A_33, B_34, C_32)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_2])).
% 2.91/1.44  tff(c_219, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_18, c_207])).
% 2.91/1.44  tff(c_253, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_219])).
% 2.91/1.44  tff(c_523, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_514, c_253])).
% 2.91/1.44  tff(c_746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_648, c_523])).
% 2.91/1.44  tff(c_747, plain, (![D_60, C_63]: (k1_xboole_0='#skF_2' | D_60='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_63, D_60))), inference(splitRight, [status(thm)], [c_447])).
% 2.91/1.44  tff(c_779, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_747])).
% 2.91/1.44  tff(c_797, plain, (![B_2]: (k2_zfmisc_1('#skF_2', B_2)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_779, c_779, c_6])).
% 2.91/1.44  tff(c_748, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_447])).
% 2.91/1.44  tff(c_781, plain, (k2_zfmisc_1('#skF_2', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_779, c_748])).
% 2.91/1.44  tff(c_873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_797, c_781])).
% 2.91/1.44  tff(c_876, plain, (![D_87, C_88]: (D_87='#skF_2' | k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')!=k2_zfmisc_1(C_88, D_87))), inference(splitRight, [status(thm)], [c_747])).
% 2.91/1.44  tff(c_879, plain, (![C_11, A_9, B_10]: (C_11='#skF_2' | k3_zfmisc_1(A_9, B_10, C_11)!=k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_876])).
% 2.91/1.44  tff(c_889, plain, ('#skF_2'='#skF_1'), inference(reflexivity, [status(thm), theory('equality')], [c_879])).
% 2.91/1.44  tff(c_891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_889])).
% 2.91/1.44  tff(c_892, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_219])).
% 2.91/1.44  tff(c_936, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_892])).
% 2.91/1.44  tff(c_893, plain, (k3_zfmisc_1('#skF_1', '#skF_1', '#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_219])).
% 2.91/1.44  tff(c_111, plain, (![C_21, A_19, B_20]: (k1_xboole_0=C_21 | k2_zfmisc_1(A_19, B_20)=k1_xboole_0 | k3_zfmisc_1(A_19, B_20, C_21)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_90, c_2])).
% 2.91/1.44  tff(c_926, plain, (k1_xboole_0='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_893, c_111])).
% 2.91/1.44  tff(c_1066, plain, ('#skF_2'='#skF_1' | k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_936, c_936, c_926])).
% 2.91/1.44  tff(c_1067, plain, (k2_zfmisc_1('#skF_1', '#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_16, c_1066])).
% 2.91/1.44  tff(c_1140, plain, (![A_106]: (A_106='#skF_2' | k2_zfmisc_1(A_106, A_106)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_936, c_936, c_64])).
% 2.91/1.44  tff(c_1143, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1067, c_1140])).
% 2.91/1.44  tff(c_1159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_1143])).
% 2.91/1.44  tff(c_1161, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_892])).
% 2.91/1.44  tff(c_919, plain, (k3_zfmisc_1('#skF_2', '#skF_2', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_893, c_18])).
% 2.91/1.44  tff(c_934, plain, (k1_xboole_0='#skF_2' | k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_919, c_111])).
% 2.91/1.44  tff(c_1162, plain, (k2_zfmisc_1('#skF_2', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_1161, c_934])).
% 2.91/1.44  tff(c_1184, plain, (k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1162, c_64])).
% 2.91/1.44  tff(c_1204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1161, c_1184])).
% 2.91/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.44  
% 2.91/1.44  Inference rules
% 2.91/1.44  ----------------------
% 2.91/1.44  #Ref     : 5
% 2.91/1.44  #Sup     : 287
% 2.91/1.44  #Fact    : 0
% 2.91/1.44  #Define  : 0
% 2.91/1.44  #Split   : 5
% 2.91/1.44  #Chain   : 0
% 2.91/1.44  #Close   : 0
% 2.91/1.44  
% 2.91/1.44  Ordering : KBO
% 2.91/1.44  
% 2.91/1.44  Simplification rules
% 2.91/1.44  ----------------------
% 2.91/1.44  #Subsume      : 44
% 2.91/1.44  #Demod        : 221
% 2.91/1.44  #Tautology    : 159
% 2.91/1.44  #SimpNegUnit  : 10
% 2.91/1.44  #BackRed      : 52
% 2.91/1.44  
% 2.91/1.44  #Partial instantiations: 0
% 2.91/1.44  #Strategies tried      : 1
% 2.91/1.44  
% 2.91/1.44  Timing (in seconds)
% 2.91/1.44  ----------------------
% 2.91/1.44  Preprocessing        : 0.28
% 2.91/1.44  Parsing              : 0.15
% 2.91/1.44  CNF conversion       : 0.02
% 2.91/1.44  Main loop            : 0.39
% 2.91/1.44  Inferencing          : 0.13
% 2.91/1.44  Reduction            : 0.11
% 2.91/1.44  Demodulation         : 0.08
% 2.91/1.44  BG Simplification    : 0.02
% 2.91/1.44  Subsumption          : 0.10
% 2.91/1.44  Abstraction          : 0.02
% 2.91/1.44  MUC search           : 0.00
% 2.91/1.44  Cooper               : 0.00
% 2.91/1.44  Total                : 0.70
% 2.91/1.44  Index Insertion      : 0.00
% 2.91/1.44  Index Deletion       : 0.00
% 2.91/1.44  Index Matching       : 0.00
% 2.91/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
