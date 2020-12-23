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
% DateTime   : Thu Dec  3 10:28:24 EST 2020

% Result     : Theorem 3.13s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 241 expanded)
%              Number of leaves         :   23 (  90 expanded)
%              Depth                    :   11
%              Number of atoms          :  106 ( 464 expanded)
%              Number of equality atoms :   60 ( 195 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_67,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_161,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_14,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_62])).

tff(c_170,plain,(
    ! [A_43,B_44] : k4_xboole_0(k3_xboole_0(A_43,B_44),A_43) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_73])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_32,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_339,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(A_56,B_55)
      | ~ v1_zfmisc_1(B_55)
      | v1_xboole_0(B_55)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1221,plain,(
    ! [B_84,A_85] :
      ( B_84 = A_85
      | ~ v1_zfmisc_1(B_84)
      | v1_xboole_0(B_84)
      | v1_xboole_0(A_85)
      | k4_xboole_0(A_85,B_84) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_339])).

tff(c_1223,plain,(
    ! [A_85] :
      ( A_85 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_85)
      | k4_xboole_0(A_85,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_32,c_1221])).

tff(c_1227,plain,(
    ! [A_86] :
      ( A_86 = '#skF_1'
      | v1_xboole_0(A_86)
      | k4_xboole_0(A_86,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1223])).

tff(c_30,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1235,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1227,c_30])).

tff(c_1243,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_1235])).

tff(c_16,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_145,plain,(
    ! [B_41,A_42] :
      ( B_41 = A_42
      | ~ r1_tarski(B_41,A_42)
      | ~ r1_tarski(A_42,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_439,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = A_60
      | ~ r1_tarski(A_60,k4_xboole_0(A_60,B_61)) ) ),
    inference(resolution,[status(thm)],[c_14,c_145])).

tff(c_468,plain,(
    ! [A_3,B_61] :
      ( k4_xboole_0(A_3,B_61) = A_3
      | k4_xboole_0(A_3,k4_xboole_0(A_3,B_61)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_439])).

tff(c_480,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = A_62
      | k3_xboole_0(A_62,B_63) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_468])).

tff(c_57,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_61,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_57,c_28])).

tff(c_527,plain,
    ( k1_xboole_0 != '#skF_1'
    | k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_480,c_61])).

tff(c_593,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_527])).

tff(c_1248,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_593])).

tff(c_38,plain,(
    ! [B_25,A_26] :
      ( ~ v1_xboole_0(B_25)
      | B_25 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_41,plain,(
    ! [A_26] :
      ( k1_xboole_0 = A_26
      | ~ v1_xboole_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_1275,plain,(
    ! [A_87] :
      ( k1_xboole_0 = A_87
      | A_87 = '#skF_1'
      | k4_xboole_0(A_87,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1227,c_41])).

tff(c_1349,plain,(
    ! [B_88] :
      ( k3_xboole_0('#skF_1',B_88) = k1_xboole_0
      | k3_xboole_0('#skF_1',B_88) = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_1275])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_196,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = k3_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_161])).

tff(c_75,plain,(
    ! [B_34] : k4_xboole_0(B_34,B_34) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_62])).

tff(c_80,plain,(
    ! [B_34] : r1_tarski(k1_xboole_0,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_14])).

tff(c_221,plain,(
    ! [B_48] :
      ( k1_xboole_0 = B_48
      | ~ r1_tarski(B_48,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_80,c_145])).

tff(c_362,plain,(
    ! [A_57] :
      ( k1_xboole_0 = A_57
      | k4_xboole_0(A_57,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_221])).

tff(c_365,plain,(
    ! [B_2] :
      ( k1_xboole_0 = B_2
      | k3_xboole_0(B_2,B_2) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_362])).

tff(c_1389,plain,
    ( k1_xboole_0 = '#skF_1'
    | k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_365])).

tff(c_1420,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1248,c_1389])).

tff(c_1586,plain,(
    ! [B_93] :
      ( k4_xboole_0('#skF_1',B_93) = k1_xboole_0
      | k4_xboole_0('#skF_1',B_93) = '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_1275])).

tff(c_1721,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1586,c_61])).

tff(c_180,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,k4_xboole_0(A_7,B_8)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_161])).

tff(c_1256,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1243,c_180])).

tff(c_1269,plain,(
    k3_xboole_0('#skF_1',k4_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1256])).

tff(c_1734,plain,(
    k3_xboole_0('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1721,c_1269])).

tff(c_1736,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1420,c_1734])).

tff(c_1738,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1248,c_1736])).

tff(c_1740,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_527])).

tff(c_1741,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1740,c_30])).

tff(c_1744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.13/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.48  
% 3.26/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.49  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.26/1.49  
% 3.26/1.49  %Foreground sorts:
% 3.26/1.49  
% 3.26/1.49  
% 3.26/1.49  %Background operators:
% 3.26/1.49  
% 3.26/1.49  
% 3.26/1.49  %Foreground operators:
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.26/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.26/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.26/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.26/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.26/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.26/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.26/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.26/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.26/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.26/1.49  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.26/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.26/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.26/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.26/1.49  
% 3.26/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.26/1.50  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.26/1.50  tff(f_38, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.26/1.50  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.26/1.50  tff(f_79, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 3.26/1.50  tff(f_67, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.26/1.50  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.50  tff(f_48, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 3.26/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.26/1.50  tff(c_161, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.26/1.50  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.26/1.50  tff(c_62, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.26/1.50  tff(c_73, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_62])).
% 3.26/1.50  tff(c_170, plain, (![A_43, B_44]: (k4_xboole_0(k3_xboole_0(A_43, B_44), A_43)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_161, c_73])).
% 3.26/1.50  tff(c_34, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.50  tff(c_32, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.50  tff(c_10, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.26/1.50  tff(c_339, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(A_56, B_55) | ~v1_zfmisc_1(B_55) | v1_xboole_0(B_55) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.26/1.50  tff(c_1221, plain, (![B_84, A_85]: (B_84=A_85 | ~v1_zfmisc_1(B_84) | v1_xboole_0(B_84) | v1_xboole_0(A_85) | k4_xboole_0(A_85, B_84)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_339])).
% 3.26/1.50  tff(c_1223, plain, (![A_85]: (A_85='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_85) | k4_xboole_0(A_85, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_1221])).
% 3.26/1.50  tff(c_1227, plain, (![A_86]: (A_86='#skF_1' | v1_xboole_0(A_86) | k4_xboole_0(A_86, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_34, c_1223])).
% 3.26/1.50  tff(c_30, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.50  tff(c_1235, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_1227, c_30])).
% 3.26/1.50  tff(c_1243, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_170, c_1235])).
% 3.26/1.50  tff(c_16, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.26/1.50  tff(c_145, plain, (![B_41, A_42]: (B_41=A_42 | ~r1_tarski(B_41, A_42) | ~r1_tarski(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.50  tff(c_439, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=A_60 | ~r1_tarski(A_60, k4_xboole_0(A_60, B_61)))), inference(resolution, [status(thm)], [c_14, c_145])).
% 3.26/1.50  tff(c_468, plain, (![A_3, B_61]: (k4_xboole_0(A_3, B_61)=A_3 | k4_xboole_0(A_3, k4_xboole_0(A_3, B_61))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_439])).
% 3.26/1.50  tff(c_480, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=A_62 | k3_xboole_0(A_62, B_63)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_468])).
% 3.26/1.50  tff(c_57, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.26/1.50  tff(c_28, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.26/1.50  tff(c_61, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_57, c_28])).
% 3.26/1.50  tff(c_527, plain, (k1_xboole_0!='#skF_1' | k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_480, c_61])).
% 3.26/1.50  tff(c_593, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_527])).
% 3.26/1.50  tff(c_1248, plain, (k1_xboole_0!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_593])).
% 3.26/1.50  tff(c_38, plain, (![B_25, A_26]: (~v1_xboole_0(B_25) | B_25=A_26 | ~v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.26/1.50  tff(c_41, plain, (![A_26]: (k1_xboole_0=A_26 | ~v1_xboole_0(A_26))), inference(resolution, [status(thm)], [c_2, c_38])).
% 3.26/1.50  tff(c_1275, plain, (![A_87]: (k1_xboole_0=A_87 | A_87='#skF_1' | k4_xboole_0(A_87, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1227, c_41])).
% 3.26/1.50  tff(c_1349, plain, (![B_88]: (k3_xboole_0('#skF_1', B_88)=k1_xboole_0 | k3_xboole_0('#skF_1', B_88)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_170, c_1275])).
% 3.26/1.50  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.26/1.50  tff(c_74, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_62])).
% 3.26/1.50  tff(c_196, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_74, c_161])).
% 3.26/1.50  tff(c_75, plain, (![B_34]: (k4_xboole_0(B_34, B_34)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_62])).
% 3.26/1.50  tff(c_80, plain, (![B_34]: (r1_tarski(k1_xboole_0, B_34))), inference(superposition, [status(thm), theory('equality')], [c_75, c_14])).
% 3.26/1.50  tff(c_221, plain, (![B_48]: (k1_xboole_0=B_48 | ~r1_tarski(B_48, k1_xboole_0))), inference(resolution, [status(thm)], [c_80, c_145])).
% 3.26/1.50  tff(c_362, plain, (![A_57]: (k1_xboole_0=A_57 | k4_xboole_0(A_57, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_221])).
% 3.26/1.50  tff(c_365, plain, (![B_2]: (k1_xboole_0=B_2 | k3_xboole_0(B_2, B_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_196, c_362])).
% 3.26/1.50  tff(c_1389, plain, (k1_xboole_0='#skF_1' | k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1349, c_365])).
% 3.26/1.50  tff(c_1420, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1248, c_1389])).
% 3.26/1.50  tff(c_1586, plain, (![B_93]: (k4_xboole_0('#skF_1', B_93)=k1_xboole_0 | k4_xboole_0('#skF_1', B_93)='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_73, c_1275])).
% 3.26/1.50  tff(c_1721, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1586, c_61])).
% 3.26/1.50  tff(c_180, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(A_7, k4_xboole_0(A_7, B_8)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_161])).
% 3.26/1.50  tff(c_1256, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1243, c_180])).
% 3.26/1.50  tff(c_1269, plain, (k3_xboole_0('#skF_1', k4_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1256])).
% 3.26/1.50  tff(c_1734, plain, (k3_xboole_0('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1721, c_1269])).
% 3.26/1.50  tff(c_1736, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1420, c_1734])).
% 3.26/1.50  tff(c_1738, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1248, c_1736])).
% 3.26/1.50  tff(c_1740, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_527])).
% 3.26/1.50  tff(c_1741, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1740, c_30])).
% 3.26/1.50  tff(c_1744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_1741])).
% 3.26/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.26/1.50  
% 3.26/1.50  Inference rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Ref     : 0
% 3.26/1.50  #Sup     : 399
% 3.26/1.50  #Fact    : 2
% 3.26/1.50  #Define  : 0
% 3.26/1.50  #Split   : 1
% 3.26/1.50  #Chain   : 0
% 3.26/1.50  #Close   : 0
% 3.26/1.50  
% 3.26/1.50  Ordering : KBO
% 3.26/1.50  
% 3.26/1.50  Simplification rules
% 3.26/1.50  ----------------------
% 3.26/1.50  #Subsume      : 49
% 3.26/1.50  #Demod        : 297
% 3.26/1.50  #Tautology    : 207
% 3.26/1.50  #SimpNegUnit  : 28
% 3.26/1.50  #BackRed      : 6
% 3.26/1.50  
% 3.26/1.50  #Partial instantiations: 0
% 3.26/1.50  #Strategies tried      : 1
% 3.26/1.50  
% 3.26/1.50  Timing (in seconds)
% 3.26/1.50  ----------------------
% 3.26/1.50  Preprocessing        : 0.29
% 3.26/1.50  Parsing              : 0.16
% 3.26/1.50  CNF conversion       : 0.02
% 3.26/1.50  Main loop            : 0.45
% 3.26/1.50  Inferencing          : 0.16
% 3.26/1.50  Reduction            : 0.16
% 3.26/1.50  Demodulation         : 0.12
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.08
% 3.26/1.50  Abstraction          : 0.03
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.77
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
