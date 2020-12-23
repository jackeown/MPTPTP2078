%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:56 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :   60 (  82 expanded)
%              Number of leaves         :   22 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 100 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_xboole_0(A,B)
          | r1_xboole_0(C,D) )
       => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1049,plain,(
    ! [B_73,A_74] :
      ( r1_xboole_0(B_73,A_74)
      | ~ r1_xboole_0(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1055,plain,(
    ! [A_7] : r1_xboole_0(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_10,c_1049])).

tff(c_20,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1173,plain,(
    ! [A_87,B_88] : k4_xboole_0(A_87,k4_xboole_0(A_87,B_88)) = k3_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1205,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1173])).

tff(c_1209,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1205])).

tff(c_69,plain,(
    ! [B_23,A_24] :
      ( r1_xboole_0(B_23,A_24)
      | ~ r1_xboole_0(A_24,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_7] : r1_xboole_0(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_10,c_69])).

tff(c_22,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_163,plain,(
    ! [A_35,B_36] : k4_xboole_0(A_35,k4_xboole_0(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_195,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_163])).

tff(c_199,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_195])).

tff(c_28,plain,
    ( r1_xboole_0('#skF_3','#skF_4')
    | r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_68,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_93,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = A_28
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_112,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_68,c_93])).

tff(c_192,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_163])).

tff(c_305,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_192])).

tff(c_469,plain,(
    ! [A_51,C_52,B_53,D_54] : k3_xboole_0(k2_zfmisc_1(A_51,C_52),k2_zfmisc_1(B_53,D_54)) = k2_zfmisc_1(k3_xboole_0(A_51,B_53),k3_xboole_0(C_52,D_54)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( ~ r1_xboole_0(k3_xboole_0(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_953,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_69,B_70),k3_xboole_0(C_71,D_72)),k2_zfmisc_1(B_70,D_72))
      | r1_xboole_0(k2_zfmisc_1(A_69,C_71),k2_zfmisc_1(B_70,D_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_12])).

tff(c_980,plain,(
    ! [C_71,D_72] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k1_xboole_0,k3_xboole_0(C_71,D_72)),k2_zfmisc_1('#skF_2',D_72))
      | r1_xboole_0(k2_zfmisc_1('#skF_1',C_71),k2_zfmisc_1('#skF_2',D_72)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_953])).

tff(c_1027,plain,(
    ! [C_71,D_72] : r1_xboole_0(k2_zfmisc_1('#skF_1',C_71),k2_zfmisc_1('#skF_2',D_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_22,c_980])).

tff(c_26,plain,(
    ~ r1_xboole_0(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1046,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_26])).

tff(c_1047,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_1065,plain,(
    ! [A_76,B_77] :
      ( k4_xboole_0(A_76,B_77) = A_76
      | ~ r1_xboole_0(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1080,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1047,c_1065])).

tff(c_1202,plain,(
    k4_xboole_0('#skF_3','#skF_3') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1080,c_1173])).

tff(c_1329,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1209,c_1202])).

tff(c_1210,plain,(
    ! [A_89,C_90,B_91,D_92] : k3_xboole_0(k2_zfmisc_1(A_89,C_90),k2_zfmisc_1(B_91,D_92)) = k2_zfmisc_1(k3_xboole_0(A_89,B_91),k3_xboole_0(C_90,D_92)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1650,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_109,B_110),k3_xboole_0(C_111,D_112)),k2_zfmisc_1(B_110,D_112))
      | r1_xboole_0(k2_zfmisc_1(A_109,C_111),k2_zfmisc_1(B_110,D_112)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1210,c_12])).

tff(c_1662,plain,(
    ! [A_109,B_110] :
      ( ~ r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_109,B_110),k1_xboole_0),k2_zfmisc_1(B_110,'#skF_4'))
      | r1_xboole_0(k2_zfmisc_1(A_109,'#skF_3'),k2_zfmisc_1(B_110,'#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1329,c_1650])).

tff(c_1706,plain,(
    ! [A_109,B_110] : r1_xboole_0(k2_zfmisc_1(A_109,'#skF_3'),k2_zfmisc_1(B_110,'#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1055,c_20,c_1662])).

tff(c_1739,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1706,c_26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.57  
% 3.32/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.57  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.32/1.57  
% 3.32/1.57  %Foreground sorts:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Background operators:
% 3.32/1.57  
% 3.32/1.57  
% 3.32/1.57  %Foreground operators:
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.32/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.32/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.32/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.32/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.32/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.32/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.32/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.32/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.32/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.32/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.32/1.57  
% 3.32/1.59  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.32/1.59  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.32/1.59  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.32/1.59  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.32/1.59  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.32/1.59  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.32/1.59  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 3.32/1.59  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.32/1.59  tff(f_55, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 3.32/1.59  tff(f_43, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 3.32/1.59  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.32/1.59  tff(c_1049, plain, (![B_73, A_74]: (r1_xboole_0(B_73, A_74) | ~r1_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.59  tff(c_1055, plain, (![A_7]: (r1_xboole_0(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_10, c_1049])).
% 3.32/1.59  tff(c_20, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.59  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.32/1.59  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.32/1.59  tff(c_1173, plain, (![A_87, B_88]: (k4_xboole_0(A_87, k4_xboole_0(A_87, B_88))=k3_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.59  tff(c_1205, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1173])).
% 3.32/1.59  tff(c_1209, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1205])).
% 3.32/1.59  tff(c_69, plain, (![B_23, A_24]: (r1_xboole_0(B_23, A_24) | ~r1_xboole_0(A_24, B_23))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.32/1.59  tff(c_75, plain, (![A_7]: (r1_xboole_0(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_10, c_69])).
% 3.32/1.59  tff(c_22, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.32/1.59  tff(c_163, plain, (![A_35, B_36]: (k4_xboole_0(A_35, k4_xboole_0(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.32/1.59  tff(c_195, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_163])).
% 3.32/1.59  tff(c_199, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_195])).
% 3.32/1.59  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_4') | r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.32/1.59  tff(c_68, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_28])).
% 3.32/1.59  tff(c_93, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=A_28 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.59  tff(c_112, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_68, c_93])).
% 3.32/1.59  tff(c_192, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_112, c_163])).
% 3.32/1.59  tff(c_305, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_199, c_192])).
% 3.32/1.59  tff(c_469, plain, (![A_51, C_52, B_53, D_54]: (k3_xboole_0(k2_zfmisc_1(A_51, C_52), k2_zfmisc_1(B_53, D_54))=k2_zfmisc_1(k3_xboole_0(A_51, B_53), k3_xboole_0(C_52, D_54)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.59  tff(c_12, plain, (![A_8, B_9]: (~r1_xboole_0(k3_xboole_0(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.32/1.59  tff(c_953, plain, (![A_69, B_70, C_71, D_72]: (~r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_69, B_70), k3_xboole_0(C_71, D_72)), k2_zfmisc_1(B_70, D_72)) | r1_xboole_0(k2_zfmisc_1(A_69, C_71), k2_zfmisc_1(B_70, D_72)))), inference(superposition, [status(thm), theory('equality')], [c_469, c_12])).
% 3.32/1.59  tff(c_980, plain, (![C_71, D_72]: (~r1_xboole_0(k2_zfmisc_1(k1_xboole_0, k3_xboole_0(C_71, D_72)), k2_zfmisc_1('#skF_2', D_72)) | r1_xboole_0(k2_zfmisc_1('#skF_1', C_71), k2_zfmisc_1('#skF_2', D_72)))), inference(superposition, [status(thm), theory('equality')], [c_305, c_953])).
% 3.32/1.59  tff(c_1027, plain, (![C_71, D_72]: (r1_xboole_0(k2_zfmisc_1('#skF_1', C_71), k2_zfmisc_1('#skF_2', D_72)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_22, c_980])).
% 3.32/1.59  tff(c_26, plain, (~r1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.32/1.59  tff(c_1046, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1027, c_26])).
% 3.32/1.59  tff(c_1047, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 3.32/1.59  tff(c_1065, plain, (![A_76, B_77]: (k4_xboole_0(A_76, B_77)=A_76 | ~r1_xboole_0(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.32/1.59  tff(c_1080, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_1047, c_1065])).
% 3.32/1.59  tff(c_1202, plain, (k4_xboole_0('#skF_3', '#skF_3')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1080, c_1173])).
% 3.32/1.59  tff(c_1329, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1209, c_1202])).
% 3.32/1.59  tff(c_1210, plain, (![A_89, C_90, B_91, D_92]: (k3_xboole_0(k2_zfmisc_1(A_89, C_90), k2_zfmisc_1(B_91, D_92))=k2_zfmisc_1(k3_xboole_0(A_89, B_91), k3_xboole_0(C_90, D_92)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.32/1.59  tff(c_1650, plain, (![A_109, B_110, C_111, D_112]: (~r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_109, B_110), k3_xboole_0(C_111, D_112)), k2_zfmisc_1(B_110, D_112)) | r1_xboole_0(k2_zfmisc_1(A_109, C_111), k2_zfmisc_1(B_110, D_112)))), inference(superposition, [status(thm), theory('equality')], [c_1210, c_12])).
% 3.32/1.59  tff(c_1662, plain, (![A_109, B_110]: (~r1_xboole_0(k2_zfmisc_1(k3_xboole_0(A_109, B_110), k1_xboole_0), k2_zfmisc_1(B_110, '#skF_4')) | r1_xboole_0(k2_zfmisc_1(A_109, '#skF_3'), k2_zfmisc_1(B_110, '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_1329, c_1650])).
% 3.32/1.59  tff(c_1706, plain, (![A_109, B_110]: (r1_xboole_0(k2_zfmisc_1(A_109, '#skF_3'), k2_zfmisc_1(B_110, '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1055, c_20, c_1662])).
% 3.32/1.59  tff(c_1739, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1706, c_26])).
% 3.32/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.32/1.59  
% 3.32/1.59  Inference rules
% 3.32/1.59  ----------------------
% 3.32/1.59  #Ref     : 0
% 3.32/1.59  #Sup     : 403
% 3.32/1.59  #Fact    : 0
% 3.32/1.59  #Define  : 0
% 3.32/1.59  #Split   : 1
% 3.32/1.59  #Chain   : 0
% 3.32/1.59  #Close   : 0
% 3.32/1.59  
% 3.32/1.59  Ordering : KBO
% 3.32/1.59  
% 3.32/1.59  Simplification rules
% 3.32/1.59  ----------------------
% 3.32/1.59  #Subsume      : 22
% 3.32/1.59  #Demod        : 455
% 3.32/1.59  #Tautology    : 254
% 3.32/1.59  #SimpNegUnit  : 0
% 3.32/1.59  #BackRed      : 2
% 3.32/1.59  
% 3.32/1.59  #Partial instantiations: 0
% 3.32/1.59  #Strategies tried      : 1
% 3.32/1.59  
% 3.32/1.59  Timing (in seconds)
% 3.32/1.59  ----------------------
% 3.32/1.59  Preprocessing        : 0.30
% 3.32/1.59  Parsing              : 0.16
% 3.32/1.59  CNF conversion       : 0.02
% 3.32/1.59  Main loop            : 0.52
% 3.32/1.59  Inferencing          : 0.20
% 3.32/1.59  Reduction            : 0.19
% 3.32/1.59  Demodulation         : 0.14
% 3.32/1.59  BG Simplification    : 0.02
% 3.32/1.59  Subsumption          : 0.08
% 3.32/1.59  Abstraction          : 0.04
% 3.32/1.59  MUC search           : 0.00
% 3.32/1.59  Cooper               : 0.00
% 3.32/1.59  Total                : 0.86
% 3.32/1.59  Index Insertion      : 0.00
% 3.32/1.59  Index Deletion       : 0.00
% 3.32/1.59  Index Matching       : 0.00
% 3.32/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
