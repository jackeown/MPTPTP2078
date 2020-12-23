%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:42 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   55 (  71 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 (  95 expanded)
%              Number of equality atoms :   29 (  43 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k7_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k7_relat_1(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_34,plain,
    ( ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3')
    | k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_75,plain,(
    k7_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_12,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_76,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_xboole_0(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_84,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_76])).

tff(c_18,plain,(
    ! [B_12] : k2_zfmisc_1(k1_xboole_0,B_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,(
    ! [B_42,A_43] :
      ( k3_xboole_0(k1_relat_1(B_42),A_43) = k1_relat_1(k7_relat_1(B_42,A_43))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_101,plain,(
    r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_40])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_105,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_195,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_105])).

tff(c_222,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_195])).

tff(c_24,plain,(
    ! [A_17] :
      ( k3_xboole_0(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17))) = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_232,plain,
    ( k3_xboole_0(k7_relat_1('#skF_4','#skF_3'),k2_zfmisc_1(k1_xboole_0,k2_relat_1(k7_relat_1('#skF_4','#skF_3')))) = k7_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_24])).

tff(c_235,plain,
    ( k7_relat_1('#skF_4','#skF_3') = k1_xboole_0
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_18,c_232])).

tff(c_236,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_235])).

tff(c_240,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_236])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_240])).

tff(c_246,plain,(
    k7_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_351,plain,(
    ! [B_58,A_59] :
      ( k3_xboole_0(k1_relat_1(B_58),A_59) = k1_relat_1(k7_relat_1(B_58,A_59))
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_245,plain,(
    ~ r1_xboole_0(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_250,plain,(
    k3_xboole_0(k1_relat_1('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_245])).

tff(c_371,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_250])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_28,c_246,c_371])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:00:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.30  
% 1.99/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.31  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.99/1.31  
% 1.99/1.31  %Foreground sorts:
% 1.99/1.31  
% 1.99/1.31  
% 1.99/1.31  %Background operators:
% 1.99/1.31  
% 1.99/1.31  
% 1.99/1.31  %Foreground operators:
% 1.99/1.31  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.99/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.99/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.99/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.99/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.99/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.31  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.31  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.99/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.99/1.31  
% 1.99/1.32  tff(f_83, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_relat_1)).
% 1.99/1.32  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.99/1.32  tff(f_65, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.99/1.32  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.99/1.32  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.99/1.32  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.99/1.32  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 1.99/1.32  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 1.99/1.32  tff(c_32, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.32  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.99/1.32  tff(c_22, plain, (![A_15, B_16]: (v1_relat_1(k7_relat_1(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.99/1.32  tff(c_34, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3') | k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.32  tff(c_75, plain, (k7_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_34])).
% 1.99/1.32  tff(c_12, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.99/1.32  tff(c_76, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.32  tff(c_84, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_76])).
% 1.99/1.32  tff(c_18, plain, (![B_12]: (k2_zfmisc_1(k1_xboole_0, B_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.32  tff(c_182, plain, (![B_42, A_43]: (k3_xboole_0(k1_relat_1(B_42), A_43)=k1_relat_1(k7_relat_1(B_42, A_43)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.99/1.32  tff(c_40, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.99/1.32  tff(c_101, plain, (r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_75, c_40])).
% 1.99/1.32  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.32  tff(c_105, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_101, c_2])).
% 1.99/1.32  tff(c_195, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_182, c_105])).
% 1.99/1.32  tff(c_222, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_195])).
% 1.99/1.32  tff(c_24, plain, (![A_17]: (k3_xboole_0(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17)))=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.32  tff(c_232, plain, (k3_xboole_0(k7_relat_1('#skF_4', '#skF_3'), k2_zfmisc_1(k1_xboole_0, k2_relat_1(k7_relat_1('#skF_4', '#skF_3'))))=k7_relat_1('#skF_4', '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_222, c_24])).
% 1.99/1.32  tff(c_235, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0 | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_84, c_18, c_232])).
% 1.99/1.32  tff(c_236, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_75, c_235])).
% 1.99/1.32  tff(c_240, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_236])).
% 1.99/1.32  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_240])).
% 1.99/1.32  tff(c_246, plain, (k7_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_34])).
% 1.99/1.32  tff(c_351, plain, (![B_58, A_59]: (k3_xboole_0(k1_relat_1(B_58), A_59)=k1_relat_1(k7_relat_1(B_58, A_59)) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.99/1.32  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.99/1.32  tff(c_245, plain, (~r1_xboole_0(k1_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 1.99/1.32  tff(c_250, plain, (k3_xboole_0(k1_relat_1('#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_4, c_245])).
% 1.99/1.32  tff(c_371, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_351, c_250])).
% 1.99/1.32  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_28, c_246, c_371])).
% 1.99/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.32  
% 1.99/1.32  Inference rules
% 1.99/1.32  ----------------------
% 1.99/1.32  #Ref     : 0
% 1.99/1.32  #Sup     : 83
% 1.99/1.32  #Fact    : 0
% 1.99/1.32  #Define  : 0
% 1.99/1.32  #Split   : 1
% 1.99/1.32  #Chain   : 0
% 1.99/1.32  #Close   : 0
% 1.99/1.32  
% 1.99/1.32  Ordering : KBO
% 1.99/1.32  
% 1.99/1.32  Simplification rules
% 1.99/1.32  ----------------------
% 1.99/1.32  #Subsume      : 3
% 1.99/1.32  #Demod        : 28
% 1.99/1.32  #Tautology    : 51
% 1.99/1.32  #SimpNegUnit  : 6
% 1.99/1.32  #BackRed      : 0
% 1.99/1.32  
% 1.99/1.32  #Partial instantiations: 0
% 1.99/1.32  #Strategies tried      : 1
% 1.99/1.32  
% 1.99/1.32  Timing (in seconds)
% 1.99/1.32  ----------------------
% 1.99/1.32  Preprocessing        : 0.31
% 1.99/1.32  Parsing              : 0.16
% 1.99/1.32  CNF conversion       : 0.02
% 1.99/1.32  Main loop            : 0.20
% 1.99/1.32  Inferencing          : 0.08
% 1.99/1.32  Reduction            : 0.06
% 1.99/1.32  Demodulation         : 0.04
% 1.99/1.32  BG Simplification    : 0.01
% 1.99/1.32  Subsumption          : 0.03
% 1.99/1.32  Abstraction          : 0.01
% 1.99/1.32  MUC search           : 0.00
% 1.99/1.32  Cooper               : 0.00
% 1.99/1.32  Total                : 0.53
% 1.99/1.32  Index Insertion      : 0.00
% 1.99/1.32  Index Deletion       : 0.00
% 1.99/1.32  Index Matching       : 0.00
% 1.99/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
