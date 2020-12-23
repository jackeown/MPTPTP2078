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
% DateTime   : Thu Dec  3 10:02:09 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   47 (  63 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   71 ( 114 expanded)
%              Number of equality atoms :   38 (  70 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
              & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
     => ( k2_zfmisc_1(A,B) = k1_xboole_0
        | ( r1_tarski(A,C)
          & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_18,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_786,plain,(
    ! [B_77,D_78,A_79,C_80] :
      ( r1_tarski(B_77,D_78)
      | k2_zfmisc_1(A_79,B_77) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_79,B_77),k2_zfmisc_1(C_80,D_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_799,plain,(
    ! [B_77,A_79] :
      ( r1_tarski(B_77,k2_relat_1(k2_zfmisc_1(A_79,B_77)))
      | k2_zfmisc_1(A_79,B_77) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_79,B_77)) ) ),
    inference(resolution,[status(thm)],[c_24,c_786])).

tff(c_827,plain,(
    ! [B_81,A_82] :
      ( r1_tarski(B_81,k2_relat_1(k2_zfmisc_1(A_82,B_81)))
      | k2_zfmisc_1(A_82,B_81) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_799])).

tff(c_22,plain,(
    ! [A_13,B_14] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_13,B_14)),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_550,plain,(
    ! [B_62,A_63] :
      ( B_62 = A_63
      | ~ r1_tarski(B_62,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_564,plain,(
    ! [A_13,B_14] :
      ( k2_relat_1(k2_zfmisc_1(A_13,B_14)) = B_14
      | ~ r1_tarski(B_14,k2_relat_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(resolution,[status(thm)],[c_22,c_550])).

tff(c_850,plain,(
    ! [A_83,B_84] :
      ( k2_relat_1(k2_zfmisc_1(A_83,B_84)) = B_84
      | k2_zfmisc_1(A_83,B_84) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_827,c_564])).

tff(c_369,plain,(
    ! [A_50,C_51,B_52,D_53] :
      ( r1_tarski(A_50,C_51)
      | k2_zfmisc_1(A_50,B_52) = k1_xboole_0
      | ~ r1_tarski(k2_zfmisc_1(A_50,B_52),k2_zfmisc_1(C_51,D_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_373,plain,(
    ! [A_50,B_52] :
      ( r1_tarski(A_50,k1_relat_1(k2_zfmisc_1(A_50,B_52)))
      | k2_zfmisc_1(A_50,B_52) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(A_50,B_52)) ) ),
    inference(resolution,[status(thm)],[c_24,c_369])).

tff(c_397,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(A_54,k1_relat_1(k2_zfmisc_1(A_54,B_55)))
      | k2_zfmisc_1(A_54,B_55) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_373])).

tff(c_20,plain,(
    ! [A_11,B_12] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_11,B_12)),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_79,plain,(
    ! [B_27,A_28] :
      ( B_27 = A_28
      | ~ r1_tarski(B_27,A_28)
      | ~ r1_tarski(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,(
    ! [A_11,B_12] :
      ( k1_relat_1(k2_zfmisc_1(A_11,B_12)) = A_11
      | ~ r1_tarski(A_11,k1_relat_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(resolution,[status(thm)],[c_20,c_79])).

tff(c_420,plain,(
    ! [A_56,B_57] :
      ( k1_relat_1(k2_zfmisc_1(A_56,B_57)) = A_56
      | k2_zfmisc_1(A_56,B_57) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_397,c_91])).

tff(c_26,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_2'
    | k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_68,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_463,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_68])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_505,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_8])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_505])).

tff(c_530,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_906,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_530])).

tff(c_940,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_906,c_8])).

tff(c_959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.64/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.39  
% 2.64/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.39  %$ r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.64/1.39  
% 2.64/1.39  %Foreground sorts:
% 2.64/1.39  
% 2.64/1.39  
% 2.64/1.39  %Background operators:
% 2.64/1.39  
% 2.64/1.39  
% 2.64/1.39  %Foreground operators:
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.64/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.64/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.64/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.64/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.64/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.64/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.64/1.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.64/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.64/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.64/1.39  
% 2.64/1.41  tff(f_68, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 2.64/1.41  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.64/1.41  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.64/1.41  tff(f_45, axiom, (![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 2.64/1.41  tff(f_51, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 2.64/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.64/1.41  tff(f_49, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 2.64/1.41  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.64/1.41  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.41  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.41  tff(c_18, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.64/1.41  tff(c_24, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.64/1.41  tff(c_786, plain, (![B_77, D_78, A_79, C_80]: (r1_tarski(B_77, D_78) | k2_zfmisc_1(A_79, B_77)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_79, B_77), k2_zfmisc_1(C_80, D_78)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.41  tff(c_799, plain, (![B_77, A_79]: (r1_tarski(B_77, k2_relat_1(k2_zfmisc_1(A_79, B_77))) | k2_zfmisc_1(A_79, B_77)=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_79, B_77)))), inference(resolution, [status(thm)], [c_24, c_786])).
% 2.64/1.41  tff(c_827, plain, (![B_81, A_82]: (r1_tarski(B_81, k2_relat_1(k2_zfmisc_1(A_82, B_81))) | k2_zfmisc_1(A_82, B_81)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_799])).
% 2.64/1.41  tff(c_22, plain, (![A_13, B_14]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_13, B_14)), B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.64/1.41  tff(c_550, plain, (![B_62, A_63]: (B_62=A_63 | ~r1_tarski(B_62, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.41  tff(c_564, plain, (![A_13, B_14]: (k2_relat_1(k2_zfmisc_1(A_13, B_14))=B_14 | ~r1_tarski(B_14, k2_relat_1(k2_zfmisc_1(A_13, B_14))))), inference(resolution, [status(thm)], [c_22, c_550])).
% 2.64/1.41  tff(c_850, plain, (![A_83, B_84]: (k2_relat_1(k2_zfmisc_1(A_83, B_84))=B_84 | k2_zfmisc_1(A_83, B_84)=k1_xboole_0)), inference(resolution, [status(thm)], [c_827, c_564])).
% 2.64/1.41  tff(c_369, plain, (![A_50, C_51, B_52, D_53]: (r1_tarski(A_50, C_51) | k2_zfmisc_1(A_50, B_52)=k1_xboole_0 | ~r1_tarski(k2_zfmisc_1(A_50, B_52), k2_zfmisc_1(C_51, D_53)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.64/1.41  tff(c_373, plain, (![A_50, B_52]: (r1_tarski(A_50, k1_relat_1(k2_zfmisc_1(A_50, B_52))) | k2_zfmisc_1(A_50, B_52)=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(A_50, B_52)))), inference(resolution, [status(thm)], [c_24, c_369])).
% 2.64/1.41  tff(c_397, plain, (![A_54, B_55]: (r1_tarski(A_54, k1_relat_1(k2_zfmisc_1(A_54, B_55))) | k2_zfmisc_1(A_54, B_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_373])).
% 2.64/1.41  tff(c_20, plain, (![A_11, B_12]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_11, B_12)), A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.64/1.41  tff(c_79, plain, (![B_27, A_28]: (B_27=A_28 | ~r1_tarski(B_27, A_28) | ~r1_tarski(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.41  tff(c_91, plain, (![A_11, B_12]: (k1_relat_1(k2_zfmisc_1(A_11, B_12))=A_11 | ~r1_tarski(A_11, k1_relat_1(k2_zfmisc_1(A_11, B_12))))), inference(resolution, [status(thm)], [c_20, c_79])).
% 2.64/1.41  tff(c_420, plain, (![A_56, B_57]: (k1_relat_1(k2_zfmisc_1(A_56, B_57))=A_56 | k2_zfmisc_1(A_56, B_57)=k1_xboole_0)), inference(resolution, [status(thm)], [c_397, c_91])).
% 2.64/1.41  tff(c_26, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_2' | k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.41  tff(c_68, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_26])).
% 2.64/1.41  tff(c_463, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_420, c_68])).
% 2.64/1.41  tff(c_8, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.64/1.41  tff(c_505, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_463, c_8])).
% 2.64/1.41  tff(c_529, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_505])).
% 2.64/1.41  tff(c_530, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.64/1.41  tff(c_906, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_850, c_530])).
% 2.64/1.41  tff(c_940, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_906, c_8])).
% 2.64/1.41  tff(c_959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_940])).
% 2.64/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/1.41  
% 2.64/1.41  Inference rules
% 2.64/1.41  ----------------------
% 2.64/1.41  #Ref     : 0
% 2.64/1.41  #Sup     : 208
% 2.64/1.41  #Fact    : 0
% 2.64/1.41  #Define  : 0
% 2.64/1.41  #Split   : 2
% 2.64/1.41  #Chain   : 0
% 2.64/1.41  #Close   : 0
% 2.64/1.41  
% 2.64/1.41  Ordering : KBO
% 2.64/1.41  
% 2.64/1.41  Simplification rules
% 2.64/1.41  ----------------------
% 2.64/1.41  #Subsume      : 18
% 2.64/1.41  #Demod        : 176
% 2.64/1.41  #Tautology    : 129
% 2.64/1.41  #SimpNegUnit  : 2
% 2.64/1.41  #BackRed      : 9
% 2.64/1.41  
% 2.64/1.41  #Partial instantiations: 0
% 2.64/1.41  #Strategies tried      : 1
% 2.64/1.41  
% 2.64/1.41  Timing (in seconds)
% 2.64/1.41  ----------------------
% 2.64/1.41  Preprocessing        : 0.28
% 2.64/1.41  Parsing              : 0.15
% 2.64/1.41  CNF conversion       : 0.02
% 2.64/1.41  Main loop            : 0.33
% 2.64/1.41  Inferencing          : 0.12
% 2.64/1.41  Reduction            : 0.11
% 2.64/1.41  Demodulation         : 0.09
% 2.64/1.41  BG Simplification    : 0.01
% 2.64/1.41  Subsumption          : 0.06
% 2.64/1.41  Abstraction          : 0.02
% 2.64/1.41  MUC search           : 0.00
% 2.64/1.41  Cooper               : 0.00
% 2.64/1.41  Total                : 0.64
% 2.64/1.41  Index Insertion      : 0.00
% 2.64/1.41  Index Deletion       : 0.00
% 2.64/1.41  Index Matching       : 0.00
% 2.64/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
