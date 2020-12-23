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
% DateTime   : Thu Dec  3 09:59:26 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   45 (  82 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 152 expanded)
%              Number of equality atoms :   32 (  84 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_12,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_52,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_74,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_1')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_74])).

tff(c_79,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_14,c_77])).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [A_20,B_21,C_22] :
      ( k1_xboole_0 = A_20
      | ~ r1_xboole_0(B_21,C_22)
      | ~ r1_tarski(A_20,C_22)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_84,plain,(
    ! [A_23,B_24,A_25] :
      ( k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,B_24)
      | ~ r1_tarski(A_23,A_25)
      | k4_xboole_0(A_25,B_24) != A_25 ) ),
    inference(resolution,[status(thm)],[c_8,c_80])).

tff(c_86,plain,(
    ! [A_25] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski('#skF_1',A_25)
      | k4_xboole_0(A_25,k1_xboole_0) != A_25 ) ),
    inference(resolution,[status(thm)],[c_79,c_84])).

tff(c_93,plain,(
    ! [A_26] :
      ( ~ r1_tarski('#skF_1',A_26)
      | k4_xboole_0(A_26,k1_xboole_0) != A_26 ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_86])).

tff(c_96,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_79,c_93])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_96])).

tff(c_105,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_128,plain,(
    ! [A_33] :
      ( r1_tarski(A_33,k2_zfmisc_1(k1_relat_1(A_33),k2_relat_1(A_33)))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_131,plain,
    ( r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_128])).

tff(c_133,plain,(
    r1_tarski('#skF_1',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_12,c_131])).

tff(c_134,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_xboole_0 = A_34
      | ~ r1_xboole_0(B_35,C_36)
      | ~ r1_tarski(A_34,C_36)
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_138,plain,(
    ! [A_37,B_38,A_39] :
      ( k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,B_38)
      | ~ r1_tarski(A_37,A_39)
      | k4_xboole_0(A_39,B_38) != A_39 ) ),
    inference(resolution,[status(thm)],[c_8,c_134])).

tff(c_140,plain,(
    ! [A_39] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski('#skF_1',A_39)
      | k4_xboole_0(A_39,k1_xboole_0) != A_39 ) ),
    inference(resolution,[status(thm)],[c_133,c_138])).

tff(c_147,plain,(
    ! [A_40] :
      ( ~ r1_tarski('#skF_1',A_40)
      | k4_xboole_0(A_40,k1_xboole_0) != A_40 ) ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_140])).

tff(c_150,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_133,c_147])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_150])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  
% 1.60/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.14  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.60/1.14  
% 1.60/1.14  %Foreground sorts:
% 1.60/1.14  
% 1.60/1.14  
% 1.60/1.14  %Background operators:
% 1.60/1.14  
% 1.60/1.14  
% 1.60/1.14  %Foreground operators:
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.60/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.60/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.14  
% 1.60/1.15  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.60/1.15  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.60/1.15  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.60/1.15  tff(f_49, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.60/1.15  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.60/1.15  tff(f_35, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.60/1.15  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.15  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.60/1.15  tff(c_12, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.15  tff(c_14, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.15  tff(c_20, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.60/1.15  tff(c_52, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_20])).
% 1.60/1.15  tff(c_74, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.60/1.15  tff(c_77, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_1'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_52, c_74])).
% 1.60/1.15  tff(c_79, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_14, c_77])).
% 1.60/1.15  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.60/1.15  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k4_xboole_0(A_5, B_6)!=A_5)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.60/1.15  tff(c_80, plain, (![A_20, B_21, C_22]: (k1_xboole_0=A_20 | ~r1_xboole_0(B_21, C_22) | ~r1_tarski(A_20, C_22) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.15  tff(c_84, plain, (![A_23, B_24, A_25]: (k1_xboole_0=A_23 | ~r1_tarski(A_23, B_24) | ~r1_tarski(A_23, A_25) | k4_xboole_0(A_25, B_24)!=A_25)), inference(resolution, [status(thm)], [c_8, c_80])).
% 1.60/1.15  tff(c_86, plain, (![A_25]: (k1_xboole_0='#skF_1' | ~r1_tarski('#skF_1', A_25) | k4_xboole_0(A_25, k1_xboole_0)!=A_25)), inference(resolution, [status(thm)], [c_79, c_84])).
% 1.60/1.15  tff(c_93, plain, (![A_26]: (~r1_tarski('#skF_1', A_26) | k4_xboole_0(A_26, k1_xboole_0)!=A_26)), inference(negUnitSimplification, [status(thm)], [c_18, c_86])).
% 1.60/1.15  tff(c_96, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_79, c_93])).
% 1.60/1.15  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_96])).
% 1.60/1.15  tff(c_105, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_20])).
% 1.60/1.15  tff(c_128, plain, (![A_33]: (r1_tarski(A_33, k2_zfmisc_1(k1_relat_1(A_33), k2_relat_1(A_33))) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.60/1.15  tff(c_131, plain, (r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0)) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_105, c_128])).
% 1.60/1.15  tff(c_133, plain, (r1_tarski('#skF_1', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_12, c_131])).
% 1.60/1.15  tff(c_134, plain, (![A_34, B_35, C_36]: (k1_xboole_0=A_34 | ~r1_xboole_0(B_35, C_36) | ~r1_tarski(A_34, C_36) | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.60/1.15  tff(c_138, plain, (![A_37, B_38, A_39]: (k1_xboole_0=A_37 | ~r1_tarski(A_37, B_38) | ~r1_tarski(A_37, A_39) | k4_xboole_0(A_39, B_38)!=A_39)), inference(resolution, [status(thm)], [c_8, c_134])).
% 1.60/1.15  tff(c_140, plain, (![A_39]: (k1_xboole_0='#skF_1' | ~r1_tarski('#skF_1', A_39) | k4_xboole_0(A_39, k1_xboole_0)!=A_39)), inference(resolution, [status(thm)], [c_133, c_138])).
% 1.60/1.15  tff(c_147, plain, (![A_40]: (~r1_tarski('#skF_1', A_40) | k4_xboole_0(A_40, k1_xboole_0)!=A_40)), inference(negUnitSimplification, [status(thm)], [c_18, c_140])).
% 1.60/1.15  tff(c_150, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_133, c_147])).
% 1.60/1.15  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_150])).
% 1.60/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  Inference rules
% 1.60/1.15  ----------------------
% 1.60/1.15  #Ref     : 0
% 1.60/1.15  #Sup     : 30
% 1.60/1.15  #Fact    : 0
% 1.60/1.15  #Define  : 0
% 1.60/1.15  #Split   : 1
% 1.60/1.15  #Chain   : 0
% 1.60/1.15  #Close   : 0
% 1.60/1.15  
% 1.60/1.16  Ordering : KBO
% 1.60/1.16  
% 1.60/1.16  Simplification rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Subsume      : 0
% 1.60/1.16  #Demod        : 6
% 1.60/1.16  #Tautology    : 18
% 1.60/1.16  #SimpNegUnit  : 2
% 1.60/1.16  #BackRed      : 0
% 1.60/1.16  
% 1.60/1.16  #Partial instantiations: 0
% 1.60/1.16  #Strategies tried      : 1
% 1.60/1.16  
% 1.60/1.16  Timing (in seconds)
% 1.60/1.16  ----------------------
% 1.60/1.16  Preprocessing        : 0.27
% 1.60/1.16  Parsing              : 0.14
% 1.60/1.16  CNF conversion       : 0.02
% 1.60/1.16  Main loop            : 0.12
% 1.60/1.16  Inferencing          : 0.05
% 1.60/1.16  Reduction            : 0.04
% 1.60/1.16  Demodulation         : 0.03
% 1.60/1.16  BG Simplification    : 0.01
% 1.60/1.16  Subsumption          : 0.02
% 1.60/1.16  Abstraction          : 0.01
% 1.60/1.16  MUC search           : 0.00
% 1.60/1.16  Cooper               : 0.00
% 1.60/1.16  Total                : 0.42
% 1.60/1.16  Index Insertion      : 0.00
% 1.60/1.16  Index Deletion       : 0.00
% 1.60/1.16  Index Matching       : 0.00
% 1.60/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
