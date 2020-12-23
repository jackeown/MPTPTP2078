%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:38 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   42 (  56 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :   55 (  90 expanded)
%              Number of equality atoms :    8 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

tff(c_29,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(A_16,B_17)
      | k4_xboole_0(A_16,B_17) != A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | k4_xboole_0(A_21,B_20) != A_21 ) ),
    inference(resolution,[status(thm)],[c_29,c_2])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_69,plain,(
    k4_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_58,c_18])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_12] :
      ( r1_tarski(A_12,k2_zfmisc_1(k1_relat_1(A_12),k2_relat_1(A_12)))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_132,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( ~ r1_xboole_0(A_37,B_38)
      | r1_xboole_0(k2_zfmisc_1(A_37,C_39),k2_zfmisc_1(B_38,D_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(A_6,B_7) = A_6
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_166,plain,(
    ! [A_55,C_56,B_57,D_58] :
      ( k4_xboole_0(k2_zfmisc_1(A_55,C_56),k2_zfmisc_1(B_57,D_58)) = k2_zfmisc_1(A_55,C_56)
      | ~ r1_xboole_0(A_55,B_57) ) ),
    inference(resolution,[status(thm)],[c_132,c_8])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_210,plain,(
    ! [B_63,A_66,A_67,C_64,D_65] :
      ( r1_xboole_0(A_67,k2_zfmisc_1(B_63,D_65))
      | ~ r1_tarski(A_67,k2_zfmisc_1(A_66,C_64))
      | ~ r1_xboole_0(A_66,B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_4])).

tff(c_214,plain,(
    ! [A_68,B_69,D_70] :
      ( r1_xboole_0(A_68,k2_zfmisc_1(B_69,D_70))
      | ~ r1_xboole_0(k1_relat_1(A_68),B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(resolution,[status(thm)],[c_16,c_210])).

tff(c_234,plain,(
    ! [D_70] :
      ( r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_70))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_20,c_214])).

tff(c_259,plain,(
    ! [D_72] : r1_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_2'),D_72)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_234])).

tff(c_310,plain,(
    ! [D_78] : r1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'),D_78),'#skF_1') ),
    inference(resolution,[status(thm)],[c_259,c_2])).

tff(c_431,plain,(
    ! [D_102] : k4_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'),D_102),'#skF_1') = k2_zfmisc_1(k1_relat_1('#skF_2'),D_102) ),
    inference(resolution,[status(thm)],[c_310,c_8])).

tff(c_458,plain,(
    ! [A_105,D_106] :
      ( r1_xboole_0(A_105,'#skF_1')
      | ~ r1_tarski(A_105,k2_zfmisc_1(k1_relat_1('#skF_2'),D_106)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_4])).

tff(c_462,plain,
    ( r1_xboole_0('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_458])).

tff(c_465,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_462])).

tff(c_468,plain,(
    k4_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_465,c_8])).

tff(c_474,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_468])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:37:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  
% 2.27/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.35  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.61/1.35  
% 2.61/1.35  %Foreground sorts:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Background operators:
% 2.61/1.35  
% 2.61/1.35  
% 2.61/1.35  %Foreground operators:
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.61/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.35  
% 2.61/1.36  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.61/1.36  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.61/1.36  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.61/1.36  tff(f_49, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.61/1.36  tff(f_45, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.61/1.36  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.61/1.36  tff(c_29, plain, (![A_16, B_17]: (r1_xboole_0(A_16, B_17) | k4_xboole_0(A_16, B_17)!=A_16)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.36  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.36  tff(c_58, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | k4_xboole_0(A_21, B_20)!=A_21)), inference(resolution, [status(thm)], [c_29, c_2])).
% 2.61/1.36  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.36  tff(c_69, plain, (k4_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(resolution, [status(thm)], [c_58, c_18])).
% 2.61/1.36  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.36  tff(c_16, plain, (![A_12]: (r1_tarski(A_12, k2_zfmisc_1(k1_relat_1(A_12), k2_relat_1(A_12))) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.61/1.36  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.36  tff(c_20, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.61/1.36  tff(c_132, plain, (![A_37, B_38, C_39, D_40]: (~r1_xboole_0(A_37, B_38) | r1_xboole_0(k2_zfmisc_1(A_37, C_39), k2_zfmisc_1(B_38, D_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.61/1.36  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, B_7)=A_6 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.36  tff(c_166, plain, (![A_55, C_56, B_57, D_58]: (k4_xboole_0(k2_zfmisc_1(A_55, C_56), k2_zfmisc_1(B_57, D_58))=k2_zfmisc_1(A_55, C_56) | ~r1_xboole_0(A_55, B_57))), inference(resolution, [status(thm)], [c_132, c_8])).
% 2.61/1.36  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.36  tff(c_210, plain, (![B_63, A_66, A_67, C_64, D_65]: (r1_xboole_0(A_67, k2_zfmisc_1(B_63, D_65)) | ~r1_tarski(A_67, k2_zfmisc_1(A_66, C_64)) | ~r1_xboole_0(A_66, B_63))), inference(superposition, [status(thm), theory('equality')], [c_166, c_4])).
% 2.61/1.36  tff(c_214, plain, (![A_68, B_69, D_70]: (r1_xboole_0(A_68, k2_zfmisc_1(B_69, D_70)) | ~r1_xboole_0(k1_relat_1(A_68), B_69) | ~v1_relat_1(A_68))), inference(resolution, [status(thm)], [c_16, c_210])).
% 2.61/1.36  tff(c_234, plain, (![D_70]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_70)) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_214])).
% 2.61/1.36  tff(c_259, plain, (![D_72]: (r1_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_2'), D_72)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_234])).
% 2.61/1.36  tff(c_310, plain, (![D_78]: (r1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'), D_78), '#skF_1'))), inference(resolution, [status(thm)], [c_259, c_2])).
% 2.61/1.36  tff(c_431, plain, (![D_102]: (k4_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_2'), D_102), '#skF_1')=k2_zfmisc_1(k1_relat_1('#skF_2'), D_102))), inference(resolution, [status(thm)], [c_310, c_8])).
% 2.61/1.36  tff(c_458, plain, (![A_105, D_106]: (r1_xboole_0(A_105, '#skF_1') | ~r1_tarski(A_105, k2_zfmisc_1(k1_relat_1('#skF_2'), D_106)))), inference(superposition, [status(thm), theory('equality')], [c_431, c_4])).
% 2.61/1.36  tff(c_462, plain, (r1_xboole_0('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_458])).
% 2.61/1.36  tff(c_465, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_462])).
% 2.61/1.36  tff(c_468, plain, (k4_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_465, c_8])).
% 2.61/1.36  tff(c_474, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_468])).
% 2.61/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  Inference rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Ref     : 0
% 2.61/1.36  #Sup     : 114
% 2.61/1.36  #Fact    : 0
% 2.61/1.36  #Define  : 0
% 2.61/1.36  #Split   : 0
% 2.61/1.36  #Chain   : 0
% 2.61/1.36  #Close   : 0
% 2.61/1.36  
% 2.61/1.36  Ordering : KBO
% 2.61/1.36  
% 2.61/1.36  Simplification rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Subsume      : 10
% 2.61/1.36  #Demod        : 11
% 2.61/1.36  #Tautology    : 37
% 2.61/1.36  #SimpNegUnit  : 1
% 2.61/1.36  #BackRed      : 0
% 2.61/1.36  
% 2.61/1.36  #Partial instantiations: 0
% 2.61/1.36  #Strategies tried      : 1
% 2.61/1.36  
% 2.61/1.36  Timing (in seconds)
% 2.61/1.36  ----------------------
% 2.61/1.36  Preprocessing        : 0.27
% 2.61/1.36  Parsing              : 0.15
% 2.61/1.36  CNF conversion       : 0.02
% 2.61/1.36  Main loop            : 0.33
% 2.61/1.36  Inferencing          : 0.14
% 2.61/1.36  Reduction            : 0.08
% 2.61/1.36  Demodulation         : 0.05
% 2.61/1.36  BG Simplification    : 0.01
% 2.61/1.36  Subsumption          : 0.08
% 2.61/1.36  Abstraction          : 0.01
% 2.61/1.36  MUC search           : 0.00
% 2.61/1.36  Cooper               : 0.00
% 2.61/1.36  Total                : 0.63
% 2.61/1.36  Index Insertion      : 0.00
% 2.61/1.36  Index Deletion       : 0.00
% 2.61/1.36  Index Matching       : 0.00
% 2.61/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
