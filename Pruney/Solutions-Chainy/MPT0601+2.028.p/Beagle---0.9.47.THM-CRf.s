%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:17 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   49 (  72 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 116 expanded)
%              Number of equality atoms :   22 (  39 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k11_relat_1,type,(
    k11_relat_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k1_relat_1(B))
        <=> k11_relat_1(B,A) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k11_relat_1(A,B) = k9_relat_1(A,k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,
    ( r2_hidden('#skF_1',k1_relat_1('#skF_2'))
    | k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_43,plain,(
    k11_relat_1('#skF_2','#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_35,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(k1_tarski(A_17),B_18)
      | r2_hidden(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_38,plain,(
    ! [B_18,A_17] :
      ( r1_xboole_0(B_18,k1_tarski(A_17))
      | r2_hidden(A_17,B_18) ) ),
    inference(resolution,[status(thm)],[c_35,c_2])).

tff(c_75,plain,(
    ! [B_33,A_34] :
      ( k9_relat_1(B_33,A_34) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_33),A_34)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,(
    ! [B_39,A_40] :
      ( k9_relat_1(B_39,k1_tarski(A_40)) = k1_xboole_0
      | ~ v1_relat_1(B_39)
      | r2_hidden(A_40,k1_relat_1(B_39)) ) ),
    inference(resolution,[status(thm)],[c_38,c_75])).

tff(c_18,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_18])).

tff(c_111,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_108,c_44])).

tff(c_114,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_111])).

tff(c_10,plain,(
    ! [A_9,B_11] :
      ( k9_relat_1(A_9,k1_tarski(B_11)) = k11_relat_1(A_9,B_11)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_118,plain,
    ( k11_relat_1('#skF_2','#skF_1') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_125,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_118])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_125])).

tff(c_128,plain,(
    r2_hidden('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_131,plain,(
    k11_relat_1('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_18])).

tff(c_173,plain,(
    ! [B_55,A_56] :
      ( r1_xboole_0(k1_relat_1(B_55),A_56)
      | k9_relat_1(B_55,A_56) != k1_xboole_0
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_181,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(A_57,k1_relat_1(B_58))
      | k9_relat_1(B_58,A_57) != k1_xboole_0
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_173,c_2])).

tff(c_4,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,(
    ! [A_41,C_42,B_43] :
      ( ~ r2_hidden(A_41,C_42)
      | ~ r1_xboole_0(k2_tarski(A_41,B_43),C_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_144,plain,(
    ! [A_3,C_42] :
      ( ~ r2_hidden(A_3,C_42)
      | ~ r1_xboole_0(k1_tarski(A_3),C_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_137])).

tff(c_201,plain,(
    ! [A_61,B_62] :
      ( ~ r2_hidden(A_61,k1_relat_1(B_62))
      | k9_relat_1(B_62,k1_tarski(A_61)) != k1_xboole_0
      | ~ v1_relat_1(B_62) ) ),
    inference(resolution,[status(thm)],[c_181,c_144])).

tff(c_207,plain,
    ( k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_128,c_201])).

tff(c_211,plain,(
    k9_relat_1('#skF_2',k1_tarski('#skF_1')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_207])).

tff(c_214,plain,
    ( k11_relat_1('#skF_2','#skF_1') != k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_211])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_131,c_214])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:00:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k2_tarski > k11_relat_1 > #nlpp > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.87/1.19  
% 1.87/1.19  %Foreground sorts:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Background operators:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Foreground operators:
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.19  tff(k11_relat_1, type, k11_relat_1: ($i * $i) > $i).
% 1.87/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.19  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.87/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.19  
% 1.92/1.21  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k1_relat_1(B)) <=> ~(k11_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t205_relat_1)).
% 1.92/1.21  tff(f_36, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.92/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.92/1.21  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.92/1.21  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (k11_relat_1(A, B) = k9_relat_1(A, k1_tarski(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d16_relat_1)).
% 1.92/1.21  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.21  tff(f_41, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.92/1.21  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.21  tff(c_24, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2')) | k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.21  tff(c_43, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_24])).
% 1.92/1.21  tff(c_35, plain, (![A_17, B_18]: (r1_xboole_0(k1_tarski(A_17), B_18) | r2_hidden(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.92/1.21  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.21  tff(c_38, plain, (![B_18, A_17]: (r1_xboole_0(B_18, k1_tarski(A_17)) | r2_hidden(A_17, B_18))), inference(resolution, [status(thm)], [c_35, c_2])).
% 1.92/1.21  tff(c_75, plain, (![B_33, A_34]: (k9_relat_1(B_33, A_34)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_33), A_34) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.21  tff(c_108, plain, (![B_39, A_40]: (k9_relat_1(B_39, k1_tarski(A_40))=k1_xboole_0 | ~v1_relat_1(B_39) | r2_hidden(A_40, k1_relat_1(B_39)))), inference(resolution, [status(thm)], [c_38, c_75])).
% 1.92/1.21  tff(c_18, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.21  tff(c_44, plain, (~r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_43, c_18])).
% 1.92/1.21  tff(c_111, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_108, c_44])).
% 1.92/1.21  tff(c_114, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_111])).
% 1.92/1.21  tff(c_10, plain, (![A_9, B_11]: (k9_relat_1(A_9, k1_tarski(B_11))=k11_relat_1(A_9, B_11) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.92/1.21  tff(c_118, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 1.92/1.21  tff(c_125, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_118])).
% 1.92/1.21  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_125])).
% 1.92/1.21  tff(c_128, plain, (r2_hidden('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_24])).
% 1.92/1.21  tff(c_131, plain, (k11_relat_1('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_128, c_18])).
% 1.92/1.21  tff(c_173, plain, (![B_55, A_56]: (r1_xboole_0(k1_relat_1(B_55), A_56) | k9_relat_1(B_55, A_56)!=k1_xboole_0 | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.21  tff(c_181, plain, (![A_57, B_58]: (r1_xboole_0(A_57, k1_relat_1(B_58)) | k9_relat_1(B_58, A_57)!=k1_xboole_0 | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_173, c_2])).
% 1.92/1.21  tff(c_4, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.21  tff(c_137, plain, (![A_41, C_42, B_43]: (~r2_hidden(A_41, C_42) | ~r1_xboole_0(k2_tarski(A_41, B_43), C_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.21  tff(c_144, plain, (![A_3, C_42]: (~r2_hidden(A_3, C_42) | ~r1_xboole_0(k1_tarski(A_3), C_42))), inference(superposition, [status(thm), theory('equality')], [c_4, c_137])).
% 1.92/1.21  tff(c_201, plain, (![A_61, B_62]: (~r2_hidden(A_61, k1_relat_1(B_62)) | k9_relat_1(B_62, k1_tarski(A_61))!=k1_xboole_0 | ~v1_relat_1(B_62))), inference(resolution, [status(thm)], [c_181, c_144])).
% 1.92/1.21  tff(c_207, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_128, c_201])).
% 1.92/1.21  tff(c_211, plain, (k9_relat_1('#skF_2', k1_tarski('#skF_1'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_207])).
% 1.92/1.21  tff(c_214, plain, (k11_relat_1('#skF_2', '#skF_1')!=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_211])).
% 1.92/1.21  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_131, c_214])).
% 1.92/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  Inference rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Ref     : 0
% 1.92/1.21  #Sup     : 40
% 1.92/1.21  #Fact    : 0
% 1.92/1.21  #Define  : 0
% 1.92/1.21  #Split   : 1
% 1.92/1.21  #Chain   : 0
% 1.92/1.21  #Close   : 0
% 1.92/1.21  
% 1.92/1.21  Ordering : KBO
% 1.92/1.21  
% 1.92/1.21  Simplification rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Subsume      : 3
% 1.92/1.21  #Demod        : 7
% 1.92/1.21  #Tautology    : 17
% 1.92/1.21  #SimpNegUnit  : 2
% 1.92/1.21  #BackRed      : 0
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.21  Preprocessing        : 0.28
% 1.92/1.21  Parsing              : 0.15
% 1.92/1.21  CNF conversion       : 0.02
% 1.92/1.21  Main loop            : 0.17
% 1.92/1.21  Inferencing          : 0.07
% 1.92/1.21  Reduction            : 0.04
% 1.92/1.21  Demodulation         : 0.02
% 1.92/1.21  BG Simplification    : 0.01
% 1.92/1.21  Subsumption          : 0.02
% 1.92/1.21  Abstraction          : 0.01
% 1.92/1.21  MUC search           : 0.00
% 1.92/1.21  Cooper               : 0.00
% 1.92/1.21  Total                : 0.48
% 1.92/1.21  Index Insertion      : 0.00
% 1.92/1.21  Index Deletion       : 0.00
% 1.92/1.21  Index Matching       : 0.00
% 1.92/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
