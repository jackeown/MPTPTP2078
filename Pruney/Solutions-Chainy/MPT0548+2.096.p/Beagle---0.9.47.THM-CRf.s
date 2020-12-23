%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:47 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   48 (  56 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  63 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_52,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_12,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,(
    ! [A_21,B_22] : v1_relat_1(k2_zfmisc_1(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_63,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_61])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_74,plain,(
    ! [A_24,B_25] : ~ r2_hidden(A_24,k2_zfmisc_1(A_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    ! [A_9] : ~ r2_hidden(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_74])).

tff(c_94,plain,(
    ! [A_32,B_33] : k4_xboole_0(A_32,k4_xboole_0(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_104,plain,(
    ! [B_33] : k3_xboole_0(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_164,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43,B_44),k3_xboole_0(A_43,B_44))
      | r1_xboole_0(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_170,plain,(
    ! [B_33] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_33),k1_xboole_0)
      | r1_xboole_0(k1_xboole_0,B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_164])).

tff(c_172,plain,(
    ! [B_33] : r1_xboole_0(k1_xboole_0,B_33) ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_170])).

tff(c_24,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_149,plain,(
    ! [B_40,A_41] :
      ( k7_relat_1(B_40,A_41) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_40),A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_155,plain,(
    ! [A_41] :
      ( k7_relat_1(k1_xboole_0,A_41) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_41)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_149])).

tff(c_158,plain,(
    ! [A_41] :
      ( k7_relat_1(k1_xboole_0,A_41) = k1_xboole_0
      | ~ r1_xboole_0(k1_xboole_0,A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_155])).

tff(c_203,plain,(
    ! [A_48] : k7_relat_1(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_158])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k2_relat_1(k7_relat_1(B_16,A_15)) = k9_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_208,plain,(
    ! [A_48] :
      ( k9_relat_1(k1_xboole_0,A_48) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_20])).

tff(c_213,plain,(
    ! [A_48] : k9_relat_1(k1_xboole_0,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_22,c_208])).

tff(c_30,plain,(
    k9_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:34:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.16  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.86/1.16  
% 1.86/1.16  %Foreground sorts:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Background operators:
% 1.86/1.16  
% 1.86/1.16  
% 1.86/1.16  %Foreground operators:
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.16  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.86/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.86/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.16  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.16  
% 1.86/1.17  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.86/1.17  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.86/1.17  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.86/1.17  tff(f_52, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.86/1.17  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.86/1.17  tff(f_43, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.86/1.17  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.86/1.17  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.86/1.17  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.86/1.17  tff(f_70, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.86/1.17  tff(c_12, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.86/1.17  tff(c_61, plain, (![A_21, B_22]: (v1_relat_1(k2_zfmisc_1(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.86/1.17  tff(c_63, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_61])).
% 1.86/1.17  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.86/1.17  tff(c_74, plain, (![A_24, B_25]: (~r2_hidden(A_24, k2_zfmisc_1(A_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.17  tff(c_77, plain, (![A_9]: (~r2_hidden(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_74])).
% 1.86/1.17  tff(c_94, plain, (![A_32, B_33]: (k4_xboole_0(A_32, k4_xboole_0(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.17  tff(c_8, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.17  tff(c_104, plain, (![B_33]: (k3_xboole_0(k1_xboole_0, B_33)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_94, c_8])).
% 1.86/1.17  tff(c_164, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43, B_44), k3_xboole_0(A_43, B_44)) | r1_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.17  tff(c_170, plain, (![B_33]: (r2_hidden('#skF_1'(k1_xboole_0, B_33), k1_xboole_0) | r1_xboole_0(k1_xboole_0, B_33))), inference(superposition, [status(thm), theory('equality')], [c_104, c_164])).
% 1.86/1.17  tff(c_172, plain, (![B_33]: (r1_xboole_0(k1_xboole_0, B_33))), inference(negUnitSimplification, [status(thm)], [c_77, c_170])).
% 1.86/1.17  tff(c_24, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.86/1.17  tff(c_149, plain, (![B_40, A_41]: (k7_relat_1(B_40, A_41)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_40), A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.86/1.17  tff(c_155, plain, (![A_41]: (k7_relat_1(k1_xboole_0, A_41)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_41) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_149])).
% 1.86/1.17  tff(c_158, plain, (![A_41]: (k7_relat_1(k1_xboole_0, A_41)=k1_xboole_0 | ~r1_xboole_0(k1_xboole_0, A_41))), inference(demodulation, [status(thm), theory('equality')], [c_63, c_155])).
% 1.86/1.17  tff(c_203, plain, (![A_48]: (k7_relat_1(k1_xboole_0, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_172, c_158])).
% 1.86/1.17  tff(c_20, plain, (![B_16, A_15]: (k2_relat_1(k7_relat_1(B_16, A_15))=k9_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.86/1.17  tff(c_208, plain, (![A_48]: (k9_relat_1(k1_xboole_0, A_48)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_203, c_20])).
% 1.86/1.17  tff(c_213, plain, (![A_48]: (k9_relat_1(k1_xboole_0, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_22, c_208])).
% 1.86/1.17  tff(c_30, plain, (k9_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.86/1.17  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_213, c_30])).
% 1.86/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.17  
% 1.86/1.17  Inference rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Ref     : 0
% 1.86/1.17  #Sup     : 45
% 1.86/1.17  #Fact    : 0
% 1.86/1.17  #Define  : 0
% 1.86/1.17  #Split   : 0
% 1.86/1.17  #Chain   : 0
% 1.86/1.17  #Close   : 0
% 1.86/1.17  
% 1.86/1.17  Ordering : KBO
% 1.86/1.17  
% 1.86/1.17  Simplification rules
% 1.86/1.17  ----------------------
% 1.86/1.17  #Subsume      : 2
% 1.86/1.17  #Demod        : 18
% 1.86/1.17  #Tautology    : 34
% 1.86/1.17  #SimpNegUnit  : 1
% 1.86/1.17  #BackRed      : 2
% 1.86/1.17  
% 1.86/1.17  #Partial instantiations: 0
% 1.95/1.17  #Strategies tried      : 1
% 1.95/1.17  
% 1.95/1.17  Timing (in seconds)
% 1.95/1.17  ----------------------
% 1.95/1.18  Preprocessing        : 0.28
% 1.95/1.18  Parsing              : 0.16
% 1.95/1.18  CNF conversion       : 0.02
% 1.95/1.18  Main loop            : 0.15
% 1.95/1.18  Inferencing          : 0.06
% 1.95/1.18  Reduction            : 0.05
% 1.95/1.18  Demodulation         : 0.03
% 1.95/1.18  BG Simplification    : 0.01
% 1.95/1.18  Subsumption          : 0.02
% 1.95/1.18  Abstraction          : 0.01
% 1.95/1.18  MUC search           : 0.00
% 1.95/1.18  Cooper               : 0.00
% 1.95/1.18  Total                : 0.46
% 1.95/1.18  Index Insertion      : 0.00
% 1.95/1.18  Index Deletion       : 0.00
% 1.95/1.18  Index Matching       : 0.00
% 1.95/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
