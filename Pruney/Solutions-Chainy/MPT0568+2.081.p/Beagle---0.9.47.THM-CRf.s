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
% DateTime   : Thu Dec  3 10:01:31 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   50 (  50 expanded)
%              Number of leaves         :   29 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   56 (  56 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_50,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_48,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_80,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_83,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_110,plain,(
    ! [A_38,B_39,C_40] :
      ( ~ r1_xboole_0(A_38,B_39)
      | ~ r2_hidden(C_40,k3_xboole_0(A_38,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_117,plain,(
    ! [A_10,C_40] :
      ( ~ r1_xboole_0(A_10,k1_xboole_0)
      | ~ r2_hidden(C_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_110])).

tff(c_120,plain,(
    ! [C_40] : ~ r2_hidden(C_40,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_117])).

tff(c_56,plain,(
    ! [A_28] : k2_zfmisc_1(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_60,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_24])).

tff(c_34,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_209,plain,(
    ! [A_62,B_63,C_64] :
      ( r2_hidden('#skF_3'(A_62,B_63,C_64),k2_relat_1(C_64))
      | ~ r2_hidden(A_62,k10_relat_1(C_64,B_63))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_215,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_62,k10_relat_1(k1_xboole_0,B_63))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_209])).

tff(c_218,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_3'(A_62,B_63,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_62,k10_relat_1(k1_xboole_0,B_63)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_215])).

tff(c_220,plain,(
    ! [A_65,B_66] : ~ r2_hidden(A_65,k10_relat_1(k1_xboole_0,B_66)) ),
    inference(negUnitSimplification,[status(thm)],[c_120,c_218])).

tff(c_231,plain,(
    ! [B_67] : v1_xboole_0(k10_relat_1(k1_xboole_0,B_67)) ),
    inference(resolution,[status(thm)],[c_4,c_220])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [B_33,A_34] :
      ( ~ v1_xboole_0(B_33)
      | B_33 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_92,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(resolution,[status(thm)],[c_6,c_89])).

tff(c_240,plain,(
    ! [B_67] : k10_relat_1(k1_xboole_0,B_67) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_231,c_92])).

tff(c_38,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:32:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  
% 2.07/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.24  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_2
% 2.07/1.24  
% 2.07/1.24  %Foreground sorts:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Background operators:
% 2.07/1.24  
% 2.07/1.24  
% 2.07/1.24  %Foreground operators:
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.24  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.07/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.24  
% 2.07/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.07/1.25  tff(f_50, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.07/1.25  tff(f_48, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.07/1.25  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.07/1.25  tff(f_64, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.07/1.25  tff(f_66, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.07/1.25  tff(f_80, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 2.07/1.25  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.07/1.25  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.07/1.25  tff(f_58, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.07/1.25  tff(f_83, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.07/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.25  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.07/1.25  tff(c_12, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.07/1.25  tff(c_110, plain, (![A_38, B_39, C_40]: (~r1_xboole_0(A_38, B_39) | ~r2_hidden(C_40, k3_xboole_0(A_38, B_39)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.25  tff(c_117, plain, (![A_10, C_40]: (~r1_xboole_0(A_10, k1_xboole_0) | ~r2_hidden(C_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_110])).
% 2.07/1.25  tff(c_120, plain, (![C_40]: (~r2_hidden(C_40, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_117])).
% 2.07/1.25  tff(c_56, plain, (![A_28]: (k2_zfmisc_1(A_28, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.07/1.25  tff(c_24, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.07/1.25  tff(c_60, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_56, c_24])).
% 2.07/1.25  tff(c_34, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.07/1.25  tff(c_209, plain, (![A_62, B_63, C_64]: (r2_hidden('#skF_3'(A_62, B_63, C_64), k2_relat_1(C_64)) | ~r2_hidden(A_62, k10_relat_1(C_64, B_63)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.07/1.25  tff(c_215, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_62, k10_relat_1(k1_xboole_0, B_63)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_34, c_209])).
% 2.07/1.25  tff(c_218, plain, (![A_62, B_63]: (r2_hidden('#skF_3'(A_62, B_63, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_62, k10_relat_1(k1_xboole_0, B_63)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_215])).
% 2.07/1.25  tff(c_220, plain, (![A_65, B_66]: (~r2_hidden(A_65, k10_relat_1(k1_xboole_0, B_66)))), inference(negUnitSimplification, [status(thm)], [c_120, c_218])).
% 2.07/1.25  tff(c_231, plain, (![B_67]: (v1_xboole_0(k10_relat_1(k1_xboole_0, B_67)))), inference(resolution, [status(thm)], [c_4, c_220])).
% 2.07/1.25  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.25  tff(c_89, plain, (![B_33, A_34]: (~v1_xboole_0(B_33) | B_33=A_34 | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.25  tff(c_92, plain, (![A_34]: (k1_xboole_0=A_34 | ~v1_xboole_0(A_34))), inference(resolution, [status(thm)], [c_6, c_89])).
% 2.07/1.25  tff(c_240, plain, (![B_67]: (k10_relat_1(k1_xboole_0, B_67)=k1_xboole_0)), inference(resolution, [status(thm)], [c_231, c_92])).
% 2.07/1.25  tff(c_38, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.07/1.25  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_240, c_38])).
% 2.07/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  Inference rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Ref     : 0
% 2.07/1.25  #Sup     : 46
% 2.07/1.25  #Fact    : 0
% 2.07/1.25  #Define  : 0
% 2.07/1.25  #Split   : 0
% 2.07/1.25  #Chain   : 0
% 2.07/1.25  #Close   : 0
% 2.07/1.25  
% 2.07/1.25  Ordering : KBO
% 2.07/1.25  
% 2.07/1.25  Simplification rules
% 2.07/1.25  ----------------------
% 2.07/1.25  #Subsume      : 3
% 2.07/1.25  #Demod        : 15
% 2.07/1.25  #Tautology    : 25
% 2.07/1.25  #SimpNegUnit  : 2
% 2.07/1.25  #BackRed      : 3
% 2.07/1.25  
% 2.07/1.25  #Partial instantiations: 0
% 2.07/1.25  #Strategies tried      : 1
% 2.07/1.25  
% 2.07/1.25  Timing (in seconds)
% 2.07/1.25  ----------------------
% 2.07/1.25  Preprocessing        : 0.29
% 2.07/1.25  Parsing              : 0.16
% 2.07/1.25  CNF conversion       : 0.02
% 2.07/1.25  Main loop            : 0.18
% 2.07/1.25  Inferencing          : 0.07
% 2.07/1.25  Reduction            : 0.05
% 2.07/1.25  Demodulation         : 0.03
% 2.07/1.26  BG Simplification    : 0.01
% 2.07/1.26  Subsumption          : 0.03
% 2.07/1.26  Abstraction          : 0.01
% 2.07/1.26  MUC search           : 0.00
% 2.07/1.26  Cooper               : 0.00
% 2.07/1.26  Total                : 0.50
% 2.07/1.26  Index Insertion      : 0.00
% 2.07/1.26  Index Deletion       : 0.00
% 2.07/1.26  Index Matching       : 0.00
% 2.07/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
