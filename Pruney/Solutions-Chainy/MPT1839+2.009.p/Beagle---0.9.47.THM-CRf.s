%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:22 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   51 (  67 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   56 (  86 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_xboole_1)).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_165,plain,(
    ! [A_36,B_37] : k2_xboole_0(k3_xboole_0(A_36,B_37),A_36) = A_36 ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_193,plain,(
    ! [A_1,B_37] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_37)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_28,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_26,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_298,plain,(
    ! [B_45,A_46] :
      ( B_45 = A_46
      | ~ r1_tarski(A_46,B_45)
      | ~ v1_zfmisc_1(B_45)
      | v1_xboole_0(B_45)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_695,plain,(
    ! [A_67,B_68] :
      ( k3_xboole_0(A_67,B_68) = A_67
      | ~ v1_zfmisc_1(A_67)
      | v1_xboole_0(A_67)
      | v1_xboole_0(k3_xboole_0(A_67,B_68)) ) ),
    inference(resolution,[status(thm)],[c_6,c_298])).

tff(c_24,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_698,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_695,c_24])).

tff(c_707,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_698])).

tff(c_708,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_707])).

tff(c_10,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_327,plain,(
    ! [A_48,B_49,C_50] : r1_tarski(k2_xboole_0(k3_xboole_0(A_48,B_49),k3_xboole_0(A_48,C_50)),k2_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_372,plain,(
    ! [A_7,C_50] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(A_7,C_50)),k2_xboole_0(k1_xboole_0,C_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_327])).

tff(c_410,plain,(
    ! [A_52,C_53] : r1_tarski(k3_xboole_0(A_52,C_53),C_53) ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_83,c_372])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_431,plain,(
    ! [A_54,C_55] : k2_xboole_0(k3_xboole_0(A_54,C_55),C_55) = C_55 ),
    inference(resolution,[status(thm)],[c_410,c_4])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : r1_tarski(k2_xboole_0(k3_xboole_0(A_9,B_10),k3_xboole_0(A_9,C_11)),k2_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_441,plain,(
    ! [A_9,A_54,C_55] : r1_tarski(k2_xboole_0(k3_xboole_0(A_9,k3_xboole_0(A_54,C_55)),k3_xboole_0(A_9,C_55)),C_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_12])).

tff(c_483,plain,(
    ! [A_9,C_55,A_54] : r1_tarski(k2_xboole_0(k3_xboole_0(A_9,C_55),k3_xboole_0(A_9,k3_xboole_0(A_54,C_55))),C_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_718,plain,(
    ! [A_54] : r1_tarski(k2_xboole_0('#skF_1',k3_xboole_0('#skF_1',k3_xboole_0(A_54,'#skF_2'))),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_708,c_483])).

tff(c_766,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_718])).

tff(c_768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_766])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:40:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.46  
% 2.69/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.46  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.69/1.46  
% 2.69/1.46  %Foreground sorts:
% 2.69/1.46  
% 2.69/1.46  
% 2.69/1.46  %Background operators:
% 2.69/1.46  
% 2.69/1.46  
% 2.69/1.46  %Foreground operators:
% 2.69/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.69/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.46  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.69/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.69/1.46  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.69/1.46  
% 2.74/1.47  tff(f_70, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.74/1.47  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.74/1.47  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.74/1.47  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.74/1.47  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.74/1.47  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.74/1.47  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.74/1.47  tff(f_39, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_xboole_1)).
% 2.74/1.47  tff(c_22, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.47  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.74/1.47  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.74/1.47  tff(c_75, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.47  tff(c_165, plain, (![A_36, B_37]: (k2_xboole_0(k3_xboole_0(A_36, B_37), A_36)=A_36)), inference(resolution, [status(thm)], [c_6, c_75])).
% 2.74/1.47  tff(c_193, plain, (![A_1, B_37]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_37))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_165])).
% 2.74/1.47  tff(c_28, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.47  tff(c_26, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.47  tff(c_298, plain, (![B_45, A_46]: (B_45=A_46 | ~r1_tarski(A_46, B_45) | ~v1_zfmisc_1(B_45) | v1_xboole_0(B_45) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.47  tff(c_695, plain, (![A_67, B_68]: (k3_xboole_0(A_67, B_68)=A_67 | ~v1_zfmisc_1(A_67) | v1_xboole_0(A_67) | v1_xboole_0(k3_xboole_0(A_67, B_68)))), inference(resolution, [status(thm)], [c_6, c_298])).
% 2.74/1.47  tff(c_24, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.74/1.47  tff(c_698, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_695, c_24])).
% 2.74/1.47  tff(c_707, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_698])).
% 2.74/1.47  tff(c_708, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_28, c_707])).
% 2.74/1.47  tff(c_10, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.74/1.47  tff(c_83, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.74/1.47  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.74/1.47  tff(c_327, plain, (![A_48, B_49, C_50]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_48, B_49), k3_xboole_0(A_48, C_50)), k2_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.47  tff(c_372, plain, (![A_7, C_50]: (r1_tarski(k2_xboole_0(k1_xboole_0, k3_xboole_0(A_7, C_50)), k2_xboole_0(k1_xboole_0, C_50)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_327])).
% 2.74/1.47  tff(c_410, plain, (![A_52, C_53]: (r1_tarski(k3_xboole_0(A_52, C_53), C_53))), inference(demodulation, [status(thm), theory('equality')], [c_83, c_83, c_372])).
% 2.74/1.47  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.74/1.47  tff(c_431, plain, (![A_54, C_55]: (k2_xboole_0(k3_xboole_0(A_54, C_55), C_55)=C_55)), inference(resolution, [status(thm)], [c_410, c_4])).
% 2.74/1.47  tff(c_12, plain, (![A_9, B_10, C_11]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_9, B_10), k3_xboole_0(A_9, C_11)), k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.74/1.47  tff(c_441, plain, (![A_9, A_54, C_55]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_9, k3_xboole_0(A_54, C_55)), k3_xboole_0(A_9, C_55)), C_55))), inference(superposition, [status(thm), theory('equality')], [c_431, c_12])).
% 2.74/1.47  tff(c_483, plain, (![A_9, C_55, A_54]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_9, C_55), k3_xboole_0(A_9, k3_xboole_0(A_54, C_55))), C_55))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_441])).
% 2.74/1.47  tff(c_718, plain, (![A_54]: (r1_tarski(k2_xboole_0('#skF_1', k3_xboole_0('#skF_1', k3_xboole_0(A_54, '#skF_2'))), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_708, c_483])).
% 2.74/1.47  tff(c_766, plain, (r1_tarski('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_718])).
% 2.74/1.47  tff(c_768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_766])).
% 2.74/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.74/1.47  
% 2.74/1.47  Inference rules
% 2.74/1.47  ----------------------
% 2.74/1.47  #Ref     : 0
% 2.74/1.47  #Sup     : 175
% 2.74/1.47  #Fact    : 0
% 2.74/1.47  #Define  : 0
% 2.74/1.47  #Split   : 1
% 2.74/1.47  #Chain   : 0
% 2.74/1.47  #Close   : 0
% 2.74/1.47  
% 2.74/1.47  Ordering : KBO
% 2.74/1.47  
% 2.74/1.47  Simplification rules
% 2.74/1.47  ----------------------
% 2.74/1.47  #Subsume      : 1
% 2.74/1.47  #Demod        : 164
% 2.74/1.47  #Tautology    : 130
% 2.74/1.47  #SimpNegUnit  : 3
% 2.74/1.47  #BackRed      : 3
% 2.74/1.47  
% 2.74/1.47  #Partial instantiations: 0
% 2.74/1.47  #Strategies tried      : 1
% 2.74/1.47  
% 2.74/1.47  Timing (in seconds)
% 2.74/1.47  ----------------------
% 2.74/1.47  Preprocessing        : 0.33
% 2.74/1.47  Parsing              : 0.18
% 2.74/1.47  CNF conversion       : 0.02
% 2.74/1.47  Main loop            : 0.29
% 2.74/1.47  Inferencing          : 0.11
% 2.74/1.47  Reduction            : 0.11
% 2.74/1.47  Demodulation         : 0.09
% 2.74/1.47  BG Simplification    : 0.01
% 2.74/1.48  Subsumption          : 0.04
% 2.74/1.48  Abstraction          : 0.02
% 2.74/1.48  MUC search           : 0.00
% 2.74/1.48  Cooper               : 0.00
% 2.74/1.48  Total                : 0.65
% 2.74/1.48  Index Insertion      : 0.00
% 2.74/1.48  Index Deletion       : 0.00
% 2.74/1.48  Index Matching       : 0.00
% 2.74/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
