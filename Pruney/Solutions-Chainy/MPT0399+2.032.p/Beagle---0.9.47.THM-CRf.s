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
% DateTime   : Thu Dec  3 09:57:36 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 130 expanded)
%              Number of leaves         :   27 (  55 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 ( 221 expanded)
%              Number of equality atoms :   33 (  85 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( A != k1_tarski(B)
        & A != k1_xboole_0
        & ! [C] :
            ~ ( r2_hidden(C,A)
              & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_38,axiom,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    r1_setfam_1('#skF_4',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_30,plain,(
    ! [A_14,B_15] :
      ( r2_hidden('#skF_2'(A_14,B_15),A_14)
      | r1_setfam_1(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_748,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden('#skF_3'(A_133,B_134,C_135),B_134)
      | ~ r2_hidden(C_135,A_133)
      | ~ r1_setfam_1(A_133,B_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_582,plain,(
    ! [B_106,C_107,A_108] :
      ( ~ r2_hidden(B_106,C_107)
      | k4_xboole_0(k2_tarski(A_108,B_106),C_107) != k2_tarski(A_108,B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_591,plain,(
    ! [B_106] : ~ r2_hidden(B_106,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_582])).

tff(c_754,plain,(
    ! [C_136,A_137] :
      ( ~ r2_hidden(C_136,A_137)
      | ~ r1_setfam_1(A_137,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_748,c_591])).

tff(c_767,plain,(
    ! [A_138,B_139] :
      ( ~ r1_setfam_1(A_138,k1_xboole_0)
      | r1_setfam_1(A_138,B_139) ) ),
    inference(resolution,[status(thm)],[c_30,c_754])).

tff(c_775,plain,(
    ! [B_139] : r1_setfam_1('#skF_4',B_139) ),
    inference(resolution,[status(thm)],[c_36,c_767])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_1'(A_8,B_9),A_8)
      | k1_xboole_0 = A_8
      | k1_tarski(B_9) = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_801,plain,(
    ! [A_143,B_144] :
      ( ~ r1_setfam_1(A_143,k1_xboole_0)
      | k1_xboole_0 = A_143
      | k1_tarski(B_144) = A_143 ) ),
    inference(resolution,[status(thm)],[c_16,c_754])).

tff(c_804,plain,(
    ! [B_144] :
      ( k1_xboole_0 = '#skF_4'
      | k1_tarski(B_144) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_775,c_801])).

tff(c_810,plain,(
    ! [B_144] : k1_tarski(B_144) = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_804])).

tff(c_8,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_34,B_35] : k2_xboole_0(k1_tarski(A_34),k1_tarski(B_35)) = k2_tarski(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [A_5] : k3_tarski(k1_tarski(A_5)) = k2_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_60])).

tff(c_96,plain,(
    ! [B_35] : k3_tarski(k1_tarski(k1_tarski(B_35))) = k2_tarski(B_35,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_69])).

tff(c_105,plain,(
    ! [B_35] : k3_tarski(k1_tarski(k1_tarski(B_35))) = k1_tarski(B_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_96])).

tff(c_828,plain,(
    k3_tarski('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_810,c_810,c_810,c_105])).

tff(c_12,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_119,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k3_tarski(A_39),k3_tarski(B_40))
      | ~ r1_setfam_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_404,plain,(
    ! [A_82] :
      ( r1_tarski(k3_tarski(A_82),k1_xboole_0)
      | ~ r1_setfam_1(A_82,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_119])).

tff(c_4,plain,(
    ! [A_2] :
      ( k1_xboole_0 = A_2
      | ~ r1_tarski(A_2,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_423,plain,(
    ! [A_83] :
      ( k3_tarski(A_83) = k1_xboole_0
      | ~ r1_setfam_1(A_83,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_404,c_4])).

tff(c_432,plain,(
    k3_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_423])).

tff(c_854,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_432])).

tff(c_856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_854])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:25:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  
% 2.67/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.40  %$ r2_hidden > r1_tarski > r1_setfam_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 2.67/1.40  
% 2.67/1.40  %Foreground sorts:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Background operators:
% 2.67/1.40  
% 2.67/1.40  
% 2.67/1.40  %Foreground operators:
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.40  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.67/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.67/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.67/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.67/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.67/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.67/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.67/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.67/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.67/1.40  
% 2.67/1.42  tff(f_81, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.67/1.42  tff(f_72, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.67/1.42  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.67/1.42  tff(f_60, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.67/1.42  tff(f_52, axiom, (![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.67/1.42  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.67/1.42  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 2.67/1.42  tff(f_37, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.67/1.42  tff(f_38, axiom, (k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 2.67/1.42  tff(f_76, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.67/1.42  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.67/1.42  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.42  tff(c_36, plain, (r1_setfam_1('#skF_4', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.67/1.42  tff(c_30, plain, (![A_14, B_15]: (r2_hidden('#skF_2'(A_14, B_15), A_14) | r1_setfam_1(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.42  tff(c_748, plain, (![A_133, B_134, C_135]: (r2_hidden('#skF_3'(A_133, B_134, C_135), B_134) | ~r2_hidden(C_135, A_133) | ~r1_setfam_1(A_133, B_134))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.67/1.42  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.42  tff(c_582, plain, (![B_106, C_107, A_108]: (~r2_hidden(B_106, C_107) | k4_xboole_0(k2_tarski(A_108, B_106), C_107)!=k2_tarski(A_108, B_106))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.42  tff(c_591, plain, (![B_106]: (~r2_hidden(B_106, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_582])).
% 2.67/1.42  tff(c_754, plain, (![C_136, A_137]: (~r2_hidden(C_136, A_137) | ~r1_setfam_1(A_137, k1_xboole_0))), inference(resolution, [status(thm)], [c_748, c_591])).
% 2.67/1.42  tff(c_767, plain, (![A_138, B_139]: (~r1_setfam_1(A_138, k1_xboole_0) | r1_setfam_1(A_138, B_139))), inference(resolution, [status(thm)], [c_30, c_754])).
% 2.67/1.42  tff(c_775, plain, (![B_139]: (r1_setfam_1('#skF_4', B_139))), inference(resolution, [status(thm)], [c_36, c_767])).
% 2.67/1.42  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_1'(A_8, B_9), A_8) | k1_xboole_0=A_8 | k1_tarski(B_9)=A_8)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.67/1.42  tff(c_801, plain, (![A_143, B_144]: (~r1_setfam_1(A_143, k1_xboole_0) | k1_xboole_0=A_143 | k1_tarski(B_144)=A_143)), inference(resolution, [status(thm)], [c_16, c_754])).
% 2.67/1.42  tff(c_804, plain, (![B_144]: (k1_xboole_0='#skF_4' | k1_tarski(B_144)='#skF_4')), inference(resolution, [status(thm)], [c_775, c_801])).
% 2.67/1.42  tff(c_810, plain, (![B_144]: (k1_tarski(B_144)='#skF_4')), inference(negUnitSimplification, [status(thm)], [c_34, c_804])).
% 2.67/1.42  tff(c_8, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.67/1.42  tff(c_89, plain, (![A_34, B_35]: (k2_xboole_0(k1_tarski(A_34), k1_tarski(B_35))=k2_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.42  tff(c_60, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.42  tff(c_69, plain, (![A_5]: (k3_tarski(k1_tarski(A_5))=k2_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_8, c_60])).
% 2.67/1.42  tff(c_96, plain, (![B_35]: (k3_tarski(k1_tarski(k1_tarski(B_35)))=k2_tarski(B_35, B_35))), inference(superposition, [status(thm), theory('equality')], [c_89, c_69])).
% 2.67/1.42  tff(c_105, plain, (![B_35]: (k3_tarski(k1_tarski(k1_tarski(B_35)))=k1_tarski(B_35))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_96])).
% 2.67/1.42  tff(c_828, plain, (k3_tarski('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_810, c_810, c_810, c_105])).
% 2.67/1.42  tff(c_12, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.67/1.42  tff(c_119, plain, (![A_39, B_40]: (r1_tarski(k3_tarski(A_39), k3_tarski(B_40)) | ~r1_setfam_1(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.67/1.42  tff(c_404, plain, (![A_82]: (r1_tarski(k3_tarski(A_82), k1_xboole_0) | ~r1_setfam_1(A_82, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_119])).
% 2.67/1.42  tff(c_4, plain, (![A_2]: (k1_xboole_0=A_2 | ~r1_tarski(A_2, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.42  tff(c_423, plain, (![A_83]: (k3_tarski(A_83)=k1_xboole_0 | ~r1_setfam_1(A_83, k1_xboole_0))), inference(resolution, [status(thm)], [c_404, c_4])).
% 2.67/1.42  tff(c_432, plain, (k3_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_423])).
% 2.67/1.42  tff(c_854, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_828, c_432])).
% 2.67/1.42  tff(c_856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_854])).
% 2.67/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.42  
% 2.67/1.42  Inference rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Ref     : 0
% 2.67/1.42  #Sup     : 181
% 2.67/1.42  #Fact    : 0
% 2.67/1.42  #Define  : 0
% 2.67/1.42  #Split   : 1
% 2.67/1.42  #Chain   : 0
% 2.67/1.42  #Close   : 0
% 2.67/1.42  
% 2.67/1.42  Ordering : KBO
% 2.67/1.42  
% 2.67/1.42  Simplification rules
% 2.67/1.42  ----------------------
% 2.67/1.42  #Subsume      : 37
% 2.67/1.42  #Demod        : 118
% 2.67/1.42  #Tautology    : 67
% 2.67/1.42  #SimpNegUnit  : 2
% 2.67/1.42  #BackRed      : 28
% 2.67/1.42  
% 2.67/1.42  #Partial instantiations: 0
% 2.67/1.42  #Strategies tried      : 1
% 2.67/1.42  
% 2.67/1.42  Timing (in seconds)
% 2.67/1.42  ----------------------
% 2.67/1.42  Preprocessing        : 0.30
% 2.67/1.42  Parsing              : 0.16
% 2.67/1.42  CNF conversion       : 0.02
% 2.67/1.42  Main loop            : 0.36
% 2.67/1.42  Inferencing          : 0.14
% 2.67/1.42  Reduction            : 0.11
% 2.67/1.42  Demodulation         : 0.08
% 2.67/1.42  BG Simplification    : 0.02
% 2.67/1.42  Subsumption          : 0.07
% 2.67/1.42  Abstraction          : 0.01
% 2.67/1.42  MUC search           : 0.00
% 2.67/1.42  Cooper               : 0.00
% 2.67/1.42  Total                : 0.69
% 2.67/1.42  Index Insertion      : 0.00
% 2.67/1.42  Index Deletion       : 0.00
% 2.67/1.42  Index Matching       : 0.00
% 2.67/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
