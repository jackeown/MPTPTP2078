%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:27 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   48 (  53 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  74 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

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
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_61,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_61,c_24])).

tff(c_8,plain,(
    ! [A_5] : k3_xboole_0(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k4_xboole_0(A_41,B_42)) = k3_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_207,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k3_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_175])).

tff(c_217,plain,(
    ! [A_6] : k4_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_207])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_87,plain,(
    ! [A_3,B_4] : k4_xboole_0(k3_xboole_0(A_3,B_4),A_3) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_75])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_384,plain,(
    ! [B_53,A_54] :
      ( B_53 = A_54
      | ~ r1_tarski(A_54,B_53)
      | ~ v1_zfmisc_1(B_53)
      | v1_xboole_0(B_53)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_656,plain,(
    ! [B_63,A_64] :
      ( B_63 = A_64
      | ~ v1_zfmisc_1(B_63)
      | v1_xboole_0(B_63)
      | v1_xboole_0(A_64)
      | k4_xboole_0(A_64,B_63) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_384])).

tff(c_658,plain,(
    ! [A_64] :
      ( A_64 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_64)
      | k4_xboole_0(A_64,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_656])).

tff(c_662,plain,(
    ! [A_65] :
      ( A_65 = '#skF_1'
      | v1_xboole_0(A_65)
      | k4_xboole_0(A_65,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_658])).

tff(c_26,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_665,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_662,c_26])).

tff(c_671,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_665])).

tff(c_12,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_686,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_12])).

tff(c_697,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_686])).

tff(c_699,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_697])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:17:08 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.59  
% 2.34/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.60  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.34/1.60  
% 2.34/1.60  %Foreground sorts:
% 2.34/1.60  
% 2.34/1.60  
% 2.34/1.60  %Background operators:
% 2.34/1.60  
% 2.34/1.60  
% 2.34/1.60  %Foreground operators:
% 2.34/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.34/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.60  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.60  tff('#skF_1', type, '#skF_1': $i).
% 2.34/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.60  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.34/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.60  
% 2.34/1.61  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.34/1.61  tff(f_70, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 2.34/1.61  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.34/1.61  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.34/1.61  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.34/1.61  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.34/1.61  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.34/1.61  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.34/1.61  tff(c_61, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | k4_xboole_0(A_29, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.61  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.61  tff(c_65, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_61, c_24])).
% 2.34/1.61  tff(c_8, plain, (![A_5]: (k3_xboole_0(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.61  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.61  tff(c_175, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k4_xboole_0(A_41, B_42))=k3_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.34/1.61  tff(c_207, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k3_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_175])).
% 2.34/1.61  tff(c_217, plain, (![A_6]: (k4_xboole_0(A_6, A_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_207])).
% 2.34/1.61  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.61  tff(c_75, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.61  tff(c_87, plain, (![A_3, B_4]: (k4_xboole_0(k3_xboole_0(A_3, B_4), A_3)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_75])).
% 2.34/1.61  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.61  tff(c_28, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.61  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.34/1.61  tff(c_384, plain, (![B_53, A_54]: (B_53=A_54 | ~r1_tarski(A_54, B_53) | ~v1_zfmisc_1(B_53) | v1_xboole_0(B_53) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.34/1.61  tff(c_656, plain, (![B_63, A_64]: (B_63=A_64 | ~v1_zfmisc_1(B_63) | v1_xboole_0(B_63) | v1_xboole_0(A_64) | k4_xboole_0(A_64, B_63)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_384])).
% 2.34/1.61  tff(c_658, plain, (![A_64]: (A_64='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_64) | k4_xboole_0(A_64, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_656])).
% 2.34/1.61  tff(c_662, plain, (![A_65]: (A_65='#skF_1' | v1_xboole_0(A_65) | k4_xboole_0(A_65, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_30, c_658])).
% 2.34/1.61  tff(c_26, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.34/1.61  tff(c_665, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_662, c_26])).
% 2.34/1.61  tff(c_671, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_665])).
% 2.34/1.61  tff(c_12, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.61  tff(c_686, plain, (k4_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_671, c_12])).
% 2.34/1.61  tff(c_697, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_217, c_686])).
% 2.34/1.61  tff(c_699, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_697])).
% 2.34/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.61  
% 2.34/1.61  Inference rules
% 2.34/1.61  ----------------------
% 2.34/1.61  #Ref     : 0
% 2.34/1.61  #Sup     : 157
% 2.34/1.61  #Fact    : 0
% 2.34/1.61  #Define  : 0
% 2.34/1.61  #Split   : 1
% 2.34/1.61  #Chain   : 0
% 2.34/1.61  #Close   : 0
% 2.34/1.61  
% 2.34/1.61  Ordering : KBO
% 2.34/1.61  
% 2.34/1.61  Simplification rules
% 2.34/1.61  ----------------------
% 2.34/1.61  #Subsume      : 1
% 2.34/1.61  #Demod        : 133
% 2.34/1.61  #Tautology    : 132
% 2.34/1.61  #SimpNegUnit  : 2
% 2.34/1.61  #BackRed      : 1
% 2.34/1.61  
% 2.34/1.61  #Partial instantiations: 0
% 2.34/1.61  #Strategies tried      : 1
% 2.34/1.61  
% 2.34/1.61  Timing (in seconds)
% 2.34/1.61  ----------------------
% 2.34/1.61  Preprocessing        : 0.45
% 2.34/1.61  Parsing              : 0.24
% 2.34/1.61  CNF conversion       : 0.03
% 2.34/1.61  Main loop            : 0.26
% 2.34/1.61  Inferencing          : 0.10
% 2.34/1.61  Reduction            : 0.09
% 2.34/1.61  Demodulation         : 0.07
% 2.34/1.61  BG Simplification    : 0.02
% 2.34/1.61  Subsumption          : 0.03
% 2.34/1.61  Abstraction          : 0.02
% 2.34/1.61  MUC search           : 0.00
% 2.34/1.61  Cooper               : 0.00
% 2.34/1.61  Total                : 0.75
% 2.34/1.61  Index Insertion      : 0.00
% 2.34/1.61  Index Deletion       : 0.00
% 2.34/1.61  Index Matching       : 0.00
% 2.34/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
