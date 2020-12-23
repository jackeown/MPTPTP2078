%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:26 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  82 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(c_37,plain,(
    ! [A_19,B_20] :
      ( r1_tarski(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_41,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_16])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,(
    ! [A_16,B_17] : r1_tarski(k3_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_42,plain,(
    ! [A_21,B_22] :
      ( k4_xboole_0(A_21,B_22) = k1_xboole_0
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_53,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_35,c_42])).

tff(c_82,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_82])).

tff(c_94,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_91])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_54,plain,(
    ! [A_7,B_8] : k4_xboole_0(k3_xboole_0(A_7,B_8),A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_42])).

tff(c_22,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_20,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(A_32,B_31)
      | ~ v1_zfmisc_1(B_31)
      | v1_xboole_0(B_31)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_116,plain,(
    ! [B_33,A_34] :
      ( B_33 = A_34
      | ~ v1_zfmisc_1(B_33)
      | v1_xboole_0(B_33)
      | v1_xboole_0(A_34)
      | k4_xboole_0(A_34,B_33) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_102])).

tff(c_118,plain,(
    ! [A_34] :
      ( A_34 = '#skF_1'
      | v1_xboole_0('#skF_1')
      | v1_xboole_0(A_34)
      | k4_xboole_0(A_34,'#skF_1') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_116])).

tff(c_122,plain,(
    ! [A_35] :
      ( A_35 = '#skF_1'
      | v1_xboole_0(A_35)
      | k4_xboole_0(A_35,'#skF_1') != k1_xboole_0 ) ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_118])).

tff(c_18,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_125,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = '#skF_1'
    | k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_122,c_18])).

tff(c_131,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_125])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_140,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_8])).

tff(c_149,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_140])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:53:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.15  %$ r1_tarski > v1_zfmisc_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.15  
% 1.68/1.15  %Foreground sorts:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Background operators:
% 1.68/1.15  
% 1.68/1.15  
% 1.68/1.15  %Foreground operators:
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.68/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.68/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.68/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.68/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.15  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.68/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.68/1.15  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.68/1.15  
% 1.68/1.16  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.68/1.16  tff(f_62, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 1.68/1.16  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.68/1.16  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.68/1.16  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.68/1.16  tff(f_50, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 1.68/1.16  tff(c_37, plain, (![A_19, B_20]: (r1_tarski(A_19, B_20) | k4_xboole_0(A_19, B_20)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.16  tff(c_16, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.16  tff(c_41, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_16])).
% 1.68/1.16  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.68/1.16  tff(c_32, plain, (![A_16, B_17]: (r1_tarski(k3_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.16  tff(c_35, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_32])).
% 1.68/1.16  tff(c_42, plain, (![A_21, B_22]: (k4_xboole_0(A_21, B_22)=k1_xboole_0 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.16  tff(c_53, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(resolution, [status(thm)], [c_35, c_42])).
% 1.68/1.16  tff(c_82, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.16  tff(c_91, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_82])).
% 1.68/1.16  tff(c_94, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_53, c_91])).
% 1.68/1.16  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.68/1.16  tff(c_54, plain, (![A_7, B_8]: (k4_xboole_0(k3_xboole_0(A_7, B_8), A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_42])).
% 1.68/1.16  tff(c_22, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.16  tff(c_20, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.16  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.16  tff(c_102, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(A_32, B_31) | ~v1_zfmisc_1(B_31) | v1_xboole_0(B_31) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.68/1.16  tff(c_116, plain, (![B_33, A_34]: (B_33=A_34 | ~v1_zfmisc_1(B_33) | v1_xboole_0(B_33) | v1_xboole_0(A_34) | k4_xboole_0(A_34, B_33)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_102])).
% 1.68/1.16  tff(c_118, plain, (![A_34]: (A_34='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(A_34) | k4_xboole_0(A_34, '#skF_1')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_116])).
% 1.68/1.16  tff(c_122, plain, (![A_35]: (A_35='#skF_1' | v1_xboole_0(A_35) | k4_xboole_0(A_35, '#skF_1')!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_22, c_118])).
% 1.68/1.16  tff(c_18, plain, (~v1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.68/1.16  tff(c_125, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1' | k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')!=k1_xboole_0), inference(resolution, [status(thm)], [c_122, c_18])).
% 1.68/1.16  tff(c_131, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_125])).
% 1.68/1.16  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.68/1.16  tff(c_140, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_131, c_8])).
% 1.68/1.16  tff(c_149, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_94, c_140])).
% 1.68/1.16  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_149])).
% 1.68/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.16  
% 1.68/1.16  Inference rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Ref     : 0
% 1.68/1.16  #Sup     : 30
% 1.68/1.16  #Fact    : 0
% 1.68/1.16  #Define  : 0
% 1.68/1.16  #Split   : 0
% 1.68/1.16  #Chain   : 0
% 1.68/1.16  #Close   : 0
% 1.68/1.16  
% 1.68/1.16  Ordering : KBO
% 1.68/1.16  
% 1.68/1.16  Simplification rules
% 1.68/1.16  ----------------------
% 1.68/1.16  #Subsume      : 1
% 1.68/1.16  #Demod        : 6
% 1.68/1.16  #Tautology    : 17
% 1.68/1.16  #SimpNegUnit  : 2
% 1.68/1.16  #BackRed      : 1
% 1.68/1.16  
% 1.68/1.16  #Partial instantiations: 0
% 1.68/1.16  #Strategies tried      : 1
% 1.68/1.16  
% 1.68/1.16  Timing (in seconds)
% 1.68/1.16  ----------------------
% 1.68/1.16  Preprocessing        : 0.26
% 1.68/1.16  Parsing              : 0.15
% 1.68/1.16  CNF conversion       : 0.02
% 1.68/1.16  Main loop            : 0.13
% 1.68/1.16  Inferencing          : 0.06
% 1.68/1.16  Reduction            : 0.04
% 1.68/1.16  Demodulation         : 0.03
% 1.68/1.16  BG Simplification    : 0.01
% 1.68/1.16  Subsumption          : 0.02
% 1.68/1.16  Abstraction          : 0.01
% 1.68/1.16  MUC search           : 0.00
% 1.68/1.16  Cooper               : 0.00
% 1.68/1.16  Total                : 0.42
% 1.68/1.16  Index Insertion      : 0.00
% 1.68/1.16  Index Deletion       : 0.00
% 1.68/1.16  Index Matching       : 0.00
% 1.68/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
