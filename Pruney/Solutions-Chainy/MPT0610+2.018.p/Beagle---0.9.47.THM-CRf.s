%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:38 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   41 (  56 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 (  98 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k1_relat_1(A),k1_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t214_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_20,plain,(
    r1_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_25,plain,(
    ! [B_14,A_15] :
      ( r1_xboole_0(B_14,A_15)
      | ~ r1_xboole_0(A_15,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_28,plain,(
    r1_xboole_0(k1_relat_1('#skF_2'),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_20,c_25])).

tff(c_41,plain,(
    ! [A_25,B_26,C_27,D_28] :
      ( ~ r1_xboole_0(A_25,B_26)
      | r1_xboole_0(k2_zfmisc_1(A_25,C_27),k2_zfmisc_1(B_26,D_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [B_26,D_28,A_25,C_27] :
      ( r1_xboole_0(k2_zfmisc_1(B_26,D_28),k2_zfmisc_1(A_25,C_27))
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(resolution,[status(thm)],[c_41,c_2])).

tff(c_36,plain,(
    ! [A_24] :
      ( r1_tarski(A_24,k2_zfmisc_1(k1_relat_1(A_24),k2_relat_1(A_24)))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_83,plain,(
    ! [A_47] :
      ( k2_xboole_0(A_47,k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47))) = k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(resolution,[status(thm)],[c_36,c_4])).

tff(c_10,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_xboole_0(A_5,B_6)
      | ~ r1_xboole_0(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_104,plain,(
    ! [A_48,A_49] :
      ( r1_xboole_0(A_48,A_49)
      | ~ r1_xboole_0(A_48,k2_zfmisc_1(k1_relat_1(A_49),k2_relat_1(A_49)))
      | ~ v1_relat_1(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_10])).

tff(c_173,plain,(
    ! [B_59,D_60,A_61] :
      ( r1_xboole_0(k2_zfmisc_1(B_59,D_60),A_61)
      | ~ v1_relat_1(A_61)
      | ~ r1_xboole_0(k1_relat_1(A_61),B_59) ) ),
    inference(resolution,[status(thm)],[c_44,c_104])).

tff(c_178,plain,(
    ! [D_60] :
      ( r1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_1'),D_60),'#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_28,c_173])).

tff(c_188,plain,(
    ! [D_62] : r1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_1'),D_62),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_178])).

tff(c_196,plain,(
    ! [D_64] : r1_xboole_0('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_1'),D_64)) ),
    inference(resolution,[status(thm)],[c_188,c_2])).

tff(c_98,plain,(
    ! [A_5,A_47] :
      ( r1_xboole_0(A_5,A_47)
      | ~ r1_xboole_0(A_5,k2_zfmisc_1(k1_relat_1(A_47),k2_relat_1(A_47)))
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_10])).

tff(c_200,plain,
    ( r1_xboole_0('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_196,c_98])).

tff(c_205,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_200])).

tff(c_219,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_205,c_2])).

tff(c_223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:13:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.23  
% 2.19/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.23  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.19/1.23  
% 2.19/1.23  %Foreground sorts:
% 2.19/1.23  
% 2.19/1.23  
% 2.19/1.23  %Background operators:
% 2.19/1.23  
% 2.19/1.23  
% 2.19/1.23  %Foreground operators:
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.19/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.19/1.23  
% 2.24/1.24  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k1_relat_1(A), k1_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t214_relat_1)).
% 2.24/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.24/1.24  tff(f_55, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.24/1.24  tff(f_59, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 2.24/1.24  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.24/1.24  tff(f_49, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.24/1.24  tff(c_18, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.24  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.24  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.24  tff(c_20, plain, (r1_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.24/1.24  tff(c_25, plain, (![B_14, A_15]: (r1_xboole_0(B_14, A_15) | ~r1_xboole_0(A_15, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.24  tff(c_28, plain, (r1_xboole_0(k1_relat_1('#skF_2'), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_20, c_25])).
% 2.24/1.24  tff(c_41, plain, (![A_25, B_26, C_27, D_28]: (~r1_xboole_0(A_25, B_26) | r1_xboole_0(k2_zfmisc_1(A_25, C_27), k2_zfmisc_1(B_26, D_28)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.25  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.25  tff(c_44, plain, (![B_26, D_28, A_25, C_27]: (r1_xboole_0(k2_zfmisc_1(B_26, D_28), k2_zfmisc_1(A_25, C_27)) | ~r1_xboole_0(A_25, B_26))), inference(resolution, [status(thm)], [c_41, c_2])).
% 2.24/1.25  tff(c_36, plain, (![A_24]: (r1_tarski(A_24, k2_zfmisc_1(k1_relat_1(A_24), k2_relat_1(A_24))) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.24/1.25  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.24/1.25  tff(c_83, plain, (![A_47]: (k2_xboole_0(A_47, k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47)))=k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47)) | ~v1_relat_1(A_47))), inference(resolution, [status(thm)], [c_36, c_4])).
% 2.24/1.25  tff(c_10, plain, (![A_5, B_6, C_7]: (r1_xboole_0(A_5, B_6) | ~r1_xboole_0(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.25  tff(c_104, plain, (![A_48, A_49]: (r1_xboole_0(A_48, A_49) | ~r1_xboole_0(A_48, k2_zfmisc_1(k1_relat_1(A_49), k2_relat_1(A_49))) | ~v1_relat_1(A_49))), inference(superposition, [status(thm), theory('equality')], [c_83, c_10])).
% 2.24/1.25  tff(c_173, plain, (![B_59, D_60, A_61]: (r1_xboole_0(k2_zfmisc_1(B_59, D_60), A_61) | ~v1_relat_1(A_61) | ~r1_xboole_0(k1_relat_1(A_61), B_59))), inference(resolution, [status(thm)], [c_44, c_104])).
% 2.24/1.25  tff(c_178, plain, (![D_60]: (r1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_1'), D_60), '#skF_2') | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_28, c_173])).
% 2.24/1.25  tff(c_188, plain, (![D_62]: (r1_xboole_0(k2_zfmisc_1(k1_relat_1('#skF_1'), D_62), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_178])).
% 2.24/1.25  tff(c_196, plain, (![D_64]: (r1_xboole_0('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_1'), D_64)))), inference(resolution, [status(thm)], [c_188, c_2])).
% 2.24/1.25  tff(c_98, plain, (![A_5, A_47]: (r1_xboole_0(A_5, A_47) | ~r1_xboole_0(A_5, k2_zfmisc_1(k1_relat_1(A_47), k2_relat_1(A_47))) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_83, c_10])).
% 2.24/1.25  tff(c_200, plain, (r1_xboole_0('#skF_2', '#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_196, c_98])).
% 2.24/1.25  tff(c_205, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_200])).
% 2.24/1.25  tff(c_219, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_205, c_2])).
% 2.24/1.25  tff(c_223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_219])).
% 2.24/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.25  
% 2.24/1.25  Inference rules
% 2.24/1.25  ----------------------
% 2.24/1.25  #Ref     : 0
% 2.24/1.25  #Sup     : 44
% 2.24/1.25  #Fact    : 0
% 2.24/1.25  #Define  : 0
% 2.24/1.25  #Split   : 0
% 2.24/1.25  #Chain   : 0
% 2.24/1.25  #Close   : 0
% 2.24/1.25  
% 2.24/1.25  Ordering : KBO
% 2.24/1.25  
% 2.24/1.25  Simplification rules
% 2.24/1.25  ----------------------
% 2.24/1.25  #Subsume      : 4
% 2.24/1.25  #Demod        : 5
% 2.24/1.25  #Tautology    : 8
% 2.24/1.25  #SimpNegUnit  : 1
% 2.24/1.25  #BackRed      : 0
% 2.24/1.25  
% 2.24/1.25  #Partial instantiations: 0
% 2.24/1.25  #Strategies tried      : 1
% 2.24/1.25  
% 2.24/1.25  Timing (in seconds)
% 2.24/1.25  ----------------------
% 2.24/1.25  Preprocessing        : 0.27
% 2.24/1.25  Parsing              : 0.16
% 2.24/1.25  CNF conversion       : 0.02
% 2.24/1.25  Main loop            : 0.22
% 2.24/1.25  Inferencing          : 0.09
% 2.24/1.25  Reduction            : 0.05
% 2.24/1.25  Demodulation         : 0.04
% 2.24/1.25  BG Simplification    : 0.01
% 2.24/1.25  Subsumption          : 0.06
% 2.24/1.25  Abstraction          : 0.01
% 2.24/1.25  MUC search           : 0.00
% 2.24/1.25  Cooper               : 0.00
% 2.24/1.25  Total                : 0.52
% 2.24/1.25  Index Insertion      : 0.00
% 2.24/1.25  Index Deletion       : 0.00
% 2.24/1.25  Index Matching       : 0.00
% 2.24/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
