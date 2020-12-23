%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:41 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   60 (  74 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_xboole_0(k2_relat_1(A),k2_relat_1(B))
             => r1_xboole_0(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t215_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    r1_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_80,plain,(
    ! [C_37,D_38,A_39,B_40] :
      ( ~ r1_xboole_0(C_37,D_38)
      | r1_xboole_0(k2_zfmisc_1(A_39,C_37),k2_zfmisc_1(B_40,D_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    ! [A_62,C_63,B_64,D_65] :
      ( k4_xboole_0(k2_zfmisc_1(A_62,C_63),k2_zfmisc_1(B_64,D_65)) = k2_zfmisc_1(A_62,C_63)
      | ~ r1_xboole_0(C_63,D_65) ) ),
    inference(resolution,[status(thm)],[c_80,c_14])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_xboole_0(A_1,C_3)
      | ~ r1_tarski(A_1,k4_xboole_0(B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_276,plain,(
    ! [C_85,D_88,B_87,A_89,A_86] :
      ( r1_xboole_0(A_89,k2_zfmisc_1(B_87,D_88))
      | ~ r1_tarski(A_89,k2_zfmisc_1(A_86,C_85))
      | ~ r1_xboole_0(C_85,D_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_2])).

tff(c_280,plain,(
    ! [A_90,B_91,D_92] :
      ( r1_xboole_0(A_90,k2_zfmisc_1(B_91,D_92))
      | ~ r1_xboole_0(k2_relat_1(A_90),D_92)
      | ~ v1_relat_1(A_90) ) ),
    inference(resolution,[status(thm)],[c_22,c_276])).

tff(c_294,plain,(
    ! [B_91] :
      ( r1_xboole_0('#skF_1',k2_zfmisc_1(B_91,k2_relat_1('#skF_2')))
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_280])).

tff(c_302,plain,(
    ! [B_93] : r1_xboole_0('#skF_1',k2_zfmisc_1(B_93,k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_294])).

tff(c_75,plain,(
    ! [A_36] :
      ( r1_tarski(A_36,k2_zfmisc_1(k1_relat_1(A_36),k2_relat_1(A_36)))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_171,plain,(
    ! [A_71] :
      ( k2_xboole_0(A_71,k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71))) = k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_75,c_6])).

tff(c_12,plain,(
    ! [A_6,B_7,C_8] :
      ( r1_xboole_0(A_6,B_7)
      | ~ r1_xboole_0(A_6,k2_xboole_0(B_7,C_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_192,plain,(
    ! [A_6,A_71] :
      ( r1_xboole_0(A_6,A_71)
      | ~ r1_xboole_0(A_6,k2_zfmisc_1(k1_relat_1(A_71),k2_relat_1(A_71)))
      | ~ v1_relat_1(A_71) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_12])).

tff(c_306,plain,
    ( r1_xboole_0('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_302,c_192])).

tff(c_312,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_306])).

tff(c_314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_312])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:46:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.25  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.08/1.25  
% 2.08/1.25  %Foreground sorts:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Background operators:
% 2.08/1.25  
% 2.08/1.25  
% 2.08/1.25  %Foreground operators:
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.25  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.08/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.08/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.08/1.25  
% 2.23/1.26  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_xboole_0(k2_relat_1(A), k2_relat_1(B)) => r1_xboole_0(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t215_relat_1)).
% 2.23/1.26  tff(f_65, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 2.23/1.26  tff(f_61, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.23/1.26  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.23/1.26  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 2.23/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.23/1.26  tff(f_51, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.23/1.26  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.23/1.26  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.23/1.26  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.23/1.26  tff(c_26, plain, (r1_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.23/1.26  tff(c_22, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.26  tff(c_80, plain, (![C_37, D_38, A_39, B_40]: (~r1_xboole_0(C_37, D_38) | r1_xboole_0(k2_zfmisc_1(A_39, C_37), k2_zfmisc_1(B_40, D_38)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.26  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.23/1.26  tff(c_144, plain, (![A_62, C_63, B_64, D_65]: (k4_xboole_0(k2_zfmisc_1(A_62, C_63), k2_zfmisc_1(B_64, D_65))=k2_zfmisc_1(A_62, C_63) | ~r1_xboole_0(C_63, D_65))), inference(resolution, [status(thm)], [c_80, c_14])).
% 2.23/1.26  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_xboole_0(A_1, C_3) | ~r1_tarski(A_1, k4_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.26  tff(c_276, plain, (![C_85, D_88, B_87, A_89, A_86]: (r1_xboole_0(A_89, k2_zfmisc_1(B_87, D_88)) | ~r1_tarski(A_89, k2_zfmisc_1(A_86, C_85)) | ~r1_xboole_0(C_85, D_88))), inference(superposition, [status(thm), theory('equality')], [c_144, c_2])).
% 2.23/1.26  tff(c_280, plain, (![A_90, B_91, D_92]: (r1_xboole_0(A_90, k2_zfmisc_1(B_91, D_92)) | ~r1_xboole_0(k2_relat_1(A_90), D_92) | ~v1_relat_1(A_90))), inference(resolution, [status(thm)], [c_22, c_276])).
% 2.23/1.26  tff(c_294, plain, (![B_91]: (r1_xboole_0('#skF_1', k2_zfmisc_1(B_91, k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_26, c_280])).
% 2.23/1.26  tff(c_302, plain, (![B_93]: (r1_xboole_0('#skF_1', k2_zfmisc_1(B_93, k2_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_294])).
% 2.23/1.26  tff(c_75, plain, (![A_36]: (r1_tarski(A_36, k2_zfmisc_1(k1_relat_1(A_36), k2_relat_1(A_36))) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.23/1.26  tff(c_6, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.26  tff(c_171, plain, (![A_71]: (k2_xboole_0(A_71, k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)))=k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71)) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_75, c_6])).
% 2.23/1.26  tff(c_12, plain, (![A_6, B_7, C_8]: (r1_xboole_0(A_6, B_7) | ~r1_xboole_0(A_6, k2_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.26  tff(c_192, plain, (![A_6, A_71]: (r1_xboole_0(A_6, A_71) | ~r1_xboole_0(A_6, k2_zfmisc_1(k1_relat_1(A_71), k2_relat_1(A_71))) | ~v1_relat_1(A_71))), inference(superposition, [status(thm), theory('equality')], [c_171, c_12])).
% 2.23/1.26  tff(c_306, plain, (r1_xboole_0('#skF_1', '#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_302, c_192])).
% 2.23/1.26  tff(c_312, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_306])).
% 2.23/1.26  tff(c_314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_312])).
% 2.23/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  Inference rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Ref     : 0
% 2.23/1.26  #Sup     : 65
% 2.23/1.26  #Fact    : 0
% 2.23/1.26  #Define  : 0
% 2.23/1.26  #Split   : 0
% 2.23/1.26  #Chain   : 0
% 2.23/1.26  #Close   : 0
% 2.23/1.26  
% 2.23/1.26  Ordering : KBO
% 2.23/1.26  
% 2.23/1.26  Simplification rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Subsume      : 2
% 2.23/1.26  #Demod        : 2
% 2.23/1.26  #Tautology    : 23
% 2.23/1.26  #SimpNegUnit  : 1
% 2.23/1.26  #BackRed      : 0
% 2.23/1.26  
% 2.23/1.26  #Partial instantiations: 0
% 2.23/1.26  #Strategies tried      : 1
% 2.23/1.26  
% 2.23/1.26  Timing (in seconds)
% 2.23/1.26  ----------------------
% 2.23/1.26  Preprocessing        : 0.27
% 2.23/1.26  Parsing              : 0.15
% 2.23/1.26  CNF conversion       : 0.02
% 2.23/1.26  Main loop            : 0.23
% 2.23/1.26  Inferencing          : 0.10
% 2.23/1.26  Reduction            : 0.05
% 2.23/1.26  Demodulation         : 0.04
% 2.23/1.26  BG Simplification    : 0.01
% 2.23/1.26  Subsumption          : 0.05
% 2.23/1.26  Abstraction          : 0.01
% 2.23/1.26  MUC search           : 0.00
% 2.23/1.26  Cooper               : 0.00
% 2.23/1.26  Total                : 0.52
% 2.23/1.26  Index Insertion      : 0.00
% 2.23/1.27  Index Deletion       : 0.00
% 2.23/1.27  Index Matching       : 0.00
% 2.23/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
