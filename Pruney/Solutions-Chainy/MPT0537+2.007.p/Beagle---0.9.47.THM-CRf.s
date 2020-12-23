%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:20 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   54 (  55 expanded)
%              Number of leaves         :   33 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :   52 (  54 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k8_relat_1(k1_xboole_0,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( ( r1_xboole_0(A,B)
        | r1_xboole_0(C,D) )
     => r1_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(c_40,plain,(
    k8_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_16,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [B_59,A_60] :
      ( r1_xboole_0(B_59,A_60)
      | ~ r1_xboole_0(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_18,c_77])).

tff(c_290,plain,(
    ! [C_87,D_88,A_89,B_90] :
      ( ~ r1_xboole_0(C_87,D_88)
      | r1_xboole_0(k2_zfmisc_1(A_89,C_87),k2_zfmisc_1(B_90,D_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_104,plain,(
    ! [A_66,B_67,C_68] :
      ( ~ r1_xboole_0(A_66,B_67)
      | ~ r2_hidden(C_68,k3_xboole_0(A_66,B_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_147,plain,(
    ! [A_75,B_76] :
      ( ~ r1_xboole_0(A_75,B_76)
      | v1_xboole_0(k3_xboole_0(A_75,B_76)) ) ),
    inference(resolution,[status(thm)],[c_4,c_104])).

tff(c_156,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_147])).

tff(c_307,plain,(
    ! [B_91,D_92] :
      ( v1_xboole_0(k2_zfmisc_1(B_91,D_92))
      | ~ r1_xboole_0(D_92,D_92) ) ),
    inference(resolution,[status(thm)],[c_290,c_156])).

tff(c_323,plain,(
    ! [B_93] : v1_xboole_0(k2_zfmisc_1(B_93,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_80,c_307])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_327,plain,(
    ! [B_93] : k2_zfmisc_1(B_93,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_323,c_8])).

tff(c_496,plain,(
    ! [B_113,A_114] :
      ( k3_xboole_0(B_113,k2_zfmisc_1(k1_relat_1(B_113),A_114)) = k8_relat_1(A_114,B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_522,plain,(
    ! [B_113] :
      ( k8_relat_1(k1_xboole_0,B_113) = k3_xboole_0(B_113,k1_xboole_0)
      | ~ v1_relat_1(B_113) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_496])).

tff(c_555,plain,(
    ! [B_122] :
      ( k8_relat_1(k1_xboole_0,B_122) = k1_xboole_0
      | ~ v1_relat_1(B_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_522])).

tff(c_558,plain,(
    k8_relat_1(k1_xboole_0,'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_555])).

tff(c_562,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_558])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:42:52 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.32  
% 2.13/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.32  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.13/1.32  
% 2.13/1.32  %Foreground sorts:
% 2.13/1.32  
% 2.13/1.32  
% 2.13/1.32  %Background operators:
% 2.13/1.32  
% 2.13/1.32  
% 2.13/1.32  %Foreground operators:
% 2.13/1.32  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.13/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.13/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.32  
% 2.52/1.34  tff(f_88, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k8_relat_1(k1_xboole_0, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t137_relat_1)).
% 2.52/1.34  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.52/1.34  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.52/1.34  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.52/1.34  tff(f_77, axiom, (![A, B, C, D]: ((r1_xboole_0(A, B) | r1_xboole_0(C, D)) => r1_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t127_zfmisc_1)).
% 2.52/1.34  tff(f_33, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.52/1.34  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.52/1.34  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.52/1.34  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.52/1.34  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 2.52/1.34  tff(c_40, plain, (k8_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.52/1.34  tff(c_42, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.52/1.34  tff(c_16, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.52/1.34  tff(c_18, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.34  tff(c_77, plain, (![B_59, A_60]: (r1_xboole_0(B_59, A_60) | ~r1_xboole_0(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.52/1.34  tff(c_80, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_18, c_77])).
% 2.52/1.34  tff(c_290, plain, (![C_87, D_88, A_89, B_90]: (~r1_xboole_0(C_87, D_88) | r1_xboole_0(k2_zfmisc_1(A_89, C_87), k2_zfmisc_1(B_90, D_88)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.52/1.34  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.52/1.34  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.52/1.34  tff(c_104, plain, (![A_66, B_67, C_68]: (~r1_xboole_0(A_66, B_67) | ~r2_hidden(C_68, k3_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.52/1.34  tff(c_147, plain, (![A_75, B_76]: (~r1_xboole_0(A_75, B_76) | v1_xboole_0(k3_xboole_0(A_75, B_76)))), inference(resolution, [status(thm)], [c_4, c_104])).
% 2.52/1.34  tff(c_156, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | v1_xboole_0(A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_147])).
% 2.52/1.34  tff(c_307, plain, (![B_91, D_92]: (v1_xboole_0(k2_zfmisc_1(B_91, D_92)) | ~r1_xboole_0(D_92, D_92))), inference(resolution, [status(thm)], [c_290, c_156])).
% 2.52/1.34  tff(c_323, plain, (![B_93]: (v1_xboole_0(k2_zfmisc_1(B_93, k1_xboole_0)))), inference(resolution, [status(thm)], [c_80, c_307])).
% 2.52/1.34  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.34  tff(c_327, plain, (![B_93]: (k2_zfmisc_1(B_93, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_323, c_8])).
% 2.52/1.34  tff(c_496, plain, (![B_113, A_114]: (k3_xboole_0(B_113, k2_zfmisc_1(k1_relat_1(B_113), A_114))=k8_relat_1(A_114, B_113) | ~v1_relat_1(B_113))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.52/1.34  tff(c_522, plain, (![B_113]: (k8_relat_1(k1_xboole_0, B_113)=k3_xboole_0(B_113, k1_xboole_0) | ~v1_relat_1(B_113))), inference(superposition, [status(thm), theory('equality')], [c_327, c_496])).
% 2.52/1.34  tff(c_555, plain, (![B_122]: (k8_relat_1(k1_xboole_0, B_122)=k1_xboole_0 | ~v1_relat_1(B_122))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_522])).
% 2.52/1.34  tff(c_558, plain, (k8_relat_1(k1_xboole_0, '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_42, c_555])).
% 2.52/1.34  tff(c_562, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_558])).
% 2.52/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.34  
% 2.52/1.34  Inference rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Ref     : 0
% 2.52/1.34  #Sup     : 117
% 2.52/1.34  #Fact    : 0
% 2.52/1.34  #Define  : 0
% 2.52/1.34  #Split   : 1
% 2.52/1.34  #Chain   : 0
% 2.52/1.34  #Close   : 0
% 2.52/1.34  
% 2.52/1.34  Ordering : KBO
% 2.52/1.34  
% 2.52/1.34  Simplification rules
% 2.52/1.34  ----------------------
% 2.52/1.34  #Subsume      : 8
% 2.52/1.34  #Demod        : 48
% 2.52/1.34  #Tautology    : 66
% 2.52/1.34  #SimpNegUnit  : 3
% 2.52/1.34  #BackRed      : 2
% 2.52/1.34  
% 2.52/1.34  #Partial instantiations: 0
% 2.52/1.34  #Strategies tried      : 1
% 2.52/1.34  
% 2.52/1.34  Timing (in seconds)
% 2.52/1.34  ----------------------
% 2.52/1.34  Preprocessing        : 0.33
% 2.52/1.34  Parsing              : 0.18
% 2.52/1.34  CNF conversion       : 0.02
% 2.52/1.34  Main loop            : 0.25
% 2.52/1.34  Inferencing          : 0.10
% 2.52/1.34  Reduction            : 0.07
% 2.52/1.34  Demodulation         : 0.05
% 2.52/1.34  BG Simplification    : 0.02
% 2.52/1.34  Subsumption          : 0.04
% 2.52/1.34  Abstraction          : 0.02
% 2.52/1.34  MUC search           : 0.00
% 2.52/1.34  Cooper               : 0.00
% 2.52/1.34  Total                : 0.60
% 2.52/1.34  Index Insertion      : 0.00
% 2.52/1.34  Index Deletion       : 0.00
% 2.52/1.34  Index Matching       : 0.00
% 2.52/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
