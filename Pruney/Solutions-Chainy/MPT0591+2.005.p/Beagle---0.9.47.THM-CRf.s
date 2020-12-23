%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:09 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   47 (  60 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 (  98 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
              & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t195_relat_1)).

tff(f_47,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k2_relat_1(k2_zfmisc_1(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k1_relat_1(k2_zfmisc_1(A,B)),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_17] :
      ( r1_tarski(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17)))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_154,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( ~ r1_tarski(k2_zfmisc_1(A_49,B_50),k2_zfmisc_1(C_51,D_52))
      | r1_tarski(B_50,D_52)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [B_50,A_49] :
      ( r1_tarski(B_50,k2_relat_1(k2_zfmisc_1(A_49,B_50)))
      | v1_xboole_0(A_49)
      | ~ v1_relat_1(k2_zfmisc_1(A_49,B_50)) ) ),
    inference(resolution,[status(thm)],[c_20,c_154])).

tff(c_172,plain,(
    ! [B_53,A_54] :
      ( r1_tarski(B_53,k2_relat_1(k2_zfmisc_1(A_54,B_53)))
      | v1_xboole_0(A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_161])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(k2_relat_1(k2_zfmisc_1(A_15,B_16)),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_33,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_41,plain,(
    ! [A_15,B_16] :
      ( k2_relat_1(k2_zfmisc_1(A_15,B_16)) = B_16
      | ~ r1_tarski(B_16,k2_relat_1(k2_zfmisc_1(A_15,B_16))) ) ),
    inference(resolution,[status(thm)],[c_18,c_33])).

tff(c_201,plain,(
    ! [A_59,B_60] :
      ( k2_relat_1(k2_zfmisc_1(A_59,B_60)) = B_60
      | v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_172,c_41])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_53,plain,(
    ! [B_33,A_34,D_35,C_36] :
      ( ~ r1_tarski(k2_zfmisc_1(B_33,A_34),k2_zfmisc_1(D_35,C_36))
      | r1_tarski(B_33,D_35)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_57,plain,(
    ! [B_33,A_34] :
      ( r1_tarski(B_33,k1_relat_1(k2_zfmisc_1(B_33,A_34)))
      | v1_xboole_0(A_34)
      | ~ v1_relat_1(k2_zfmisc_1(B_33,A_34)) ) ),
    inference(resolution,[status(thm)],[c_20,c_53])).

tff(c_67,plain,(
    ! [B_37,A_38] :
      ( r1_tarski(B_37,k1_relat_1(k2_zfmisc_1(B_37,A_38)))
      | v1_xboole_0(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_57])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k1_relat_1(k2_zfmisc_1(A_13,B_14)),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    ! [A_13,B_14] :
      ( k1_relat_1(k2_zfmisc_1(A_13,B_14)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(resolution,[status(thm)],[c_16,c_33])).

tff(c_91,plain,(
    ! [B_43,A_44] :
      ( k1_relat_1(k2_zfmisc_1(B_43,A_44)) = B_43
      | v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_67,c_40])).

tff(c_22,plain,
    ( k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_2'
    | k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_117,plain,(
    v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_50])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_124,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_117,c_2])).

tff(c_128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_124])).

tff(c_129,plain,(
    k2_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_231,plain,(
    v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_129])).

tff(c_238,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_231,c_2])).

tff(c_242,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  %$ r1_tarski > v1_xboole_0 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.92/1.20  
% 1.92/1.20  %Foreground sorts:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Background operators:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Foreground operators:
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.92/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.20  
% 1.92/1.21  tff(f_68, negated_conjecture, ~(![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t195_relat_1)).
% 1.92/1.21  tff(f_47, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.92/1.21  tff(f_55, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.92/1.21  tff(f_45, axiom, (![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 1.92/1.21  tff(f_51, axiom, (![A, B]: r1_tarski(k2_relat_1(k2_zfmisc_1(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t194_relat_1)).
% 1.92/1.21  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.92/1.21  tff(f_49, axiom, (![A, B]: r1_tarski(k1_relat_1(k2_zfmisc_1(A, B)), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t193_relat_1)).
% 1.92/1.21  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.92/1.21  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.21  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.92/1.21  tff(c_20, plain, (![A_17]: (r1_tarski(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17))) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.92/1.21  tff(c_154, plain, (![A_49, B_50, C_51, D_52]: (~r1_tarski(k2_zfmisc_1(A_49, B_50), k2_zfmisc_1(C_51, D_52)) | r1_tarski(B_50, D_52) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.21  tff(c_161, plain, (![B_50, A_49]: (r1_tarski(B_50, k2_relat_1(k2_zfmisc_1(A_49, B_50))) | v1_xboole_0(A_49) | ~v1_relat_1(k2_zfmisc_1(A_49, B_50)))), inference(resolution, [status(thm)], [c_20, c_154])).
% 1.92/1.21  tff(c_172, plain, (![B_53, A_54]: (r1_tarski(B_53, k2_relat_1(k2_zfmisc_1(A_54, B_53))) | v1_xboole_0(A_54))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_161])).
% 1.92/1.21  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(k2_relat_1(k2_zfmisc_1(A_15, B_16)), B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.92/1.21  tff(c_33, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.21  tff(c_41, plain, (![A_15, B_16]: (k2_relat_1(k2_zfmisc_1(A_15, B_16))=B_16 | ~r1_tarski(B_16, k2_relat_1(k2_zfmisc_1(A_15, B_16))))), inference(resolution, [status(thm)], [c_18, c_33])).
% 1.92/1.21  tff(c_201, plain, (![A_59, B_60]: (k2_relat_1(k2_zfmisc_1(A_59, B_60))=B_60 | v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_172, c_41])).
% 1.92/1.21  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.21  tff(c_53, plain, (![B_33, A_34, D_35, C_36]: (~r1_tarski(k2_zfmisc_1(B_33, A_34), k2_zfmisc_1(D_35, C_36)) | r1_tarski(B_33, D_35) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.21  tff(c_57, plain, (![B_33, A_34]: (r1_tarski(B_33, k1_relat_1(k2_zfmisc_1(B_33, A_34))) | v1_xboole_0(A_34) | ~v1_relat_1(k2_zfmisc_1(B_33, A_34)))), inference(resolution, [status(thm)], [c_20, c_53])).
% 1.92/1.21  tff(c_67, plain, (![B_37, A_38]: (r1_tarski(B_37, k1_relat_1(k2_zfmisc_1(B_37, A_38))) | v1_xboole_0(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_57])).
% 1.92/1.21  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k1_relat_1(k2_zfmisc_1(A_13, B_14)), A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.92/1.21  tff(c_40, plain, (![A_13, B_14]: (k1_relat_1(k2_zfmisc_1(A_13, B_14))=A_13 | ~r1_tarski(A_13, k1_relat_1(k2_zfmisc_1(A_13, B_14))))), inference(resolution, [status(thm)], [c_16, c_33])).
% 1.92/1.21  tff(c_91, plain, (![B_43, A_44]: (k1_relat_1(k2_zfmisc_1(B_43, A_44))=B_43 | v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_67, c_40])).
% 1.92/1.21  tff(c_22, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_2' | k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.92/1.21  tff(c_50, plain, (k1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_22])).
% 1.92/1.21  tff(c_117, plain, (v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_91, c_50])).
% 1.92/1.21  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.21  tff(c_124, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_117, c_2])).
% 1.92/1.21  tff(c_128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_124])).
% 1.92/1.21  tff(c_129, plain, (k2_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_22])).
% 1.92/1.21  tff(c_231, plain, (v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_201, c_129])).
% 1.92/1.21  tff(c_238, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_231, c_2])).
% 1.92/1.21  tff(c_242, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_238])).
% 1.92/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  Inference rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Ref     : 0
% 1.92/1.21  #Sup     : 41
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
% 1.92/1.21  #Subsume      : 2
% 1.92/1.21  #Demod        : 26
% 1.92/1.21  #Tautology    : 20
% 1.92/1.21  #SimpNegUnit  : 2
% 1.92/1.21  #BackRed      : 0
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.22  Preprocessing        : 0.29
% 1.92/1.22  Parsing              : 0.16
% 1.92/1.22  CNF conversion       : 0.02
% 1.92/1.22  Main loop            : 0.17
% 1.92/1.22  Inferencing          : 0.07
% 1.92/1.22  Reduction            : 0.05
% 1.92/1.22  Demodulation         : 0.04
% 1.92/1.22  BG Simplification    : 0.01
% 1.92/1.22  Subsumption          : 0.03
% 1.92/1.22  Abstraction          : 0.01
% 1.92/1.22  MUC search           : 0.00
% 1.92/1.22  Cooper               : 0.00
% 1.92/1.22  Total                : 0.49
% 1.92/1.22  Index Insertion      : 0.00
% 1.92/1.22  Index Deletion       : 0.00
% 1.92/1.22  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
