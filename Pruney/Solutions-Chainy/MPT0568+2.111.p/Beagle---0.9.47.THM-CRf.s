%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:35 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   51 (  52 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  57 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    ! [A_30,B_31] : ~ r2_hidden(A_30,k2_zfmisc_1(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_99,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_93])).

tff(c_66,plain,(
    ! [A_28] : k2_zfmisc_1(A_28,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_16,B_17] : v1_relat_1(k2_zfmisc_1(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_26])).

tff(c_36,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_396,plain,(
    ! [A_71,B_72,C_73] :
      ( r2_hidden('#skF_2'(A_71,B_72,C_73),k2_relat_1(C_73))
      | ~ r2_hidden(A_71,k10_relat_1(C_73,B_72))
      | ~ v1_relat_1(C_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_401,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_2'(A_71,B_72,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_71,k10_relat_1(k1_xboole_0,B_72))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_396])).

tff(c_404,plain,(
    ! [A_71,B_72] :
      ( r2_hidden('#skF_2'(A_71,B_72,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_71,k10_relat_1(k1_xboole_0,B_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_401])).

tff(c_430,plain,(
    ! [A_74,B_75] : ~ r2_hidden(A_74,k10_relat_1(k1_xboole_0,B_75)) ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_404])).

tff(c_448,plain,(
    ! [A_76,B_77] : r1_xboole_0(A_76,k10_relat_1(k1_xboole_0,B_77)) ),
    inference(resolution,[status(thm)],[c_4,c_430])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_491,plain,(
    ! [A_83,B_84] : k4_xboole_0(A_83,k10_relat_1(k1_xboole_0,B_84)) = A_83 ),
    inference(resolution,[status(thm)],[c_448,c_14])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_113])).

tff(c_131,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_128])).

tff(c_506,plain,(
    ! [B_84] : k10_relat_1(k1_xboole_0,B_84) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_491,c_131])).

tff(c_40,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_549,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_506,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.27  
% 2.16/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.27  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 2.16/1.27  
% 2.16/1.27  %Foreground sorts:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Background operators:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Foreground operators:
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.16/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.16/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.16/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.16/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.16/1.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.16/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.16/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.16/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.16/1.27  
% 2.16/1.29  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.16/1.29  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.16/1.29  tff(f_62, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 2.16/1.29  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.16/1.29  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.16/1.29  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.16/1.29  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.16/1.29  tff(f_45, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.16/1.29  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.16/1.29  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.16/1.29  tff(f_81, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.16/1.29  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.16/1.29  tff(c_20, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.29  tff(c_93, plain, (![A_30, B_31]: (~r2_hidden(A_30, k2_zfmisc_1(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.16/1.29  tff(c_99, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_93])).
% 2.16/1.29  tff(c_66, plain, (![A_28]: (k2_zfmisc_1(A_28, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.16/1.29  tff(c_26, plain, (![A_16, B_17]: (v1_relat_1(k2_zfmisc_1(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.16/1.29  tff(c_70, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_66, c_26])).
% 2.16/1.29  tff(c_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.16/1.29  tff(c_396, plain, (![A_71, B_72, C_73]: (r2_hidden('#skF_2'(A_71, B_72, C_73), k2_relat_1(C_73)) | ~r2_hidden(A_71, k10_relat_1(C_73, B_72)) | ~v1_relat_1(C_73))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.16/1.29  tff(c_401, plain, (![A_71, B_72]: (r2_hidden('#skF_2'(A_71, B_72, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_71, k10_relat_1(k1_xboole_0, B_72)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_396])).
% 2.16/1.29  tff(c_404, plain, (![A_71, B_72]: (r2_hidden('#skF_2'(A_71, B_72, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_71, k10_relat_1(k1_xboole_0, B_72)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_401])).
% 2.16/1.29  tff(c_430, plain, (![A_74, B_75]: (~r2_hidden(A_74, k10_relat_1(k1_xboole_0, B_75)))), inference(negUnitSimplification, [status(thm)], [c_99, c_404])).
% 2.16/1.29  tff(c_448, plain, (![A_76, B_77]: (r1_xboole_0(A_76, k10_relat_1(k1_xboole_0, B_77)))), inference(resolution, [status(thm)], [c_4, c_430])).
% 2.16/1.29  tff(c_14, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.16/1.29  tff(c_491, plain, (![A_83, B_84]: (k4_xboole_0(A_83, k10_relat_1(k1_xboole_0, B_84))=A_83)), inference(resolution, [status(thm)], [c_448, c_14])).
% 2.16/1.29  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.16/1.29  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.16/1.29  tff(c_113, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.16/1.29  tff(c_128, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_113])).
% 2.16/1.29  tff(c_131, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_128])).
% 2.16/1.29  tff(c_506, plain, (![B_84]: (k10_relat_1(k1_xboole_0, B_84)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_491, c_131])).
% 2.16/1.29  tff(c_40, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.16/1.29  tff(c_549, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_506, c_40])).
% 2.16/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.16/1.29  
% 2.16/1.29  Inference rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Ref     : 0
% 2.16/1.29  #Sup     : 117
% 2.16/1.29  #Fact    : 0
% 2.16/1.29  #Define  : 0
% 2.16/1.29  #Split   : 0
% 2.16/1.29  #Chain   : 0
% 2.16/1.29  #Close   : 0
% 2.16/1.29  
% 2.16/1.29  Ordering : KBO
% 2.16/1.29  
% 2.16/1.29  Simplification rules
% 2.16/1.29  ----------------------
% 2.16/1.29  #Subsume      : 11
% 2.16/1.29  #Demod        : 45
% 2.16/1.29  #Tautology    : 72
% 2.16/1.29  #SimpNegUnit  : 1
% 2.16/1.29  #BackRed      : 5
% 2.16/1.29  
% 2.16/1.29  #Partial instantiations: 0
% 2.16/1.29  #Strategies tried      : 1
% 2.16/1.29  
% 2.16/1.29  Timing (in seconds)
% 2.16/1.29  ----------------------
% 2.16/1.29  Preprocessing        : 0.29
% 2.16/1.29  Parsing              : 0.16
% 2.16/1.29  CNF conversion       : 0.02
% 2.16/1.29  Main loop            : 0.24
% 2.16/1.29  Inferencing          : 0.10
% 2.16/1.29  Reduction            : 0.07
% 2.16/1.29  Demodulation         : 0.05
% 2.16/1.29  BG Simplification    : 0.01
% 2.16/1.29  Subsumption          : 0.04
% 2.16/1.29  Abstraction          : 0.01
% 2.16/1.29  MUC search           : 0.00
% 2.16/1.29  Cooper               : 0.00
% 2.16/1.29  Total                : 0.55
% 2.16/1.29  Index Insertion      : 0.00
% 2.16/1.29  Index Deletion       : 0.00
% 2.16/1.29  Index Matching       : 0.00
% 2.16/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
