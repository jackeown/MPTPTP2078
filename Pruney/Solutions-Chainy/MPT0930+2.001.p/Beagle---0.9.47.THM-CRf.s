%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:25 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   46 (  63 expanded)
%              Number of leaves         :   23 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  98 expanded)
%              Number of equality atoms :    8 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( r2_hidden(B,A)
           => ( r2_hidden(k1_mcart_1(B),k1_relat_1(A))
              & r2_hidden(k2_mcart_1(B),k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_mcart_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_541,plain,(
    ! [A_84] :
      ( k3_xboole_0(A_84,k2_zfmisc_1(k1_relat_1(A_84),k2_relat_1(A_84))) = A_84
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_104,plain,(
    ! [D_27,A_28,B_29] :
      ( r2_hidden(D_27,A_28)
      | ~ r2_hidden(D_27,k4_xboole_0(A_28,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_135,plain,(
    ! [D_32,A_33,B_34] :
      ( r2_hidden(D_32,A_33)
      | ~ r2_hidden(D_32,k3_xboole_0(A_33,B_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_104])).

tff(c_141,plain,(
    ! [D_32,B_2,A_1] :
      ( r2_hidden(D_32,B_2)
      | ~ r2_hidden(D_32,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_761,plain,(
    ! [D_106,A_107] :
      ( r2_hidden(D_106,k2_zfmisc_1(k1_relat_1(A_107),k2_relat_1(A_107)))
      | ~ r2_hidden(D_106,A_107)
      | ~ v1_relat_1(A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_541,c_141])).

tff(c_28,plain,(
    ! [A_14,C_16,B_15] :
      ( r2_hidden(k2_mcart_1(A_14),C_16)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_910,plain,(
    ! [D_115,A_116] :
      ( r2_hidden(k2_mcart_1(D_115),k2_relat_1(A_116))
      | ~ r2_hidden(D_115,A_116)
      | ~ v1_relat_1(A_116) ) ),
    inference(resolution,[status(thm)],[c_761,c_28])).

tff(c_153,plain,(
    ! [A_44] :
      ( k3_xboole_0(A_44,k2_zfmisc_1(k1_relat_1(A_44),k2_relat_1(A_44))) = A_44
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_138,plain,(
    ! [D_32,A_1,B_2] :
      ( r2_hidden(D_32,A_1)
      | ~ r2_hidden(D_32,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_135])).

tff(c_509,plain,(
    ! [D_71,A_72] :
      ( r2_hidden(D_71,k2_zfmisc_1(k1_relat_1(A_72),k2_relat_1(A_72)))
      | ~ r2_hidden(D_71,A_72)
      | ~ v1_relat_1(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_138])).

tff(c_30,plain,(
    ! [A_14,B_15,C_16] :
      ( r2_hidden(k1_mcart_1(A_14),B_15)
      | ~ r2_hidden(A_14,k2_zfmisc_1(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_521,plain,(
    ! [D_73,A_74] :
      ( r2_hidden(k1_mcart_1(D_73),k1_relat_1(A_74))
      | ~ r2_hidden(D_73,A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(resolution,[status(thm)],[c_509,c_30])).

tff(c_32,plain,
    ( ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3'))
    | ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_142,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_4'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_524,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_521,c_142])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_524])).

tff(c_529,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_4'),k2_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_913,plain,
    ( ~ r2_hidden('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_910,c_529])).

tff(c_917,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_913])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:58:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.48  
% 2.97/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.97/1.49  %$ r2_hidden > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.97/1.49  
% 2.97/1.49  %Foreground sorts:
% 2.97/1.49  
% 2.97/1.49  
% 2.97/1.49  %Background operators:
% 2.97/1.49  
% 2.97/1.49  
% 2.97/1.49  %Foreground operators:
% 2.97/1.49  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.97/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.97/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.97/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.49  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.97/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.97/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.97/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.49  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.97/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.97/1.49  
% 3.10/1.50  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (r2_hidden(B, A) => (r2_hidden(k1_mcart_1(B), k1_relat_1(A)) & r2_hidden(k2_mcart_1(B), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_mcart_1)).
% 3.10/1.50  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 3.10/1.50  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.10/1.50  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.10/1.50  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.10/1.50  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.10/1.50  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.50  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.50  tff(c_541, plain, (![A_84]: (k3_xboole_0(A_84, k2_zfmisc_1(k1_relat_1(A_84), k2_relat_1(A_84)))=A_84 | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.10/1.50  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.10/1.50  tff(c_24, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.10/1.50  tff(c_104, plain, (![D_27, A_28, B_29]: (r2_hidden(D_27, A_28) | ~r2_hidden(D_27, k4_xboole_0(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.50  tff(c_135, plain, (![D_32, A_33, B_34]: (r2_hidden(D_32, A_33) | ~r2_hidden(D_32, k3_xboole_0(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_104])).
% 3.10/1.50  tff(c_141, plain, (![D_32, B_2, A_1]: (r2_hidden(D_32, B_2) | ~r2_hidden(D_32, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 3.10/1.50  tff(c_761, plain, (![D_106, A_107]: (r2_hidden(D_106, k2_zfmisc_1(k1_relat_1(A_107), k2_relat_1(A_107))) | ~r2_hidden(D_106, A_107) | ~v1_relat_1(A_107))), inference(superposition, [status(thm), theory('equality')], [c_541, c_141])).
% 3.10/1.50  tff(c_28, plain, (![A_14, C_16, B_15]: (r2_hidden(k2_mcart_1(A_14), C_16) | ~r2_hidden(A_14, k2_zfmisc_1(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.50  tff(c_910, plain, (![D_115, A_116]: (r2_hidden(k2_mcart_1(D_115), k2_relat_1(A_116)) | ~r2_hidden(D_115, A_116) | ~v1_relat_1(A_116))), inference(resolution, [status(thm)], [c_761, c_28])).
% 3.10/1.50  tff(c_153, plain, (![A_44]: (k3_xboole_0(A_44, k2_zfmisc_1(k1_relat_1(A_44), k2_relat_1(A_44)))=A_44 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.10/1.50  tff(c_138, plain, (![D_32, A_1, B_2]: (r2_hidden(D_32, A_1) | ~r2_hidden(D_32, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_135])).
% 3.10/1.50  tff(c_509, plain, (![D_71, A_72]: (r2_hidden(D_71, k2_zfmisc_1(k1_relat_1(A_72), k2_relat_1(A_72))) | ~r2_hidden(D_71, A_72) | ~v1_relat_1(A_72))), inference(superposition, [status(thm), theory('equality')], [c_153, c_138])).
% 3.10/1.50  tff(c_30, plain, (![A_14, B_15, C_16]: (r2_hidden(k1_mcart_1(A_14), B_15) | ~r2_hidden(A_14, k2_zfmisc_1(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.10/1.50  tff(c_521, plain, (![D_73, A_74]: (r2_hidden(k1_mcart_1(D_73), k1_relat_1(A_74)) | ~r2_hidden(D_73, A_74) | ~v1_relat_1(A_74))), inference(resolution, [status(thm)], [c_509, c_30])).
% 3.10/1.50  tff(c_32, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3')) | ~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.50  tff(c_142, plain, (~r2_hidden(k1_mcart_1('#skF_4'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_32])).
% 3.10/1.50  tff(c_524, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_521, c_142])).
% 3.10/1.50  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_524])).
% 3.10/1.50  tff(c_529, plain, (~r2_hidden(k2_mcart_1('#skF_4'), k2_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_32])).
% 3.10/1.50  tff(c_913, plain, (~r2_hidden('#skF_4', '#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_910, c_529])).
% 3.10/1.50  tff(c_917, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_913])).
% 3.10/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.50  
% 3.10/1.50  Inference rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Ref     : 0
% 3.10/1.50  #Sup     : 216
% 3.10/1.50  #Fact    : 0
% 3.10/1.50  #Define  : 0
% 3.10/1.50  #Split   : 1
% 3.10/1.50  #Chain   : 0
% 3.10/1.50  #Close   : 0
% 3.10/1.50  
% 3.10/1.50  Ordering : KBO
% 3.10/1.50  
% 3.10/1.50  Simplification rules
% 3.10/1.50  ----------------------
% 3.10/1.50  #Subsume      : 16
% 3.10/1.50  #Demod        : 22
% 3.10/1.50  #Tautology    : 62
% 3.10/1.50  #SimpNegUnit  : 0
% 3.10/1.50  #BackRed      : 0
% 3.10/1.50  
% 3.10/1.50  #Partial instantiations: 0
% 3.10/1.50  #Strategies tried      : 1
% 3.10/1.50  
% 3.10/1.50  Timing (in seconds)
% 3.10/1.50  ----------------------
% 3.10/1.50  Preprocessing        : 0.30
% 3.10/1.50  Parsing              : 0.16
% 3.10/1.50  CNF conversion       : 0.02
% 3.10/1.50  Main loop            : 0.43
% 3.10/1.50  Inferencing          : 0.16
% 3.10/1.50  Reduction            : 0.13
% 3.10/1.50  Demodulation         : 0.10
% 3.10/1.50  BG Simplification    : 0.02
% 3.10/1.50  Subsumption          : 0.08
% 3.10/1.50  Abstraction          : 0.02
% 3.10/1.50  MUC search           : 0.00
% 3.10/1.50  Cooper               : 0.00
% 3.10/1.50  Total                : 0.76
% 3.10/1.50  Index Insertion      : 0.00
% 3.10/1.50  Index Deletion       : 0.00
% 3.10/1.50  Index Matching       : 0.00
% 3.10/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
