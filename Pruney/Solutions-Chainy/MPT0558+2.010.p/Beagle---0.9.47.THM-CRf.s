%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:08 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 (  82 expanded)
%              Number of equality atoms :   20 (  22 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_69,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k7_relat_1(k5_relat_1(B,C),A) = k5_relat_1(k7_relat_1(B,A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_relat_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( v1_relat_1(k5_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_7] :
      ( k9_relat_1(A_7,k1_relat_1(A_7)) = k2_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_52,plain,(
    ! [B_24,A_25] :
      ( k3_xboole_0(B_24,k2_zfmisc_1(A_25,k2_relat_1(B_24))) = k7_relat_1(B_24,A_25)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_14] :
      ( k3_xboole_0(A_14,k2_zfmisc_1(k1_relat_1(A_14),k2_relat_1(A_14))) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_59,plain,(
    ! [B_24] :
      ( k7_relat_1(B_24,k1_relat_1(B_24)) = B_24
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_12])).

tff(c_100,plain,(
    ! [B_30,C_31,A_32] :
      ( k7_relat_1(k5_relat_1(B_30,C_31),A_32) = k5_relat_1(k7_relat_1(B_30,A_32),C_31)
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_120,plain,(
    ! [B_33,A_34,C_35] :
      ( k2_relat_1(k5_relat_1(k7_relat_1(B_33,A_34),C_35)) = k9_relat_1(k5_relat_1(B_33,C_35),A_34)
      | ~ v1_relat_1(k5_relat_1(B_33,C_35))
      | ~ v1_relat_1(C_35)
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_8])).

tff(c_223,plain,(
    ! [B_43,C_44] :
      ( k9_relat_1(k5_relat_1(B_43,C_44),k1_relat_1(B_43)) = k2_relat_1(k5_relat_1(B_43,C_44))
      | ~ v1_relat_1(k5_relat_1(B_43,C_44))
      | ~ v1_relat_1(C_44)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_120])).

tff(c_10,plain,(
    ! [B_11,C_13,A_10] :
      ( k9_relat_1(k5_relat_1(B_11,C_13),A_10) = k9_relat_1(C_13,k9_relat_1(B_11,A_10))
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_392,plain,(
    ! [C_55,B_56] :
      ( k9_relat_1(C_55,k9_relat_1(B_56,k1_relat_1(B_56))) = k2_relat_1(k5_relat_1(B_56,C_55))
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k5_relat_1(B_56,C_55))
      | ~ v1_relat_1(C_55)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_10])).

tff(c_492,plain,(
    ! [C_59,A_60] :
      ( k9_relat_1(C_59,k2_relat_1(A_60)) = k2_relat_1(k5_relat_1(A_60,C_59))
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(A_60)
      | ~ v1_relat_1(k5_relat_1(A_60,C_59))
      | ~ v1_relat_1(C_59)
      | ~ v1_relat_1(A_60)
      | ~ v1_relat_1(A_60)
      | ~ v1_relat_1(A_60)
      | ~ v1_relat_1(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_392])).

tff(c_500,plain,(
    ! [B_61,A_62] :
      ( k9_relat_1(B_61,k2_relat_1(A_62)) = k2_relat_1(k5_relat_1(A_62,B_61))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(A_62) ) ),
    inference(resolution,[status(thm)],[c_2,c_492])).

tff(c_16,plain,(
    k9_relat_1('#skF_2',k2_relat_1('#skF_1')) != k2_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_516,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_500,c_16])).

tff(c_534,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_516])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 11:32:34 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.35  
% 2.68/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.35  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.68/1.35  
% 2.68/1.35  %Foreground sorts:
% 2.68/1.35  
% 2.68/1.35  
% 2.68/1.35  %Background operators:
% 2.68/1.35  
% 2.68/1.35  
% 2.68/1.35  %Foreground operators:
% 2.68/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.68/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.68/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.68/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.68/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.68/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.68/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.68/1.35  
% 2.68/1.36  tff(f_69, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.68/1.36  tff(f_31, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.68/1.36  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.68/1.36  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 2.68/1.36  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 2.68/1.36  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k7_relat_1(k5_relat_1(B, C), A) = k5_relat_1(k7_relat_1(B, A), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_relat_1)).
% 2.68/1.36  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.68/1.36  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.68/1.36  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.36  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.36  tff(c_2, plain, (![A_1, B_2]: (v1_relat_1(k5_relat_1(A_1, B_2)) | ~v1_relat_1(B_2) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.68/1.36  tff(c_6, plain, (![A_7]: (k9_relat_1(A_7, k1_relat_1(A_7))=k2_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.68/1.36  tff(c_52, plain, (![B_24, A_25]: (k3_xboole_0(B_24, k2_zfmisc_1(A_25, k2_relat_1(B_24)))=k7_relat_1(B_24, A_25) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.36  tff(c_12, plain, (![A_14]: (k3_xboole_0(A_14, k2_zfmisc_1(k1_relat_1(A_14), k2_relat_1(A_14)))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.68/1.36  tff(c_59, plain, (![B_24]: (k7_relat_1(B_24, k1_relat_1(B_24))=B_24 | ~v1_relat_1(B_24) | ~v1_relat_1(B_24))), inference(superposition, [status(thm), theory('equality')], [c_52, c_12])).
% 2.68/1.36  tff(c_100, plain, (![B_30, C_31, A_32]: (k7_relat_1(k5_relat_1(B_30, C_31), A_32)=k5_relat_1(k7_relat_1(B_30, A_32), C_31) | ~v1_relat_1(C_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.68/1.36  tff(c_8, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.68/1.36  tff(c_120, plain, (![B_33, A_34, C_35]: (k2_relat_1(k5_relat_1(k7_relat_1(B_33, A_34), C_35))=k9_relat_1(k5_relat_1(B_33, C_35), A_34) | ~v1_relat_1(k5_relat_1(B_33, C_35)) | ~v1_relat_1(C_35) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_100, c_8])).
% 2.68/1.36  tff(c_223, plain, (![B_43, C_44]: (k9_relat_1(k5_relat_1(B_43, C_44), k1_relat_1(B_43))=k2_relat_1(k5_relat_1(B_43, C_44)) | ~v1_relat_1(k5_relat_1(B_43, C_44)) | ~v1_relat_1(C_44) | ~v1_relat_1(B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(B_43))), inference(superposition, [status(thm), theory('equality')], [c_59, c_120])).
% 2.68/1.36  tff(c_10, plain, (![B_11, C_13, A_10]: (k9_relat_1(k5_relat_1(B_11, C_13), A_10)=k9_relat_1(C_13, k9_relat_1(B_11, A_10)) | ~v1_relat_1(C_13) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.68/1.36  tff(c_392, plain, (![C_55, B_56]: (k9_relat_1(C_55, k9_relat_1(B_56, k1_relat_1(B_56)))=k2_relat_1(k5_relat_1(B_56, C_55)) | ~v1_relat_1(C_55) | ~v1_relat_1(B_56) | ~v1_relat_1(k5_relat_1(B_56, C_55)) | ~v1_relat_1(C_55) | ~v1_relat_1(B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_223, c_10])).
% 2.68/1.36  tff(c_492, plain, (![C_59, A_60]: (k9_relat_1(C_59, k2_relat_1(A_60))=k2_relat_1(k5_relat_1(A_60, C_59)) | ~v1_relat_1(C_59) | ~v1_relat_1(A_60) | ~v1_relat_1(k5_relat_1(A_60, C_59)) | ~v1_relat_1(C_59) | ~v1_relat_1(A_60) | ~v1_relat_1(A_60) | ~v1_relat_1(A_60) | ~v1_relat_1(A_60))), inference(superposition, [status(thm), theory('equality')], [c_6, c_392])).
% 2.68/1.36  tff(c_500, plain, (![B_61, A_62]: (k9_relat_1(B_61, k2_relat_1(A_62))=k2_relat_1(k5_relat_1(A_62, B_61)) | ~v1_relat_1(B_61) | ~v1_relat_1(A_62))), inference(resolution, [status(thm)], [c_2, c_492])).
% 2.68/1.36  tff(c_16, plain, (k9_relat_1('#skF_2', k2_relat_1('#skF_1'))!=k2_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.36  tff(c_516, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_500, c_16])).
% 2.68/1.36  tff(c_534, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_516])).
% 2.68/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.36  
% 2.68/1.36  Inference rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Ref     : 0
% 2.68/1.36  #Sup     : 138
% 2.68/1.36  #Fact    : 0
% 2.68/1.36  #Define  : 0
% 2.68/1.36  #Split   : 0
% 2.68/1.36  #Chain   : 0
% 2.68/1.36  #Close   : 0
% 2.68/1.36  
% 2.68/1.36  Ordering : KBO
% 2.68/1.36  
% 2.68/1.36  Simplification rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Subsume      : 14
% 2.68/1.36  #Demod        : 2
% 2.68/1.36  #Tautology    : 39
% 2.68/1.36  #SimpNegUnit  : 0
% 2.68/1.36  #BackRed      : 0
% 2.68/1.36  
% 2.68/1.36  #Partial instantiations: 0
% 2.68/1.36  #Strategies tried      : 1
% 2.68/1.36  
% 2.68/1.36  Timing (in seconds)
% 2.68/1.36  ----------------------
% 2.68/1.36  Preprocessing        : 0.29
% 2.68/1.36  Parsing              : 0.16
% 2.68/1.36  CNF conversion       : 0.02
% 2.68/1.36  Main loop            : 0.33
% 2.68/1.36  Inferencing          : 0.15
% 2.68/1.36  Reduction            : 0.09
% 2.68/1.36  Demodulation         : 0.06
% 2.68/1.36  BG Simplification    : 0.03
% 2.68/1.36  Subsumption          : 0.06
% 2.68/1.36  Abstraction          : 0.02
% 2.68/1.36  MUC search           : 0.00
% 2.68/1.36  Cooper               : 0.00
% 2.68/1.36  Total                : 0.65
% 2.68/1.36  Index Insertion      : 0.00
% 2.68/1.36  Index Deletion       : 0.00
% 2.68/1.36  Index Matching       : 0.00
% 2.68/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
