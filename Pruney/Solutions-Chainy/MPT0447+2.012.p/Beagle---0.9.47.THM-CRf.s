%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:29 EST 2020

% Result     : Theorem 2.89s
% Output     : CNFRefutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  93 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   79 ( 164 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_98,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( r1_tarski(A,B)
             => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_46,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_50,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_48,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_46,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_36,plain,(
    ! [A_41,B_43] :
      ( r1_tarski(k2_relat_1(A_41),k2_relat_1(B_43))
      | ~ r1_tarski(A_41,B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_208,plain,(
    ! [A_75] :
      ( k2_xboole_0(k1_relat_1(A_75),k2_relat_1(A_75)) = k3_relat_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,k2_xboole_0(C_8,B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_217,plain,(
    ! [A_6,A_75] :
      ( r1_tarski(A_6,k3_relat_1(A_75))
      | ~ r1_tarski(A_6,k2_relat_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_8])).

tff(c_38,plain,(
    ! [A_41,B_43] :
      ( r1_tarski(k1_relat_1(A_41),k1_relat_1(B_43))
      | ~ r1_tarski(A_41,B_43)
      | ~ v1_relat_1(B_43)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_12,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_105,plain,(
    ! [B_56,A_57] : k3_tarski(k2_tarski(B_56,A_57)) = k2_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_85])).

tff(c_14,plain,(
    ! [A_14,B_15] : k3_tarski(k2_tarski(A_14,B_15)) = k2_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_111,plain,(
    ! [B_56,A_57] : k2_xboole_0(B_56,A_57) = k2_xboole_0(A_57,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_170,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,k2_xboole_0(C_66,B_67))
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_176,plain,(
    ! [A_65,A_57,B_56] :
      ( r1_tarski(A_65,k2_xboole_0(A_57,B_56))
      | ~ r1_tarski(A_65,A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_170])).

tff(c_214,plain,(
    ! [A_65,A_75] :
      ( r1_tarski(A_65,k3_relat_1(A_75))
      | ~ r1_tarski(A_65,k1_relat_1(A_75))
      | ~ v1_relat_1(A_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_176])).

tff(c_34,plain,(
    ! [A_40] :
      ( k2_xboole_0(k1_relat_1(A_40),k2_relat_1(A_40)) = k3_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_242,plain,(
    ! [A_88,C_89,B_90] :
      ( r1_tarski(k2_xboole_0(A_88,C_89),B_90)
      | ~ r1_tarski(C_89,B_90)
      | ~ r1_tarski(A_88,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_818,plain,(
    ! [A_190,B_191] :
      ( r1_tarski(k3_relat_1(A_190),B_191)
      | ~ r1_tarski(k2_relat_1(A_190),B_191)
      | ~ r1_tarski(k1_relat_1(A_190),B_191)
      | ~ v1_relat_1(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_242])).

tff(c_44,plain,(
    ~ r1_tarski(k3_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_871,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_818,c_44])).

tff(c_895,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7'))
    | ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_871])).

tff(c_896,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_895])).

tff(c_899,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_214,c_896])).

tff(c_905,plain,(
    ~ r1_tarski(k1_relat_1('#skF_6'),k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_899])).

tff(c_911,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_38,c_905])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_911])).

tff(c_916,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k3_relat_1('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_895])).

tff(c_923,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_217,c_916])).

tff(c_929,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),k2_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_923])).

tff(c_948,plain,
    ( ~ r1_tarski('#skF_6','#skF_7')
    | ~ v1_relat_1('#skF_7')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_36,c_929])).

tff(c_952,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_46,c_948])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.89/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.19/1.47  
% 3.19/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.47  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_2 > #skF_1 > #skF_4
% 3.20/1.47  
% 3.20/1.47  %Foreground sorts:
% 3.20/1.47  
% 3.20/1.47  
% 3.20/1.47  %Background operators:
% 3.20/1.47  
% 3.20/1.47  
% 3.20/1.47  %Foreground operators:
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.20/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.20/1.47  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.20/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.20/1.47  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.20/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.20/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.20/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.20/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.20/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.20/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.47  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.20/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.20/1.47  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.20/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.47  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.20/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.47  
% 3.20/1.48  tff(f_98, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 3.20/1.48  tff(f_80, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 3.20/1.48  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 3.20/1.48  tff(f_36, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.20/1.48  tff(f_44, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.20/1.48  tff(f_46, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.20/1.48  tff(f_42, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.20/1.48  tff(c_50, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.48  tff(c_48, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.48  tff(c_46, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.48  tff(c_36, plain, (![A_41, B_43]: (r1_tarski(k2_relat_1(A_41), k2_relat_1(B_43)) | ~r1_tarski(A_41, B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.48  tff(c_208, plain, (![A_75]: (k2_xboole_0(k1_relat_1(A_75), k2_relat_1(A_75))=k3_relat_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.48  tff(c_8, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, k2_xboole_0(C_8, B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.20/1.48  tff(c_217, plain, (![A_6, A_75]: (r1_tarski(A_6, k3_relat_1(A_75)) | ~r1_tarski(A_6, k2_relat_1(A_75)) | ~v1_relat_1(A_75))), inference(superposition, [status(thm), theory('equality')], [c_208, c_8])).
% 3.20/1.48  tff(c_38, plain, (![A_41, B_43]: (r1_tarski(k1_relat_1(A_41), k1_relat_1(B_43)) | ~r1_tarski(A_41, B_43) | ~v1_relat_1(B_43) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.20/1.48  tff(c_12, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.20/1.48  tff(c_85, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.48  tff(c_105, plain, (![B_56, A_57]: (k3_tarski(k2_tarski(B_56, A_57))=k2_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_12, c_85])).
% 3.20/1.48  tff(c_14, plain, (![A_14, B_15]: (k3_tarski(k2_tarski(A_14, B_15))=k2_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.20/1.48  tff(c_111, plain, (![B_56, A_57]: (k2_xboole_0(B_56, A_57)=k2_xboole_0(A_57, B_56))), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 3.20/1.48  tff(c_170, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, k2_xboole_0(C_66, B_67)) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.20/1.48  tff(c_176, plain, (![A_65, A_57, B_56]: (r1_tarski(A_65, k2_xboole_0(A_57, B_56)) | ~r1_tarski(A_65, A_57))), inference(superposition, [status(thm), theory('equality')], [c_111, c_170])).
% 3.20/1.48  tff(c_214, plain, (![A_65, A_75]: (r1_tarski(A_65, k3_relat_1(A_75)) | ~r1_tarski(A_65, k1_relat_1(A_75)) | ~v1_relat_1(A_75))), inference(superposition, [status(thm), theory('equality')], [c_208, c_176])).
% 3.20/1.48  tff(c_34, plain, (![A_40]: (k2_xboole_0(k1_relat_1(A_40), k2_relat_1(A_40))=k3_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.20/1.48  tff(c_242, plain, (![A_88, C_89, B_90]: (r1_tarski(k2_xboole_0(A_88, C_89), B_90) | ~r1_tarski(C_89, B_90) | ~r1_tarski(A_88, B_90))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.20/1.48  tff(c_818, plain, (![A_190, B_191]: (r1_tarski(k3_relat_1(A_190), B_191) | ~r1_tarski(k2_relat_1(A_190), B_191) | ~r1_tarski(k1_relat_1(A_190), B_191) | ~v1_relat_1(A_190))), inference(superposition, [status(thm), theory('equality')], [c_34, c_242])).
% 3.20/1.48  tff(c_44, plain, (~r1_tarski(k3_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.20/1.48  tff(c_871, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_818, c_44])).
% 3.20/1.48  tff(c_895, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7')) | ~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_871])).
% 3.20/1.48  tff(c_896, plain, (~r1_tarski(k1_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(splitLeft, [status(thm)], [c_895])).
% 3.20/1.48  tff(c_899, plain, (~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_214, c_896])).
% 3.20/1.48  tff(c_905, plain, (~r1_tarski(k1_relat_1('#skF_6'), k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_899])).
% 3.20/1.48  tff(c_911, plain, (~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_38, c_905])).
% 3.20/1.48  tff(c_915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_911])).
% 3.20/1.48  tff(c_916, plain, (~r1_tarski(k2_relat_1('#skF_6'), k3_relat_1('#skF_7'))), inference(splitRight, [status(thm)], [c_895])).
% 3.20/1.48  tff(c_923, plain, (~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_217, c_916])).
% 3.20/1.48  tff(c_929, plain, (~r1_tarski(k2_relat_1('#skF_6'), k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_923])).
% 3.20/1.48  tff(c_948, plain, (~r1_tarski('#skF_6', '#skF_7') | ~v1_relat_1('#skF_7') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_36, c_929])).
% 3.20/1.48  tff(c_952, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_46, c_948])).
% 3.20/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.20/1.48  
% 3.20/1.48  Inference rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Ref     : 0
% 3.20/1.48  #Sup     : 227
% 3.20/1.48  #Fact    : 0
% 3.20/1.48  #Define  : 0
% 3.20/1.48  #Split   : 3
% 3.20/1.48  #Chain   : 0
% 3.20/1.48  #Close   : 0
% 3.20/1.48  
% 3.20/1.48  Ordering : KBO
% 3.20/1.48  
% 3.20/1.48  Simplification rules
% 3.20/1.48  ----------------------
% 3.20/1.48  #Subsume      : 71
% 3.20/1.48  #Demod        : 28
% 3.20/1.48  #Tautology    : 36
% 3.20/1.48  #SimpNegUnit  : 1
% 3.20/1.48  #BackRed      : 1
% 3.20/1.48  
% 3.20/1.48  #Partial instantiations: 0
% 3.20/1.48  #Strategies tried      : 1
% 3.20/1.48  
% 3.20/1.48  Timing (in seconds)
% 3.20/1.48  ----------------------
% 3.20/1.48  Preprocessing        : 0.30
% 3.20/1.48  Parsing              : 0.16
% 3.20/1.48  CNF conversion       : 0.02
% 3.20/1.48  Main loop            : 0.42
% 3.20/1.48  Inferencing          : 0.15
% 3.20/1.48  Reduction            : 0.12
% 3.20/1.48  Demodulation         : 0.08
% 3.20/1.48  BG Simplification    : 0.02
% 3.20/1.48  Subsumption          : 0.11
% 3.20/1.48  Abstraction          : 0.02
% 3.20/1.49  MUC search           : 0.00
% 3.20/1.49  Cooper               : 0.00
% 3.20/1.49  Total                : 0.75
% 3.20/1.49  Index Insertion      : 0.00
% 3.20/1.49  Index Deletion       : 0.00
% 3.20/1.49  Index Matching       : 0.00
% 3.20/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
