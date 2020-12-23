%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:41 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   59 (  70 expanded)
%              Number of leaves         :   34 (  41 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  84 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_67,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_77,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_48,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_32,plain,(
    ! [A_39] : k2_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_139,plain,(
    ! [A_73,B_74] :
      ( k5_relat_1(k6_relat_1(A_73),B_74) = k7_relat_1(B_74,A_73)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_40,plain,(
    ! [B_44,A_43] : k5_relat_1(k6_relat_1(B_44),k6_relat_1(A_43)) = k6_relat_1(k3_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_146,plain,(
    ! [A_43,A_73] :
      ( k7_relat_1(k6_relat_1(A_43),A_73) = k6_relat_1(k3_xboole_0(A_43,A_73))
      | ~ v1_relat_1(k6_relat_1(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_40])).

tff(c_155,plain,(
    ! [A_43,A_73] : k7_relat_1(k6_relat_1(A_43),A_73) = k6_relat_1(k3_xboole_0(A_43,A_73)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_146])).

tff(c_30,plain,(
    ! [A_39] : k1_relat_1(k6_relat_1(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_102,plain,(
    ! [B_62,A_63] :
      ( v4_relat_1(B_62,A_63)
      | ~ r1_tarski(k1_relat_1(B_62),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_105,plain,(
    ! [A_39,A_63] :
      ( v4_relat_1(k6_relat_1(A_39),A_63)
      | ~ r1_tarski(A_39,A_63)
      | ~ v1_relat_1(k6_relat_1(A_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_102])).

tff(c_111,plain,(
    ! [A_39,A_63] :
      ( v4_relat_1(k6_relat_1(A_39),A_63)
      | ~ r1_tarski(A_39,A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_105])).

tff(c_230,plain,(
    ! [B_86,A_87] :
      ( k7_relat_1(B_86,A_87) = B_86
      | ~ v4_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_233,plain,(
    ! [A_39,A_63] :
      ( k7_relat_1(k6_relat_1(A_39),A_63) = k6_relat_1(A_39)
      | ~ v1_relat_1(k6_relat_1(A_39))
      | ~ r1_tarski(A_39,A_63) ) ),
    inference(resolution,[status(thm)],[c_111,c_230])).

tff(c_423,plain,(
    ! [A_103,A_104] :
      ( k6_relat_1(k3_xboole_0(A_103,A_104)) = k6_relat_1(A_103)
      | ~ r1_tarski(A_103,A_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_155,c_233])).

tff(c_456,plain,(
    ! [A_103,A_104] :
      ( k3_xboole_0(A_103,A_104) = k2_relat_1(k6_relat_1(A_103))
      | ~ r1_tarski(A_103,A_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_32])).

tff(c_482,plain,(
    ! [A_105,A_106] :
      ( k3_xboole_0(A_105,A_106) = A_105
      | ~ r1_tarski(A_105,A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_456])).

tff(c_499,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_482])).

tff(c_42,plain,(
    ! [C_47,A_45,B_46] :
      ( k2_wellord1(k2_wellord1(C_47,A_45),B_46) = k2_wellord1(C_47,k3_xboole_0(A_45,B_46))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_744,plain,(
    ! [C_119,B_120,A_121] :
      ( k2_wellord1(k2_wellord1(C_119,B_120),A_121) = k2_wellord1(k2_wellord1(C_119,A_121),B_120)
      | ~ v1_relat_1(C_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_46,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_783,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_744,c_46])).

tff(c_828,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_783])).

tff(c_837,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_828])).

tff(c_840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_499,c_837])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:24:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  
% 2.79/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.42  %$ v4_relat_1 > r1_tarski > v1_relat_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.79/1.42  
% 2.79/1.42  %Foreground sorts:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Background operators:
% 2.79/1.42  
% 2.79/1.42  
% 2.79/1.42  %Foreground operators:
% 2.79/1.42  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.42  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.42  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.79/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.79/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.79/1.42  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.79/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.79/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.42  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.79/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.42  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.79/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.79/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.42  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.79/1.42  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.42  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.79/1.42  
% 2.79/1.43  tff(f_92, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 2.79/1.43  tff(f_67, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.79/1.43  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.79/1.43  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.79/1.43  tff(f_77, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.79/1.43  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 2.79/1.43  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.79/1.43  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 2.79/1.43  tff(f_85, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 2.79/1.43  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.43  tff(c_48, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.43  tff(c_32, plain, (![A_39]: (k2_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.43  tff(c_36, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.79/1.43  tff(c_139, plain, (![A_73, B_74]: (k5_relat_1(k6_relat_1(A_73), B_74)=k7_relat_1(B_74, A_73) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.43  tff(c_40, plain, (![B_44, A_43]: (k5_relat_1(k6_relat_1(B_44), k6_relat_1(A_43))=k6_relat_1(k3_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.79/1.43  tff(c_146, plain, (![A_43, A_73]: (k7_relat_1(k6_relat_1(A_43), A_73)=k6_relat_1(k3_xboole_0(A_43, A_73)) | ~v1_relat_1(k6_relat_1(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_40])).
% 2.79/1.43  tff(c_155, plain, (![A_43, A_73]: (k7_relat_1(k6_relat_1(A_43), A_73)=k6_relat_1(k3_xboole_0(A_43, A_73)))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_146])).
% 2.79/1.43  tff(c_30, plain, (![A_39]: (k1_relat_1(k6_relat_1(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.79/1.43  tff(c_102, plain, (![B_62, A_63]: (v4_relat_1(B_62, A_63) | ~r1_tarski(k1_relat_1(B_62), A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.79/1.43  tff(c_105, plain, (![A_39, A_63]: (v4_relat_1(k6_relat_1(A_39), A_63) | ~r1_tarski(A_39, A_63) | ~v1_relat_1(k6_relat_1(A_39)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_102])).
% 2.79/1.43  tff(c_111, plain, (![A_39, A_63]: (v4_relat_1(k6_relat_1(A_39), A_63) | ~r1_tarski(A_39, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_105])).
% 2.79/1.43  tff(c_230, plain, (![B_86, A_87]: (k7_relat_1(B_86, A_87)=B_86 | ~v4_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.79/1.43  tff(c_233, plain, (![A_39, A_63]: (k7_relat_1(k6_relat_1(A_39), A_63)=k6_relat_1(A_39) | ~v1_relat_1(k6_relat_1(A_39)) | ~r1_tarski(A_39, A_63))), inference(resolution, [status(thm)], [c_111, c_230])).
% 2.79/1.43  tff(c_423, plain, (![A_103, A_104]: (k6_relat_1(k3_xboole_0(A_103, A_104))=k6_relat_1(A_103) | ~r1_tarski(A_103, A_104))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_155, c_233])).
% 2.79/1.43  tff(c_456, plain, (![A_103, A_104]: (k3_xboole_0(A_103, A_104)=k2_relat_1(k6_relat_1(A_103)) | ~r1_tarski(A_103, A_104))), inference(superposition, [status(thm), theory('equality')], [c_423, c_32])).
% 2.79/1.43  tff(c_482, plain, (![A_105, A_106]: (k3_xboole_0(A_105, A_106)=A_105 | ~r1_tarski(A_105, A_106))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_456])).
% 2.79/1.43  tff(c_499, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_48, c_482])).
% 2.79/1.43  tff(c_42, plain, (![C_47, A_45, B_46]: (k2_wellord1(k2_wellord1(C_47, A_45), B_46)=k2_wellord1(C_47, k3_xboole_0(A_45, B_46)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.79/1.43  tff(c_744, plain, (![C_119, B_120, A_121]: (k2_wellord1(k2_wellord1(C_119, B_120), A_121)=k2_wellord1(k2_wellord1(C_119, A_121), B_120) | ~v1_relat_1(C_119))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.79/1.43  tff(c_46, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.79/1.43  tff(c_783, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_744, c_46])).
% 2.79/1.43  tff(c_828, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_783])).
% 2.79/1.43  tff(c_837, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_42, c_828])).
% 2.79/1.43  tff(c_840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_499, c_837])).
% 2.79/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.43  
% 2.79/1.43  Inference rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Ref     : 0
% 2.79/1.43  #Sup     : 183
% 2.79/1.43  #Fact    : 0
% 2.79/1.43  #Define  : 0
% 2.79/1.43  #Split   : 1
% 2.79/1.43  #Chain   : 0
% 2.79/1.43  #Close   : 0
% 2.79/1.43  
% 2.79/1.43  Ordering : KBO
% 2.79/1.43  
% 2.79/1.43  Simplification rules
% 2.79/1.43  ----------------------
% 2.79/1.43  #Subsume      : 22
% 2.79/1.43  #Demod        : 96
% 2.79/1.43  #Tautology    : 80
% 2.79/1.43  #SimpNegUnit  : 0
% 2.79/1.43  #BackRed      : 0
% 2.79/1.43  
% 2.79/1.43  #Partial instantiations: 0
% 2.79/1.43  #Strategies tried      : 1
% 2.79/1.43  
% 2.79/1.43  Timing (in seconds)
% 2.79/1.43  ----------------------
% 2.79/1.43  Preprocessing        : 0.33
% 2.79/1.43  Parsing              : 0.18
% 2.79/1.43  CNF conversion       : 0.02
% 2.79/1.43  Main loop            : 0.32
% 2.79/1.44  Inferencing          : 0.12
% 2.79/1.44  Reduction            : 0.10
% 2.79/1.44  Demodulation         : 0.07
% 2.79/1.44  BG Simplification    : 0.02
% 2.79/1.44  Subsumption          : 0.07
% 2.79/1.44  Abstraction          : 0.02
% 2.79/1.44  MUC search           : 0.00
% 2.79/1.44  Cooper               : 0.00
% 2.79/1.44  Total                : 0.68
% 2.79/1.44  Index Insertion      : 0.00
% 2.79/1.44  Index Deletion       : 0.00
% 2.79/1.44  Index Matching       : 0.00
% 2.79/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
