%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:39 EST 2020

% Result     : Theorem 30.18s
% Output     : CNFRefutation 30.18s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 131 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_74,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( B = k1_wellord2(A)
      <=> ( k3_relat_1(B) = A
          & ! [C,D] :
              ( ( r2_hidden(C,A)
                & r2_hidden(D,A) )
             => ( r2_hidden(k4_tarski(C,D),B)
              <=> r1_tarski(C,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_40,plain,(
    ! [A_24] : v1_relat_1(k1_wellord2(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ! [A_16] :
      ( k3_relat_1(k1_wellord2(A_16)) = A_16
      | ~ v1_relat_1(k1_wellord2(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_16] : k3_relat_1(k1_wellord2(A_16)) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34])).

tff(c_76,plain,(
    ! [A_35] :
      ( k2_xboole_0(k1_relat_1(A_35),k2_relat_1(A_35)) = k3_relat_1(A_35)
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_91,plain,(
    ! [A_36] :
      ( r1_tarski(k1_relat_1(A_36),k3_relat_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_12])).

tff(c_96,plain,(
    ! [A_16] :
      ( r1_tarski(k1_relat_1(k1_wellord2(A_16)),A_16)
      | ~ v1_relat_1(k1_wellord2(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_91])).

tff(c_99,plain,(
    ! [A_16] : r1_tarski(k1_relat_1(k1_wellord2(A_16)),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_96])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_202,plain,(
    ! [A_58,A_59] :
      ( r1_tarski(A_58,k3_relat_1(A_59))
      | ~ r1_tarski(A_58,k2_relat_1(A_59))
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_8])).

tff(c_213,plain,(
    ! [A_58,A_16] :
      ( r1_tarski(A_58,A_16)
      | ~ r1_tarski(A_58,k2_relat_1(k1_wellord2(A_16)))
      | ~ v1_relat_1(k1_wellord2(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_202])).

tff(c_219,plain,(
    ! [A_60,A_61] :
      ( r1_tarski(A_60,A_61)
      | ~ r1_tarski(A_60,k2_relat_1(k1_wellord2(A_61))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_213])).

tff(c_239,plain,(
    ! [A_61] : r1_tarski(k2_relat_1(k1_wellord2(A_61)),A_61) ),
    inference(resolution,[status(thm)],[c_6,c_219])).

tff(c_20,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_161,plain,(
    ! [C_48,A_49,B_50] :
      ( r1_tarski(k2_zfmisc_1(C_48,A_49),k2_zfmisc_1(C_48,B_50))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1964,plain,(
    ! [A_202,C_203,B_204,A_205] :
      ( r1_tarski(A_202,k2_zfmisc_1(C_203,B_204))
      | ~ r1_tarski(A_202,k2_zfmisc_1(C_203,A_205))
      | ~ r1_tarski(A_205,B_204) ) ),
    inference(resolution,[status(thm)],[c_161,c_10])).

tff(c_3939,plain,(
    ! [A_275,B_276] :
      ( r1_tarski(A_275,k2_zfmisc_1(k1_relat_1(A_275),B_276))
      | ~ r1_tarski(k2_relat_1(A_275),B_276)
      | ~ v1_relat_1(A_275) ) ),
    inference(resolution,[status(thm)],[c_20,c_1964])).

tff(c_166,plain,(
    ! [A_6,C_48,B_50,A_49] :
      ( r1_tarski(A_6,k2_zfmisc_1(C_48,B_50))
      | ~ r1_tarski(A_6,k2_zfmisc_1(C_48,A_49))
      | ~ r1_tarski(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_161,c_10])).

tff(c_55066,plain,(
    ! [A_1479,B_1480,B_1481] :
      ( r1_tarski(A_1479,k2_zfmisc_1(k1_relat_1(A_1479),B_1480))
      | ~ r1_tarski(B_1481,B_1480)
      | ~ r1_tarski(k2_relat_1(A_1479),B_1481)
      | ~ v1_relat_1(A_1479) ) ),
    inference(resolution,[status(thm)],[c_3939,c_166])).

tff(c_66058,plain,(
    ! [A_1666,A_1667] :
      ( r1_tarski(A_1666,k2_zfmisc_1(k1_relat_1(A_1666),A_1667))
      | ~ r1_tarski(k2_relat_1(A_1666),k2_relat_1(k1_wellord2(A_1667)))
      | ~ v1_relat_1(A_1666) ) ),
    inference(resolution,[status(thm)],[c_239,c_55066])).

tff(c_66172,plain,(
    ! [A_1667] :
      ( r1_tarski(k1_wellord2(A_1667),k2_zfmisc_1(k1_relat_1(k1_wellord2(A_1667)),A_1667))
      | ~ v1_relat_1(k1_wellord2(A_1667)) ) ),
    inference(resolution,[status(thm)],[c_6,c_66058])).

tff(c_66620,plain,(
    ! [A_1672] : r1_tarski(k1_wellord2(A_1672),k2_zfmisc_1(k1_relat_1(k1_wellord2(A_1672)),A_1672)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_66172])).

tff(c_195,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(k2_zfmisc_1(A_55,C_56),k2_zfmisc_1(B_57,C_56))
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_200,plain,(
    ! [A_6,B_57,C_56,A_55] :
      ( r1_tarski(A_6,k2_zfmisc_1(B_57,C_56))
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_55,C_56))
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(resolution,[status(thm)],[c_195,c_10])).

tff(c_66760,plain,(
    ! [A_1675,B_1676] :
      ( r1_tarski(k1_wellord2(A_1675),k2_zfmisc_1(B_1676,A_1675))
      | ~ r1_tarski(k1_relat_1(k1_wellord2(A_1675)),B_1676) ) ),
    inference(resolution,[status(thm)],[c_66620,c_200])).

tff(c_67609,plain,(
    ! [A_16] : r1_tarski(k1_wellord2(A_16),k2_zfmisc_1(A_16,A_16)) ),
    inference(resolution,[status(thm)],[c_99,c_66760])).

tff(c_42,plain,(
    ~ r1_tarski(k1_wellord2('#skF_3'),k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_67700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67609,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 30.18/21.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.18/21.56  
% 30.18/21.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.18/21.56  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k3_relat_1 > k2_relat_1 > k1_wellord2 > k1_relat_1 > #skF_3 > #skF_2 > #skF_1
% 30.18/21.56  
% 30.18/21.56  %Foreground sorts:
% 30.18/21.56  
% 30.18/21.56  
% 30.18/21.56  %Background operators:
% 30.18/21.56  
% 30.18/21.56  
% 30.18/21.56  %Foreground operators:
% 30.18/21.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.18/21.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.18/21.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 30.18/21.56  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 30.18/21.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 30.18/21.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 30.18/21.56  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 30.18/21.56  tff('#skF_3', type, '#skF_3': $i).
% 30.18/21.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.18/21.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 30.18/21.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 30.18/21.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.18/21.56  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 30.18/21.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 30.18/21.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 30.18/21.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 30.18/21.56  
% 30.18/21.59  tff(f_74, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 30.18/21.59  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => ((B = k1_wellord2(A)) <=> ((k3_relat_1(B) = A) & (![C, D]: ((r2_hidden(C, A) & r2_hidden(D, A)) => (r2_hidden(k4_tarski(C, D), B) <=> r1_tarski(C, D)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord2)).
% 30.18/21.59  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 30.18/21.59  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 30.18/21.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 30.18/21.59  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 30.18/21.59  tff(f_57, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 30.18/21.59  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 30.18/21.59  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 30.18/21.59  tff(f_77, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 30.18/21.59  tff(c_40, plain, (![A_24]: (v1_relat_1(k1_wellord2(A_24)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 30.18/21.59  tff(c_34, plain, (![A_16]: (k3_relat_1(k1_wellord2(A_16))=A_16 | ~v1_relat_1(k1_wellord2(A_16)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 30.18/21.59  tff(c_48, plain, (![A_16]: (k3_relat_1(k1_wellord2(A_16))=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34])).
% 30.18/21.59  tff(c_76, plain, (![A_35]: (k2_xboole_0(k1_relat_1(A_35), k2_relat_1(A_35))=k3_relat_1(A_35) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_53])).
% 30.18/21.59  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 30.18/21.59  tff(c_91, plain, (![A_36]: (r1_tarski(k1_relat_1(A_36), k3_relat_1(A_36)) | ~v1_relat_1(A_36))), inference(superposition, [status(thm), theory('equality')], [c_76, c_12])).
% 30.18/21.59  tff(c_96, plain, (![A_16]: (r1_tarski(k1_relat_1(k1_wellord2(A_16)), A_16) | ~v1_relat_1(k1_wellord2(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_91])).
% 30.18/21.59  tff(c_99, plain, (![A_16]: (r1_tarski(k1_relat_1(k1_wellord2(A_16)), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_96])).
% 30.18/21.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.18/21.59  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.18/21.59  tff(c_202, plain, (![A_58, A_59]: (r1_tarski(A_58, k3_relat_1(A_59)) | ~r1_tarski(A_58, k2_relat_1(A_59)) | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_76, c_8])).
% 30.18/21.59  tff(c_213, plain, (![A_58, A_16]: (r1_tarski(A_58, A_16) | ~r1_tarski(A_58, k2_relat_1(k1_wellord2(A_16))) | ~v1_relat_1(k1_wellord2(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_202])).
% 30.18/21.59  tff(c_219, plain, (![A_60, A_61]: (r1_tarski(A_60, A_61) | ~r1_tarski(A_60, k2_relat_1(k1_wellord2(A_61))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_213])).
% 30.18/21.59  tff(c_239, plain, (![A_61]: (r1_tarski(k2_relat_1(k1_wellord2(A_61)), A_61))), inference(resolution, [status(thm)], [c_6, c_219])).
% 30.18/21.59  tff(c_20, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 30.18/21.59  tff(c_161, plain, (![C_48, A_49, B_50]: (r1_tarski(k2_zfmisc_1(C_48, A_49), k2_zfmisc_1(C_48, B_50)) | ~r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 30.18/21.59  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 30.18/21.59  tff(c_1964, plain, (![A_202, C_203, B_204, A_205]: (r1_tarski(A_202, k2_zfmisc_1(C_203, B_204)) | ~r1_tarski(A_202, k2_zfmisc_1(C_203, A_205)) | ~r1_tarski(A_205, B_204))), inference(resolution, [status(thm)], [c_161, c_10])).
% 30.18/21.59  tff(c_3939, plain, (![A_275, B_276]: (r1_tarski(A_275, k2_zfmisc_1(k1_relat_1(A_275), B_276)) | ~r1_tarski(k2_relat_1(A_275), B_276) | ~v1_relat_1(A_275))), inference(resolution, [status(thm)], [c_20, c_1964])).
% 30.18/21.59  tff(c_166, plain, (![A_6, C_48, B_50, A_49]: (r1_tarski(A_6, k2_zfmisc_1(C_48, B_50)) | ~r1_tarski(A_6, k2_zfmisc_1(C_48, A_49)) | ~r1_tarski(A_49, B_50))), inference(resolution, [status(thm)], [c_161, c_10])).
% 30.18/21.59  tff(c_55066, plain, (![A_1479, B_1480, B_1481]: (r1_tarski(A_1479, k2_zfmisc_1(k1_relat_1(A_1479), B_1480)) | ~r1_tarski(B_1481, B_1480) | ~r1_tarski(k2_relat_1(A_1479), B_1481) | ~v1_relat_1(A_1479))), inference(resolution, [status(thm)], [c_3939, c_166])).
% 30.18/21.59  tff(c_66058, plain, (![A_1666, A_1667]: (r1_tarski(A_1666, k2_zfmisc_1(k1_relat_1(A_1666), A_1667)) | ~r1_tarski(k2_relat_1(A_1666), k2_relat_1(k1_wellord2(A_1667))) | ~v1_relat_1(A_1666))), inference(resolution, [status(thm)], [c_239, c_55066])).
% 30.18/21.59  tff(c_66172, plain, (![A_1667]: (r1_tarski(k1_wellord2(A_1667), k2_zfmisc_1(k1_relat_1(k1_wellord2(A_1667)), A_1667)) | ~v1_relat_1(k1_wellord2(A_1667)))), inference(resolution, [status(thm)], [c_6, c_66058])).
% 30.18/21.59  tff(c_66620, plain, (![A_1672]: (r1_tarski(k1_wellord2(A_1672), k2_zfmisc_1(k1_relat_1(k1_wellord2(A_1672)), A_1672)))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_66172])).
% 30.18/21.59  tff(c_195, plain, (![A_55, C_56, B_57]: (r1_tarski(k2_zfmisc_1(A_55, C_56), k2_zfmisc_1(B_57, C_56)) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 30.18/21.59  tff(c_200, plain, (![A_6, B_57, C_56, A_55]: (r1_tarski(A_6, k2_zfmisc_1(B_57, C_56)) | ~r1_tarski(A_6, k2_zfmisc_1(A_55, C_56)) | ~r1_tarski(A_55, B_57))), inference(resolution, [status(thm)], [c_195, c_10])).
% 30.18/21.59  tff(c_66760, plain, (![A_1675, B_1676]: (r1_tarski(k1_wellord2(A_1675), k2_zfmisc_1(B_1676, A_1675)) | ~r1_tarski(k1_relat_1(k1_wellord2(A_1675)), B_1676))), inference(resolution, [status(thm)], [c_66620, c_200])).
% 30.18/21.59  tff(c_67609, plain, (![A_16]: (r1_tarski(k1_wellord2(A_16), k2_zfmisc_1(A_16, A_16)))), inference(resolution, [status(thm)], [c_99, c_66760])).
% 30.18/21.59  tff(c_42, plain, (~r1_tarski(k1_wellord2('#skF_3'), k2_zfmisc_1('#skF_3', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 30.18/21.59  tff(c_67700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67609, c_42])).
% 30.18/21.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 30.18/21.59  
% 30.18/21.59  Inference rules
% 30.18/21.59  ----------------------
% 30.18/21.59  #Ref     : 0
% 30.18/21.59  #Sup     : 18246
% 30.18/21.59  #Fact    : 0
% 30.18/21.59  #Define  : 0
% 30.18/21.59  #Split   : 0
% 30.18/21.59  #Chain   : 0
% 30.18/21.59  #Close   : 0
% 30.18/21.59  
% 30.18/21.59  Ordering : KBO
% 30.18/21.59  
% 30.18/21.59  Simplification rules
% 30.18/21.59  ----------------------
% 30.18/21.59  #Subsume      : 173
% 30.18/21.59  #Demod        : 713
% 30.18/21.59  #Tautology    : 446
% 30.18/21.59  #SimpNegUnit  : 0
% 30.18/21.59  #BackRed      : 1
% 30.18/21.59  
% 30.18/21.59  #Partial instantiations: 0
% 30.18/21.59  #Strategies tried      : 1
% 30.18/21.59  
% 30.18/21.59  Timing (in seconds)
% 30.18/21.59  ----------------------
% 30.18/21.60  Preprocessing        : 0.29
% 30.18/21.60  Parsing              : 0.16
% 30.18/21.60  CNF conversion       : 0.02
% 30.18/21.60  Main loop            : 20.47
% 30.18/21.60  Inferencing          : 1.73
% 30.18/21.60  Reduction            : 7.05
% 30.18/21.60  Demodulation         : 6.29
% 30.18/21.60  BG Simplification    : 0.32
% 30.18/21.60  Subsumption          : 10.23
% 30.18/21.60  Abstraction          : 0.42
% 30.18/21.60  MUC search           : 0.00
% 30.18/21.60  Cooper               : 0.00
% 30.18/21.60  Total                : 20.81
% 30.18/21.60  Index Insertion      : 0.00
% 30.18/21.60  Index Deletion       : 0.00
% 30.18/21.60  Index Matching       : 0.00
% 30.18/21.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
