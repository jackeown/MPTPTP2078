%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:14 EST 2020

% Result     : Theorem 7.94s
% Output     : CNFRefutation 7.94s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 117 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 167 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_133,plain,(
    ! [B_47,A_48] : k1_setfam_1(k2_tarski(B_47,A_48)) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_91])).

tff(c_16,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_139,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_16])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(A_18,k1_zfmisc_1(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_201,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(B_51)
      | ~ m1_subset_1(B_51,k1_zfmisc_1(A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_3010,plain,(
    ! [A_140,B_141] :
      ( v1_relat_1(A_140)
      | ~ v1_relat_1(B_141)
      | ~ r1_tarski(A_140,B_141) ) ),
    inference(resolution,[status(thm)],[c_20,c_201])).

tff(c_3039,plain,(
    ! [A_142,B_143] :
      ( v1_relat_1(k3_xboole_0(A_142,B_143))
      | ~ v1_relat_1(A_142) ) ),
    inference(resolution,[status(thm)],[c_4,c_3010])).

tff(c_3042,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(k3_xboole_0(B_47,A_48))
      | ~ v1_relat_1(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_3039])).

tff(c_111,plain,(
    ! [A_43,B_44] :
      ( k2_xboole_0(A_43,B_44) = B_44
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_111])).

tff(c_292,plain,(
    ! [A_62,B_63] :
      ( k2_xboole_0(k1_relat_1(A_62),k1_relat_1(B_63)) = k1_relat_1(k2_xboole_0(A_62,B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3693,plain,(
    ! [A_164,B_165] :
      ( r1_tarski(k1_relat_1(A_164),k1_relat_1(k2_xboole_0(A_164,B_165)))
      | ~ v1_relat_1(B_165)
      | ~ v1_relat_1(A_164) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_8])).

tff(c_5767,plain,(
    ! [A_203,B_204] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_203,B_204)),k1_relat_1(A_203))
      | ~ v1_relat_1(A_203)
      | ~ v1_relat_1(k3_xboole_0(A_203,B_204)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_3693])).

tff(c_12078,plain,(
    ! [A_260,B_261] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_260,B_261)),k1_relat_1(B_261))
      | ~ v1_relat_1(B_261)
      | ~ v1_relat_1(k3_xboole_0(B_261,A_260)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_5767])).

tff(c_506,plain,(
    ! [A_74,B_75] :
      ( v1_relat_1(A_74)
      | ~ v1_relat_1(B_75)
      | ~ r1_tarski(A_74,B_75) ) ),
    inference(resolution,[status(thm)],[c_20,c_201])).

tff(c_531,plain,(
    ! [A_76,B_77] :
      ( v1_relat_1(k3_xboole_0(A_76,B_77))
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_4,c_506])).

tff(c_537,plain,(
    ! [A_48,B_47] :
      ( v1_relat_1(k3_xboole_0(A_48,B_47))
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_531])).

tff(c_30,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_656,plain,(
    ! [A_86,B_87] :
      ( r1_tarski(k1_relat_1(A_86),k1_relat_1(k2_xboole_0(A_86,B_87)))
      | ~ v1_relat_1(B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_8])).

tff(c_2869,plain,(
    ! [A_135,B_136] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_135,B_136)),k1_relat_1(A_135))
      | ~ v1_relat_1(A_135)
      | ~ v1_relat_1(k3_xboole_0(A_135,B_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_656])).

tff(c_220,plain,(
    ! [A_55,B_56,C_57] :
      ( r1_tarski(A_55,k3_xboole_0(B_56,C_57))
      | ~ r1_tarski(A_55,C_57)
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_234,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_220,c_26])).

tff(c_410,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_234])).

tff(c_2881,plain,
    ( ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2869,c_410])).

tff(c_2927,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2881])).

tff(c_2942,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_537,c_2927])).

tff(c_2949,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_2942])).

tff(c_2950,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_234])).

tff(c_12087,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_12078,c_2950])).

tff(c_12168,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_28,c_12087])).

tff(c_12195,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_3042,c_12168])).

tff(c_12202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_12195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:28:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.94/2.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.79  
% 7.94/2.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.79  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 7.94/2.79  
% 7.94/2.79  %Foreground sorts:
% 7.94/2.79  
% 7.94/2.79  
% 7.94/2.79  %Background operators:
% 7.94/2.79  
% 7.94/2.79  
% 7.94/2.79  %Foreground operators:
% 7.94/2.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.94/2.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.94/2.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.94/2.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.94/2.79  tff('#skF_2', type, '#skF_2': $i).
% 7.94/2.79  tff('#skF_1', type, '#skF_1': $i).
% 7.94/2.79  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.94/2.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.94/2.79  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.94/2.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.94/2.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.94/2.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.94/2.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.94/2.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.94/2.79  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.94/2.79  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.94/2.80  
% 7.94/2.81  tff(f_73, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 7.94/2.81  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.94/2.81  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 7.94/2.81  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.94/2.81  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.94/2.81  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.94/2.81  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.94/2.81  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 7.94/2.81  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.94/2.81  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 7.94/2.81  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.94/2.81  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.94/2.81  tff(c_91, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.94/2.81  tff(c_133, plain, (![B_47, A_48]: (k1_setfam_1(k2_tarski(B_47, A_48))=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_10, c_91])).
% 7.94/2.81  tff(c_16, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.94/2.81  tff(c_139, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_133, c_16])).
% 7.94/2.81  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.94/2.81  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(A_18, k1_zfmisc_1(B_19)) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.94/2.81  tff(c_201, plain, (![B_51, A_52]: (v1_relat_1(B_51) | ~m1_subset_1(B_51, k1_zfmisc_1(A_52)) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.94/2.81  tff(c_3010, plain, (![A_140, B_141]: (v1_relat_1(A_140) | ~v1_relat_1(B_141) | ~r1_tarski(A_140, B_141))), inference(resolution, [status(thm)], [c_20, c_201])).
% 7.94/2.81  tff(c_3039, plain, (![A_142, B_143]: (v1_relat_1(k3_xboole_0(A_142, B_143)) | ~v1_relat_1(A_142))), inference(resolution, [status(thm)], [c_4, c_3010])).
% 7.94/2.81  tff(c_3042, plain, (![B_47, A_48]: (v1_relat_1(k3_xboole_0(B_47, A_48)) | ~v1_relat_1(A_48))), inference(superposition, [status(thm), theory('equality')], [c_139, c_3039])).
% 7.94/2.81  tff(c_111, plain, (![A_43, B_44]: (k2_xboole_0(A_43, B_44)=B_44 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.94/2.81  tff(c_118, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_111])).
% 7.94/2.81  tff(c_292, plain, (![A_62, B_63]: (k2_xboole_0(k1_relat_1(A_62), k1_relat_1(B_63))=k1_relat_1(k2_xboole_0(A_62, B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.94/2.81  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.94/2.81  tff(c_3693, plain, (![A_164, B_165]: (r1_tarski(k1_relat_1(A_164), k1_relat_1(k2_xboole_0(A_164, B_165))) | ~v1_relat_1(B_165) | ~v1_relat_1(A_164))), inference(superposition, [status(thm), theory('equality')], [c_292, c_8])).
% 7.94/2.81  tff(c_5767, plain, (![A_203, B_204]: (r1_tarski(k1_relat_1(k3_xboole_0(A_203, B_204)), k1_relat_1(A_203)) | ~v1_relat_1(A_203) | ~v1_relat_1(k3_xboole_0(A_203, B_204)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_3693])).
% 7.94/2.81  tff(c_12078, plain, (![A_260, B_261]: (r1_tarski(k1_relat_1(k3_xboole_0(A_260, B_261)), k1_relat_1(B_261)) | ~v1_relat_1(B_261) | ~v1_relat_1(k3_xboole_0(B_261, A_260)))), inference(superposition, [status(thm), theory('equality')], [c_139, c_5767])).
% 7.94/2.81  tff(c_506, plain, (![A_74, B_75]: (v1_relat_1(A_74) | ~v1_relat_1(B_75) | ~r1_tarski(A_74, B_75))), inference(resolution, [status(thm)], [c_20, c_201])).
% 7.94/2.81  tff(c_531, plain, (![A_76, B_77]: (v1_relat_1(k3_xboole_0(A_76, B_77)) | ~v1_relat_1(A_76))), inference(resolution, [status(thm)], [c_4, c_506])).
% 7.94/2.81  tff(c_537, plain, (![A_48, B_47]: (v1_relat_1(k3_xboole_0(A_48, B_47)) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_139, c_531])).
% 7.94/2.81  tff(c_30, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.94/2.81  tff(c_656, plain, (![A_86, B_87]: (r1_tarski(k1_relat_1(A_86), k1_relat_1(k2_xboole_0(A_86, B_87))) | ~v1_relat_1(B_87) | ~v1_relat_1(A_86))), inference(superposition, [status(thm), theory('equality')], [c_292, c_8])).
% 7.94/2.81  tff(c_2869, plain, (![A_135, B_136]: (r1_tarski(k1_relat_1(k3_xboole_0(A_135, B_136)), k1_relat_1(A_135)) | ~v1_relat_1(A_135) | ~v1_relat_1(k3_xboole_0(A_135, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_118, c_656])).
% 7.94/2.81  tff(c_220, plain, (![A_55, B_56, C_57]: (r1_tarski(A_55, k3_xboole_0(B_56, C_57)) | ~r1_tarski(A_55, C_57) | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.94/2.81  tff(c_26, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.94/2.81  tff(c_234, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_220, c_26])).
% 7.94/2.81  tff(c_410, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_234])).
% 7.94/2.81  tff(c_2881, plain, (~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_2869, c_410])).
% 7.94/2.81  tff(c_2927, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2881])).
% 7.94/2.81  tff(c_2942, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_537, c_2927])).
% 7.94/2.81  tff(c_2949, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_2942])).
% 7.94/2.81  tff(c_2950, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_234])).
% 7.94/2.81  tff(c_12087, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_12078, c_2950])).
% 7.94/2.81  tff(c_12168, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_28, c_12087])).
% 7.94/2.81  tff(c_12195, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_3042, c_12168])).
% 7.94/2.81  tff(c_12202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_12195])).
% 7.94/2.81  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.94/2.81  
% 7.94/2.81  Inference rules
% 7.94/2.81  ----------------------
% 7.94/2.81  #Ref     : 0
% 7.94/2.81  #Sup     : 3130
% 7.94/2.81  #Fact    : 0
% 7.94/2.81  #Define  : 0
% 7.94/2.81  #Split   : 3
% 7.94/2.81  #Chain   : 0
% 7.94/2.81  #Close   : 0
% 7.94/2.81  
% 7.94/2.81  Ordering : KBO
% 7.94/2.81  
% 7.94/2.81  Simplification rules
% 7.94/2.81  ----------------------
% 7.94/2.81  #Subsume      : 484
% 7.94/2.81  #Demod        : 4242
% 7.94/2.81  #Tautology    : 2042
% 7.94/2.81  #SimpNegUnit  : 3
% 7.94/2.81  #BackRed      : 0
% 7.94/2.81  
% 7.94/2.81  #Partial instantiations: 0
% 7.94/2.81  #Strategies tried      : 1
% 7.94/2.81  
% 7.94/2.81  Timing (in seconds)
% 7.94/2.81  ----------------------
% 7.94/2.81  Preprocessing        : 0.30
% 7.94/2.81  Parsing              : 0.16
% 7.94/2.81  CNF conversion       : 0.02
% 7.94/2.81  Main loop            : 1.75
% 7.94/2.81  Inferencing          : 0.43
% 7.94/2.81  Reduction            : 0.95
% 7.94/2.81  Demodulation         : 0.83
% 7.94/2.81  BG Simplification    : 0.05
% 7.94/2.81  Subsumption          : 0.24
% 7.94/2.81  Abstraction          : 0.09
% 7.94/2.81  MUC search           : 0.00
% 7.94/2.81  Cooper               : 0.00
% 7.94/2.81  Total                : 2.09
% 7.94/2.81  Index Insertion      : 0.00
% 7.94/2.81  Index Deletion       : 0.00
% 7.94/2.81  Index Matching       : 0.00
% 7.94/2.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
