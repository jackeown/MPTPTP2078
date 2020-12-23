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
% DateTime   : Thu Dec  3 09:58:21 EST 2020

% Result     : Theorem 2.92s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 120 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 212 expanded)
%              Number of equality atoms :    6 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k2_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k2_relat_1(A),k2_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] : r1_tarski(k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)),k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_14,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [A_75,C_76,B_77] :
      ( r1_tarski(k2_xboole_0(A_75,C_76),B_77)
      | ~ r1_tarski(C_76,B_77)
      | ~ r1_tarski(A_75,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_48,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = A_15
      | ~ r1_tarski(k2_xboole_0(A_15,B_16),A_15) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_234,plain,(
    ! [B_77,C_76] :
      ( k2_xboole_0(B_77,C_76) = B_77
      | ~ r1_tarski(C_76,B_77)
      | ~ r1_tarski(B_77,B_77) ) ),
    inference(resolution,[status(thm)],[c_226,c_58])).

tff(c_255,plain,(
    ! [B_78,C_79] :
      ( k2_xboole_0(B_78,C_79) = B_78
      | ~ r1_tarski(C_79,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_234])).

tff(c_294,plain,(
    ! [A_80] : k2_xboole_0(A_80,k1_xboole_0) = A_80 ),
    inference(resolution,[status(thm)],[c_14,c_255])).

tff(c_180,plain,(
    ! [A_67,B_68,C_69] : r1_tarski(k2_xboole_0(k3_xboole_0(A_67,B_68),k3_xboole_0(A_67,C_69)),k2_xboole_0(B_68,C_69)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_195,plain,(
    ! [A_67,B_68,C_69] : r1_tarski(k3_xboole_0(A_67,B_68),k2_xboole_0(B_68,C_69)) ),
    inference(resolution,[status(thm)],[c_180,c_8])).

tff(c_410,plain,(
    ! [A_82,A_83] : r1_tarski(k3_xboole_0(A_82,A_83),A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_195])).

tff(c_24,plain,(
    ! [A_20,B_21] :
      ( m1_subset_1(A_20,k1_zfmisc_1(B_21))
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(A_20)
      | ~ v1_relat_1(B_21)
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(resolution,[status(thm)],[c_24,c_93])).

tff(c_427,plain,(
    ! [A_82,A_83] :
      ( v1_relat_1(k3_xboole_0(A_82,A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(resolution,[status(thm)],[c_410,c_97])).

tff(c_303,plain,(
    ! [A_67,A_80] : r1_tarski(k3_xboole_0(A_67,A_80),A_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_195])).

tff(c_1578,plain,(
    ! [A_129,B_130] :
      ( r1_tarski(k2_relat_1(A_129),k2_relat_1(B_130))
      | ~ r1_tarski(A_129,B_130)
      | ~ v1_relat_1(B_130)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_956,plain,(
    ! [A_106,B_107] :
      ( r1_tarski(k2_relat_1(A_106),k2_relat_1(B_107))
      | ~ r1_tarski(A_106,B_107)
      | ~ v1_relat_1(B_107)
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_473,plain,(
    ! [A_85,B_86,C_87] :
      ( r1_tarski(A_85,k3_xboole_0(B_86,C_87))
      | ~ r1_tarski(A_85,C_87)
      | ~ r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_510,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_473,c_32])).

tff(c_572,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_510])).

tff(c_962,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_956,c_572])).

tff(c_974,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_10,c_962])).

tff(c_980,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_427,c_974])).

tff(c_987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_980])).

tff(c_988,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0('#skF_1','#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_510])).

tff(c_1584,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1578,c_988])).

tff(c_1596,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_303,c_1584])).

tff(c_1602,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_427,c_1596])).

tff(c_1609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1602])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:37:45 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.92/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.45  
% 2.92/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.92/1.45  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.92/1.45  
% 2.92/1.45  %Foreground sorts:
% 2.92/1.45  
% 2.92/1.45  
% 2.92/1.45  %Background operators:
% 2.92/1.45  
% 2.92/1.45  
% 2.92/1.45  %Foreground operators:
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.92/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.92/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.92/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.92/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.92/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.92/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.92/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.92/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.92/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.92/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.92/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.92/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.92/1.45  
% 3.06/1.47  tff(f_85, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_relat_1)).
% 3.06/1.47  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.06/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.47  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.06/1.47  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.06/1.47  tff(f_47, axiom, (![A, B, C]: r1_tarski(k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)), k2_xboole_0(B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 3.06/1.47  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.06/1.47  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.06/1.47  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.06/1.47  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 3.06/1.47  tff(f_37, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.06/1.47  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 3.06/1.47  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.06/1.47  tff(c_14, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.06/1.47  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.47  tff(c_226, plain, (![A_75, C_76, B_77]: (r1_tarski(k2_xboole_0(A_75, C_76), B_77) | ~r1_tarski(C_76, B_77) | ~r1_tarski(A_75, B_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.06/1.47  tff(c_18, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.47  tff(c_48, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.47  tff(c_58, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=A_15 | ~r1_tarski(k2_xboole_0(A_15, B_16), A_15))), inference(resolution, [status(thm)], [c_18, c_48])).
% 3.06/1.47  tff(c_234, plain, (![B_77, C_76]: (k2_xboole_0(B_77, C_76)=B_77 | ~r1_tarski(C_76, B_77) | ~r1_tarski(B_77, B_77))), inference(resolution, [status(thm)], [c_226, c_58])).
% 3.06/1.47  tff(c_255, plain, (![B_78, C_79]: (k2_xboole_0(B_78, C_79)=B_78 | ~r1_tarski(C_79, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_234])).
% 3.06/1.47  tff(c_294, plain, (![A_80]: (k2_xboole_0(A_80, k1_xboole_0)=A_80)), inference(resolution, [status(thm)], [c_14, c_255])).
% 3.06/1.47  tff(c_180, plain, (![A_67, B_68, C_69]: (r1_tarski(k2_xboole_0(k3_xboole_0(A_67, B_68), k3_xboole_0(A_67, C_69)), k2_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.47  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.47  tff(c_195, plain, (![A_67, B_68, C_69]: (r1_tarski(k3_xboole_0(A_67, B_68), k2_xboole_0(B_68, C_69)))), inference(resolution, [status(thm)], [c_180, c_8])).
% 3.06/1.47  tff(c_410, plain, (![A_82, A_83]: (r1_tarski(k3_xboole_0(A_82, A_83), A_83))), inference(superposition, [status(thm), theory('equality')], [c_294, c_195])).
% 3.06/1.47  tff(c_24, plain, (![A_20, B_21]: (m1_subset_1(A_20, k1_zfmisc_1(B_21)) | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.06/1.47  tff(c_93, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.06/1.47  tff(c_97, plain, (![A_20, B_21]: (v1_relat_1(A_20) | ~v1_relat_1(B_21) | ~r1_tarski(A_20, B_21))), inference(resolution, [status(thm)], [c_24, c_93])).
% 3.06/1.47  tff(c_427, plain, (![A_82, A_83]: (v1_relat_1(k3_xboole_0(A_82, A_83)) | ~v1_relat_1(A_83))), inference(resolution, [status(thm)], [c_410, c_97])).
% 3.06/1.47  tff(c_303, plain, (![A_67, A_80]: (r1_tarski(k3_xboole_0(A_67, A_80), A_80))), inference(superposition, [status(thm), theory('equality')], [c_294, c_195])).
% 3.06/1.47  tff(c_1578, plain, (![A_129, B_130]: (r1_tarski(k2_relat_1(A_129), k2_relat_1(B_130)) | ~r1_tarski(A_129, B_130) | ~v1_relat_1(B_130) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.06/1.47  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.06/1.47  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.47  tff(c_956, plain, (![A_106, B_107]: (r1_tarski(k2_relat_1(A_106), k2_relat_1(B_107)) | ~r1_tarski(A_106, B_107) | ~v1_relat_1(B_107) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.06/1.47  tff(c_473, plain, (![A_85, B_86, C_87]: (r1_tarski(A_85, k3_xboole_0(B_86, C_87)) | ~r1_tarski(A_85, C_87) | ~r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.47  tff(c_32, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.06/1.47  tff(c_510, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2')) | ~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_473, c_32])).
% 3.06/1.47  tff(c_572, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_510])).
% 3.06/1.47  tff(c_962, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_956, c_572])).
% 3.06/1.47  tff(c_974, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_10, c_962])).
% 3.06/1.47  tff(c_980, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_427, c_974])).
% 3.06/1.47  tff(c_987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_980])).
% 3.06/1.47  tff(c_988, plain, (~r1_tarski(k2_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k2_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_510])).
% 3.06/1.47  tff(c_1584, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1578, c_988])).
% 3.06/1.47  tff(c_1596, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_303, c_1584])).
% 3.06/1.47  tff(c_1602, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_427, c_1596])).
% 3.06/1.47  tff(c_1609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1602])).
% 3.06/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.47  
% 3.06/1.47  Inference rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Ref     : 0
% 3.06/1.47  #Sup     : 380
% 3.06/1.47  #Fact    : 0
% 3.06/1.47  #Define  : 0
% 3.06/1.47  #Split   : 3
% 3.06/1.47  #Chain   : 0
% 3.06/1.47  #Close   : 0
% 3.06/1.47  
% 3.06/1.47  Ordering : KBO
% 3.06/1.47  
% 3.06/1.47  Simplification rules
% 3.06/1.47  ----------------------
% 3.06/1.47  #Subsume      : 31
% 3.06/1.47  #Demod        : 201
% 3.06/1.47  #Tautology    : 242
% 3.06/1.47  #SimpNegUnit  : 4
% 3.06/1.47  #BackRed      : 3
% 3.06/1.47  
% 3.06/1.47  #Partial instantiations: 0
% 3.06/1.47  #Strategies tried      : 1
% 3.06/1.47  
% 3.06/1.47  Timing (in seconds)
% 3.06/1.47  ----------------------
% 3.06/1.47  Preprocessing        : 0.27
% 3.06/1.47  Parsing              : 0.15
% 3.06/1.47  CNF conversion       : 0.02
% 3.06/1.47  Main loop            : 0.41
% 3.06/1.47  Inferencing          : 0.16
% 3.06/1.47  Reduction            : 0.13
% 3.06/1.47  Demodulation         : 0.09
% 3.06/1.47  BG Simplification    : 0.02
% 3.06/1.47  Subsumption          : 0.07
% 3.06/1.47  Abstraction          : 0.02
% 3.06/1.47  MUC search           : 0.00
% 3.06/1.47  Cooper               : 0.00
% 3.06/1.47  Total                : 0.71
% 3.06/1.47  Index Insertion      : 0.00
% 3.06/1.47  Index Deletion       : 0.00
% 3.06/1.47  Index Matching       : 0.00
% 3.06/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
