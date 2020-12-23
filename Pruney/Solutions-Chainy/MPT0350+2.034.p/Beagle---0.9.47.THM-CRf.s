%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:30 EST 2020

% Result     : Theorem 2.55s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 118 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_66,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_28,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_44,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_40])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_34,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_114,plain,(
    ! [B_39,A_40] :
      ( r2_hidden(B_39,A_40)
      | ~ m1_subset_1(B_39,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [C_11,A_7] :
      ( r1_tarski(C_11,A_7)
      | ~ r2_hidden(C_11,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_118,plain,(
    ! [B_39,A_7] :
      ( r1_tarski(B_39,A_7)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_114,c_8])).

tff(c_122,plain,(
    ! [B_41,A_42] :
      ( r1_tarski(B_41,A_42)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_118])).

tff(c_131,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_122])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_135,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_131,c_4])).

tff(c_169,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(A_49,B_50) = k3_subset_1(A_49,B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_169])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_186,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_6])).

tff(c_189,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_186])).

tff(c_201,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k3_subset_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_121,plain,(
    ! [B_39,A_7] :
      ( r1_tarski(B_39,A_7)
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_7)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_118])).

tff(c_215,plain,(
    ! [A_53,B_54] :
      ( r1_tarski(k3_subset_1(A_53,B_54),A_53)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(resolution,[status(thm)],[c_201,c_121])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( r2_hidden(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_140,plain,(
    ! [B_43,A_44] :
      ( m1_subset_1(B_43,A_44)
      | ~ r2_hidden(B_43,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_146,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | v1_xboole_0(k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_140])).

tff(c_150,plain,(
    ! [C_11,A_7] :
      ( m1_subset_1(C_11,k1_zfmisc_1(A_7))
      | ~ r1_tarski(C_11,A_7) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_146])).

tff(c_365,plain,(
    ! [A_78,B_79,C_80] :
      ( k4_subset_1(A_78,B_79,C_80) = k2_xboole_0(B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_516,plain,(
    ! [A_91,B_92,C_93] :
      ( k4_subset_1(A_91,B_92,C_93) = k2_xboole_0(B_92,C_93)
      | ~ m1_subset_1(B_92,k1_zfmisc_1(A_91))
      | ~ r1_tarski(C_93,A_91) ) ),
    inference(resolution,[status(thm)],[c_150,c_365])).

tff(c_530,plain,(
    ! [C_94] :
      ( k4_subset_1('#skF_3','#skF_4',C_94) = k2_xboole_0('#skF_4',C_94)
      | ~ r1_tarski(C_94,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_42,c_516])).

tff(c_591,plain,(
    ! [B_101] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_101)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_101))
      | ~ m1_subset_1(B_101,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_215,c_530])).

tff(c_606,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_591])).

tff(c_611,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_606])).

tff(c_613,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_611])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:17:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.55/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.37  
% 2.55/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.55/1.38  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.55/1.38  
% 2.55/1.38  %Foreground sorts:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Background operators:
% 2.55/1.38  
% 2.55/1.38  
% 2.55/1.38  %Foreground operators:
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.55/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.55/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.55/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.55/1.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.55/1.38  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.55/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.55/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.55/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.55/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.55/1.38  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.55/1.38  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.55/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.55/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.55/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.55/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.55/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.55/1.38  
% 2.76/1.39  tff(f_55, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.76/1.39  tff(f_79, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.76/1.39  tff(f_66, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.76/1.39  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.76/1.39  tff(f_40, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.76/1.39  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.76/1.39  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.76/1.39  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.76/1.39  tff(f_63, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.76/1.39  tff(f_72, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.76/1.39  tff(c_28, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.39  tff(c_40, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.39  tff(c_44, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_40])).
% 2.76/1.39  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.76/1.39  tff(c_34, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.76/1.39  tff(c_114, plain, (![B_39, A_40]: (r2_hidden(B_39, A_40) | ~m1_subset_1(B_39, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.39  tff(c_8, plain, (![C_11, A_7]: (r1_tarski(C_11, A_7) | ~r2_hidden(C_11, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.39  tff(c_118, plain, (![B_39, A_7]: (r1_tarski(B_39, A_7) | ~m1_subset_1(B_39, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_114, c_8])).
% 2.76/1.39  tff(c_122, plain, (![B_41, A_42]: (r1_tarski(B_41, A_42) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)))), inference(negUnitSimplification, [status(thm)], [c_34, c_118])).
% 2.76/1.39  tff(c_131, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_122])).
% 2.76/1.39  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.39  tff(c_135, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_131, c_4])).
% 2.76/1.39  tff(c_169, plain, (![A_49, B_50]: (k4_xboole_0(A_49, B_50)=k3_subset_1(A_49, B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.76/1.39  tff(c_182, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_169])).
% 2.76/1.39  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.76/1.39  tff(c_186, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_182, c_6])).
% 2.76/1.39  tff(c_189, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_186])).
% 2.76/1.39  tff(c_201, plain, (![A_53, B_54]: (m1_subset_1(k3_subset_1(A_53, B_54), k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.76/1.39  tff(c_121, plain, (![B_39, A_7]: (r1_tarski(B_39, A_7) | ~m1_subset_1(B_39, k1_zfmisc_1(A_7)))), inference(negUnitSimplification, [status(thm)], [c_34, c_118])).
% 2.76/1.39  tff(c_215, plain, (![A_53, B_54]: (r1_tarski(k3_subset_1(A_53, B_54), A_53) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(resolution, [status(thm)], [c_201, c_121])).
% 2.76/1.39  tff(c_10, plain, (![C_11, A_7]: (r2_hidden(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.76/1.39  tff(c_140, plain, (![B_43, A_44]: (m1_subset_1(B_43, A_44) | ~r2_hidden(B_43, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.76/1.39  tff(c_146, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | v1_xboole_0(k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(resolution, [status(thm)], [c_10, c_140])).
% 2.76/1.39  tff(c_150, plain, (![C_11, A_7]: (m1_subset_1(C_11, k1_zfmisc_1(A_7)) | ~r1_tarski(C_11, A_7))), inference(negUnitSimplification, [status(thm)], [c_34, c_146])).
% 2.76/1.39  tff(c_365, plain, (![A_78, B_79, C_80]: (k4_subset_1(A_78, B_79, C_80)=k2_xboole_0(B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.76/1.39  tff(c_516, plain, (![A_91, B_92, C_93]: (k4_subset_1(A_91, B_92, C_93)=k2_xboole_0(B_92, C_93) | ~m1_subset_1(B_92, k1_zfmisc_1(A_91)) | ~r1_tarski(C_93, A_91))), inference(resolution, [status(thm)], [c_150, c_365])).
% 2.76/1.39  tff(c_530, plain, (![C_94]: (k4_subset_1('#skF_3', '#skF_4', C_94)=k2_xboole_0('#skF_4', C_94) | ~r1_tarski(C_94, '#skF_3'))), inference(resolution, [status(thm)], [c_42, c_516])).
% 2.76/1.39  tff(c_591, plain, (![B_101]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_101))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_101)) | ~m1_subset_1(B_101, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_215, c_530])).
% 2.76/1.39  tff(c_606, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_591])).
% 2.76/1.39  tff(c_611, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_606])).
% 2.76/1.39  tff(c_613, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_611])).
% 2.76/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.76/1.39  
% 2.76/1.39  Inference rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Ref     : 0
% 2.76/1.39  #Sup     : 130
% 2.76/1.39  #Fact    : 0
% 2.76/1.39  #Define  : 0
% 2.76/1.39  #Split   : 1
% 2.76/1.39  #Chain   : 0
% 2.76/1.39  #Close   : 0
% 2.76/1.39  
% 2.76/1.39  Ordering : KBO
% 2.76/1.39  
% 2.76/1.39  Simplification rules
% 2.76/1.39  ----------------------
% 2.76/1.39  #Subsume      : 19
% 2.76/1.39  #Demod        : 26
% 2.76/1.39  #Tautology    : 53
% 2.76/1.39  #SimpNegUnit  : 4
% 2.76/1.39  #BackRed      : 0
% 2.76/1.39  
% 2.76/1.39  #Partial instantiations: 0
% 2.76/1.39  #Strategies tried      : 1
% 2.76/1.39  
% 2.76/1.39  Timing (in seconds)
% 2.76/1.39  ----------------------
% 2.76/1.40  Preprocessing        : 0.31
% 2.76/1.40  Parsing              : 0.16
% 2.76/1.40  CNF conversion       : 0.02
% 2.76/1.40  Main loop            : 0.32
% 2.76/1.40  Inferencing          : 0.12
% 2.76/1.40  Reduction            : 0.10
% 2.76/1.40  Demodulation         : 0.07
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.06
% 2.76/1.40  Abstraction          : 0.02
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.66
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
