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
% DateTime   : Thu Dec  3 09:55:45 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   62 (  92 expanded)
%              Number of leaves         :   29 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   65 ( 106 expanded)
%              Number of equality atoms :   37 (  55 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_61,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(c_24,plain,(
    ! [A_22] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_10] : k1_subset_1(A_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = k2_subset_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_29,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_22])).

tff(c_31,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_29])).

tff(c_204,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(k3_subset_1(A_41,B_42),k1_zfmisc_1(A_41))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_218,plain,(
    ! [A_21] :
      ( m1_subset_1(A_21,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_204])).

tff(c_224,plain,(
    ! [A_21] : m1_subset_1(A_21,k1_zfmisc_1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_218])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_270,plain,(
    ! [A_46,B_47,C_48] :
      ( k4_subset_1(A_46,B_47,C_48) = k2_xboole_0(B_47,C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(A_46))
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_316,plain,(
    ! [B_51] :
      ( k4_subset_1('#skF_1',B_51,'#skF_2') = k2_xboole_0(B_51,'#skF_2')
      | ~ m1_subset_1(B_51,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_270])).

tff(c_332,plain,(
    k4_subset_1('#skF_1','#skF_1','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_224,c_316])).

tff(c_388,plain,(
    ! [A_55,C_56,B_57] :
      ( k4_subset_1(A_55,C_56,B_57) = k4_subset_1(A_55,B_57,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_418,plain,(
    ! [B_58] :
      ( k4_subset_1('#skF_1',B_58,'#skF_2') = k4_subset_1('#skF_1','#skF_2',B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_388])).

tff(c_422,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k4_subset_1('#skF_1','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_224,c_418])).

tff(c_435,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_422])).

tff(c_26,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_30,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_26])).

tff(c_441,plain,(
    k2_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_435,c_30])).

tff(c_91,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k3_subset_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_98,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_91])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_4])).

tff(c_148,plain,(
    ! [A_37,B_38] :
      ( k3_subset_1(A_37,k3_subset_1(A_37,B_38)) = B_38
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_153,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_148])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = k3_subset_1(A_12,B_13)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_853,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,k3_subset_1(A_78,B_79)) = k3_subset_1(A_78,k3_subset_1(A_78,B_79))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(resolution,[status(thm)],[c_204,c_14])).

tff(c_859,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_853])).

tff(c_866,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_153,c_859])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_879,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_2])).

tff(c_884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_879])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  
% 2.58/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  %$ m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.58/1.39  
% 2.58/1.39  %Foreground sorts:
% 2.58/1.39  
% 2.58/1.39  
% 2.58/1.39  %Background operators:
% 2.58/1.39  
% 2.58/1.39  
% 2.58/1.39  %Foreground operators:
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.58/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.58/1.39  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.58/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.39  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.58/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.58/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.58/1.39  
% 2.58/1.41  tff(f_63, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.58/1.41  tff(f_39, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.58/1.41  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.58/1.41  tff(f_61, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.58/1.41  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.58/1.41  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.58/1.41  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.58/1.41  tff(f_37, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.58/1.41  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.58/1.41  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.58/1.41  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.58/1.41  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.58/1.41  tff(c_24, plain, (![A_22]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.58/1.41  tff(c_10, plain, (![A_10]: (k1_subset_1(A_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.41  tff(c_12, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.41  tff(c_22, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=k2_subset_1(A_21))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.58/1.41  tff(c_29, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_22])).
% 2.58/1.41  tff(c_31, plain, (![A_21]: (k3_subset_1(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_29])).
% 2.58/1.41  tff(c_204, plain, (![A_41, B_42]: (m1_subset_1(k3_subset_1(A_41, B_42), k1_zfmisc_1(A_41)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.41  tff(c_218, plain, (![A_21]: (m1_subset_1(A_21, k1_zfmisc_1(A_21)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_31, c_204])).
% 2.58/1.41  tff(c_224, plain, (![A_21]: (m1_subset_1(A_21, k1_zfmisc_1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_218])).
% 2.58/1.41  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.58/1.41  tff(c_270, plain, (![A_46, B_47, C_48]: (k4_subset_1(A_46, B_47, C_48)=k2_xboole_0(B_47, C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(A_46)) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.58/1.41  tff(c_316, plain, (![B_51]: (k4_subset_1('#skF_1', B_51, '#skF_2')=k2_xboole_0(B_51, '#skF_2') | ~m1_subset_1(B_51, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_270])).
% 2.58/1.41  tff(c_332, plain, (k4_subset_1('#skF_1', '#skF_1', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_224, c_316])).
% 2.58/1.41  tff(c_388, plain, (![A_55, C_56, B_57]: (k4_subset_1(A_55, C_56, B_57)=k4_subset_1(A_55, B_57, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(A_55)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.58/1.41  tff(c_418, plain, (![B_58]: (k4_subset_1('#skF_1', B_58, '#skF_2')=k4_subset_1('#skF_1', '#skF_2', B_58) | ~m1_subset_1(B_58, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_388])).
% 2.58/1.41  tff(c_422, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k4_subset_1('#skF_1', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_224, c_418])).
% 2.58/1.41  tff(c_435, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_332, c_422])).
% 2.58/1.41  tff(c_26, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.58/1.41  tff(c_30, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_26])).
% 2.58/1.41  tff(c_441, plain, (k2_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_435, c_30])).
% 2.58/1.41  tff(c_91, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k3_subset_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.41  tff(c_98, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_91])).
% 2.58/1.41  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.58/1.41  tff(c_116, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_98, c_4])).
% 2.58/1.41  tff(c_148, plain, (![A_37, B_38]: (k3_subset_1(A_37, k3_subset_1(A_37, B_38))=B_38 | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.58/1.41  tff(c_153, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_148])).
% 2.58/1.41  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=k3_subset_1(A_12, B_13) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.58/1.41  tff(c_853, plain, (![A_78, B_79]: (k4_xboole_0(A_78, k3_subset_1(A_78, B_79))=k3_subset_1(A_78, k3_subset_1(A_78, B_79)) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(resolution, [status(thm)], [c_204, c_14])).
% 2.58/1.41  tff(c_859, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_853])).
% 2.58/1.41  tff(c_866, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_153, c_859])).
% 2.58/1.41  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.58/1.41  tff(c_879, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_866, c_2])).
% 2.58/1.41  tff(c_884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_441, c_879])).
% 2.58/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.41  
% 2.58/1.41  Inference rules
% 2.58/1.41  ----------------------
% 2.58/1.41  #Ref     : 0
% 2.58/1.41  #Sup     : 215
% 2.58/1.41  #Fact    : 0
% 2.58/1.41  #Define  : 0
% 2.58/1.41  #Split   : 0
% 2.58/1.41  #Chain   : 0
% 2.58/1.41  #Close   : 0
% 2.58/1.41  
% 2.58/1.41  Ordering : KBO
% 2.58/1.41  
% 2.58/1.41  Simplification rules
% 2.58/1.41  ----------------------
% 2.58/1.41  #Subsume      : 1
% 2.58/1.41  #Demod        : 110
% 2.58/1.41  #Tautology    : 155
% 2.58/1.41  #SimpNegUnit  : 1
% 2.58/1.41  #BackRed      : 8
% 2.58/1.41  
% 2.58/1.41  #Partial instantiations: 0
% 2.58/1.41  #Strategies tried      : 1
% 2.58/1.41  
% 2.58/1.41  Timing (in seconds)
% 2.58/1.41  ----------------------
% 2.58/1.41  Preprocessing        : 0.29
% 2.58/1.41  Parsing              : 0.16
% 2.58/1.41  CNF conversion       : 0.01
% 2.58/1.41  Main loop            : 0.32
% 2.58/1.41  Inferencing          : 0.12
% 2.58/1.41  Reduction            : 0.11
% 2.58/1.41  Demodulation         : 0.08
% 2.58/1.41  BG Simplification    : 0.02
% 2.58/1.41  Subsumption          : 0.05
% 2.58/1.41  Abstraction          : 0.02
% 2.58/1.41  MUC search           : 0.00
% 2.58/1.41  Cooper               : 0.00
% 2.58/1.41  Total                : 0.64
% 2.58/1.41  Index Insertion      : 0.00
% 2.58/1.41  Index Deletion       : 0.00
% 2.58/1.41  Index Matching       : 0.00
% 2.58/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
