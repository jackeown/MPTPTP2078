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
% DateTime   : Thu Dec  3 09:55:46 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   30 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  73 expanded)
%              Number of equality atoms :   24 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_45,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_34] : k2_subset_1(A_34) = A_34 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ! [A_37] : m1_subset_1(k2_subset_1(A_37),k1_zfmisc_1(A_37)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_36,plain,(
    ! [A_37] : m1_subset_1(A_37,k1_zfmisc_1(A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_24])).

tff(c_231,plain,(
    ! [A_86,B_87,C_88] :
      ( k4_subset_1(A_86,B_87,C_88) = k2_xboole_0(B_87,C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_241,plain,(
    ! [A_89,B_90] :
      ( k4_subset_1(A_89,B_90,A_89) = k2_xboole_0(B_90,A_89)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_89)) ) ),
    inference(resolution,[status(thm)],[c_36,c_231])).

tff(c_250,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_241])).

tff(c_32,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_35,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_20,c_32])).

tff(c_260,plain,(
    k2_xboole_0('#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_35])).

tff(c_30,plain,(
    ! [A_43,B_44] :
      ( k4_subset_1(A_43,B_44,k3_subset_1(A_43,B_44)) = k2_subset_1(A_43)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_139,plain,(
    ! [A_64,B_65] :
      ( k4_subset_1(A_64,B_65,k3_subset_1(A_64,B_65)) = A_64
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_30])).

tff(c_148,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_139])).

tff(c_93,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_93])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_4])).

tff(c_26,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k3_subset_1(A_38,B_39),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_364,plain,(
    ! [A_108,B_109,B_110] :
      ( k4_subset_1(A_108,B_109,k3_subset_1(A_108,B_110)) = k2_xboole_0(B_109,k3_subset_1(A_108,B_110))
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(A_108)) ) ),
    inference(resolution,[status(thm)],[c_26,c_231])).

tff(c_385,plain,(
    ! [B_113] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_113)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_113))
      | ~ m1_subset_1(B_113,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_34,c_364])).

tff(c_396,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_385])).

tff(c_400,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_117,c_396])).

tff(c_402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_400])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.88  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.88  
% 3.09/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.89  %$ m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 3.09/1.89  
% 3.09/1.89  %Foreground sorts:
% 3.09/1.89  
% 3.09/1.89  
% 3.09/1.89  %Background operators:
% 3.09/1.89  
% 3.09/1.89  
% 3.09/1.89  %Foreground operators:
% 3.09/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.09/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.09/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.89  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.09/1.89  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 3.09/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.89  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.89  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.09/1.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.89  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.09/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.09/1.89  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.09/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.09/1.89  
% 3.09/1.91  tff(f_70, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 3.09/1.91  tff(f_45, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.09/1.91  tff(f_51, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.09/1.91  tff(f_61, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 3.09/1.91  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 3.09/1.91  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.09/1.91  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.09/1.91  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 3.09/1.91  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.09/1.91  tff(c_20, plain, (![A_34]: (k2_subset_1(A_34)=A_34)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.09/1.91  tff(c_24, plain, (![A_37]: (m1_subset_1(k2_subset_1(A_37), k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.09/1.91  tff(c_36, plain, (![A_37]: (m1_subset_1(A_37, k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_24])).
% 3.09/1.91  tff(c_231, plain, (![A_86, B_87, C_88]: (k4_subset_1(A_86, B_87, C_88)=k2_xboole_0(B_87, C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.09/1.91  tff(c_241, plain, (![A_89, B_90]: (k4_subset_1(A_89, B_90, A_89)=k2_xboole_0(B_90, A_89) | ~m1_subset_1(B_90, k1_zfmisc_1(A_89)))), inference(resolution, [status(thm)], [c_36, c_231])).
% 3.09/1.91  tff(c_250, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_241])).
% 3.09/1.91  tff(c_32, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.09/1.91  tff(c_35, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_20, c_32])).
% 3.09/1.91  tff(c_260, plain, (k2_xboole_0('#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_35])).
% 3.09/1.91  tff(c_30, plain, (![A_43, B_44]: (k4_subset_1(A_43, B_44, k3_subset_1(A_43, B_44))=k2_subset_1(A_43) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.91  tff(c_139, plain, (![A_64, B_65]: (k4_subset_1(A_64, B_65, k3_subset_1(A_64, B_65))=A_64 | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_30])).
% 3.09/1.91  tff(c_148, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_34, c_139])).
% 3.09/1.91  tff(c_93, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.09/1.91  tff(c_101, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_93])).
% 3.09/1.91  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.09/1.91  tff(c_117, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_101, c_4])).
% 3.09/1.91  tff(c_26, plain, (![A_38, B_39]: (m1_subset_1(k3_subset_1(A_38, B_39), k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.09/1.91  tff(c_364, plain, (![A_108, B_109, B_110]: (k4_subset_1(A_108, B_109, k3_subset_1(A_108, B_110))=k2_xboole_0(B_109, k3_subset_1(A_108, B_110)) | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)) | ~m1_subset_1(B_110, k1_zfmisc_1(A_108)))), inference(resolution, [status(thm)], [c_26, c_231])).
% 3.09/1.91  tff(c_385, plain, (![B_113]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_113))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_113)) | ~m1_subset_1(B_113, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_34, c_364])).
% 3.09/1.91  tff(c_396, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_385])).
% 3.09/1.91  tff(c_400, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_148, c_117, c_396])).
% 3.09/1.91  tff(c_402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_400])).
% 3.09/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.91  
% 3.09/1.91  Inference rules
% 3.09/1.91  ----------------------
% 3.09/1.91  #Ref     : 0
% 3.09/1.91  #Sup     : 98
% 3.09/1.91  #Fact    : 0
% 3.09/1.91  #Define  : 0
% 3.09/1.91  #Split   : 0
% 3.09/1.91  #Chain   : 0
% 3.09/1.91  #Close   : 0
% 3.09/1.91  
% 3.09/1.91  Ordering : KBO
% 3.09/1.91  
% 3.09/1.91  Simplification rules
% 3.09/1.91  ----------------------
% 3.09/1.91  #Subsume      : 0
% 3.09/1.91  #Demod        : 9
% 3.09/1.91  #Tautology    : 60
% 3.09/1.91  #SimpNegUnit  : 1
% 3.09/1.91  #BackRed      : 1
% 3.09/1.91  
% 3.09/1.91  #Partial instantiations: 0
% 3.09/1.91  #Strategies tried      : 1
% 3.09/1.91  
% 3.09/1.91  Timing (in seconds)
% 3.09/1.91  ----------------------
% 3.09/1.91  Preprocessing        : 0.52
% 3.09/1.91  Parsing              : 0.27
% 3.09/1.91  CNF conversion       : 0.04
% 3.09/1.91  Main loop            : 0.46
% 3.09/1.91  Inferencing          : 0.19
% 3.09/1.91  Reduction            : 0.13
% 3.09/1.91  Demodulation         : 0.10
% 3.09/1.91  BG Simplification    : 0.03
% 3.09/1.91  Subsumption          : 0.08
% 3.09/1.91  Abstraction          : 0.03
% 3.09/1.91  MUC search           : 0.00
% 3.09/1.91  Cooper               : 0.00
% 3.09/1.92  Total                : 1.03
% 3.09/1.92  Index Insertion      : 0.00
% 3.09/1.92  Index Deletion       : 0.00
% 3.09/1.92  Index Matching       : 0.00
% 3.09/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
