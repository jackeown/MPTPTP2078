%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:19 EST 2020

% Result     : Theorem 3.29s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 104 expanded)
%              Number of leaves         :   32 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 146 expanded)
%              Number of equality atoms :   39 (  59 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_70,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_59,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_480,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k3_subset_1(A_57,B_58)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_489,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_480])).

tff(c_30,plain,(
    ! [A_26] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [A_17] : k1_subset_1(A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_18] : k2_subset_1(A_18) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = k2_subset_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_39,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_40,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_39])).

tff(c_16,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_619,plain,(
    ! [C_64,A_65,B_66] :
      ( r1_tarski(C_64,k3_subset_1(A_65,B_66))
      | ~ r1_tarski(B_66,k3_subset_1(A_65,C_64))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_626,plain,(
    ! [C_64,A_65] :
      ( r1_tarski(C_64,k3_subset_1(A_65,k1_xboole_0))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(A_65))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_16,c_619])).

tff(c_728,plain,(
    ! [C_71,A_72] :
      ( r1_tarski(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_40,c_626])).

tff(c_737,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_728])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_741,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_737,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_269,plain,(
    ! [A_46,B_47] : k5_xboole_0(A_46,k3_xboole_0(A_46,B_47)) = k4_xboole_0(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_797,plain,(
    ! [A_73,B_74] : k5_xboole_0(A_73,k3_xboole_0(B_74,A_73)) = k4_xboole_0(A_73,B_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_269])).

tff(c_823,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_797])).

tff(c_861,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_489,c_823])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_134,plain,(
    ! [A_36,B_37] : r1_xboole_0(k3_xboole_0(A_36,B_37),k5_xboole_0(A_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_140,plain,(
    ! [B_4,A_3] : r1_xboole_0(k3_xboole_0(B_4,A_3),k5_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_134])).

tff(c_746,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_741,c_140])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_793,plain,(
    k3_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_746,c_6])).

tff(c_927,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_861,c_793])).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_357,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_xboole_0(A_51,C_52)
      | ~ r1_xboole_0(B_53,C_52)
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1549,plain,(
    ! [A_88,B_89,A_90] :
      ( r1_xboole_0(A_88,B_89)
      | ~ r1_tarski(A_88,A_90)
      | k3_xboole_0(A_90,B_89) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_357])).

tff(c_1563,plain,(
    ! [B_91] :
      ( r1_xboole_0('#skF_2',B_91)
      | k3_xboole_0('#skF_3',B_91) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_36,c_1549])).

tff(c_1579,plain,(
    ! [B_93] :
      ( k3_xboole_0('#skF_2',B_93) = k1_xboole_0
      | k3_xboole_0('#skF_3',B_93) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1563,c_6])).

tff(c_34,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_152,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_162,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_152])).

tff(c_1619,plain,
    ( k1_xboole_0 = '#skF_2'
    | k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1579,c_162])).

tff(c_1676,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_1619])).

tff(c_1678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:17:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.29/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.51  
% 3.29/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.52  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.29/1.52  
% 3.29/1.52  %Foreground sorts:
% 3.29/1.52  
% 3.29/1.52  
% 3.29/1.52  %Background operators:
% 3.29/1.52  
% 3.29/1.52  
% 3.29/1.52  %Foreground operators:
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.29/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.29/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.29/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.29/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.29/1.52  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.29/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.29/1.52  tff('#skF_2', type, '#skF_2': $i).
% 3.29/1.52  tff('#skF_3', type, '#skF_3': $i).
% 3.29/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.29/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.29/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.29/1.52  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.29/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.29/1.52  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.29/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.29/1.52  
% 3.40/1.53  tff(f_79, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 3.40/1.53  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.40/1.53  tff(f_70, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.40/1.53  tff(f_51, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.40/1.53  tff(f_53, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.40/1.53  tff(f_59, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.40/1.53  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.40/1.53  tff(f_68, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 3.40/1.53  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.40/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.40/1.53  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.40/1.53  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.40/1.53  tff(f_35, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.40/1.53  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.40/1.53  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.40/1.53  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.53  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.53  tff(c_480, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k3_subset_1(A_57, B_58) | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.40/1.53  tff(c_489, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_480])).
% 3.40/1.53  tff(c_30, plain, (![A_26]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.40/1.53  tff(c_20, plain, (![A_17]: (k1_subset_1(A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.40/1.53  tff(c_22, plain, (![A_18]: (k2_subset_1(A_18)=A_18)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.53  tff(c_26, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=k2_subset_1(A_21))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.40/1.53  tff(c_39, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 3.40/1.53  tff(c_40, plain, (![A_21]: (k3_subset_1(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_39])).
% 3.40/1.53  tff(c_16, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.40/1.53  tff(c_619, plain, (![C_64, A_65, B_66]: (r1_tarski(C_64, k3_subset_1(A_65, B_66)) | ~r1_tarski(B_66, k3_subset_1(A_65, C_64)) | ~m1_subset_1(C_64, k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.40/1.53  tff(c_626, plain, (![C_64, A_65]: (r1_tarski(C_64, k3_subset_1(A_65, k1_xboole_0)) | ~m1_subset_1(C_64, k1_zfmisc_1(A_65)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_65)))), inference(resolution, [status(thm)], [c_16, c_619])).
% 3.40/1.53  tff(c_728, plain, (![C_71, A_72]: (r1_tarski(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_40, c_626])).
% 3.40/1.53  tff(c_737, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_728])).
% 3.40/1.53  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.53  tff(c_741, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_737, c_14])).
% 3.40/1.53  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.40/1.53  tff(c_269, plain, (![A_46, B_47]: (k5_xboole_0(A_46, k3_xboole_0(A_46, B_47))=k4_xboole_0(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.40/1.53  tff(c_797, plain, (![A_73, B_74]: (k5_xboole_0(A_73, k3_xboole_0(B_74, A_73))=k4_xboole_0(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_2, c_269])).
% 3.40/1.53  tff(c_823, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_741, c_797])).
% 3.40/1.53  tff(c_861, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_489, c_823])).
% 3.40/1.53  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.40/1.53  tff(c_134, plain, (![A_36, B_37]: (r1_xboole_0(k3_xboole_0(A_36, B_37), k5_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.53  tff(c_140, plain, (![B_4, A_3]: (r1_xboole_0(k3_xboole_0(B_4, A_3), k5_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_134])).
% 3.40/1.53  tff(c_746, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_741, c_140])).
% 3.40/1.53  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.53  tff(c_793, plain, (k3_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_746, c_6])).
% 3.40/1.53  tff(c_927, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_861, c_793])).
% 3.40/1.53  tff(c_36, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.53  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.40/1.53  tff(c_357, plain, (![A_51, C_52, B_53]: (r1_xboole_0(A_51, C_52) | ~r1_xboole_0(B_53, C_52) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.40/1.53  tff(c_1549, plain, (![A_88, B_89, A_90]: (r1_xboole_0(A_88, B_89) | ~r1_tarski(A_88, A_90) | k3_xboole_0(A_90, B_89)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_357])).
% 3.40/1.53  tff(c_1563, plain, (![B_91]: (r1_xboole_0('#skF_2', B_91) | k3_xboole_0('#skF_3', B_91)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_1549])).
% 3.40/1.53  tff(c_1579, plain, (![B_93]: (k3_xboole_0('#skF_2', B_93)=k1_xboole_0 | k3_xboole_0('#skF_3', B_93)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_1563, c_6])).
% 3.40/1.53  tff(c_34, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.53  tff(c_152, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.53  tff(c_162, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))='#skF_2'), inference(resolution, [status(thm)], [c_34, c_152])).
% 3.40/1.53  tff(c_1619, plain, (k1_xboole_0='#skF_2' | k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1579, c_162])).
% 3.40/1.53  tff(c_1676, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_927, c_1619])).
% 3.40/1.53  tff(c_1678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_1676])).
% 3.40/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.40/1.53  
% 3.40/1.53  Inference rules
% 3.40/1.53  ----------------------
% 3.40/1.53  #Ref     : 0
% 3.40/1.53  #Sup     : 426
% 3.40/1.53  #Fact    : 0
% 3.40/1.53  #Define  : 0
% 3.40/1.53  #Split   : 1
% 3.40/1.53  #Chain   : 0
% 3.40/1.53  #Close   : 0
% 3.40/1.53  
% 3.40/1.53  Ordering : KBO
% 3.40/1.53  
% 3.40/1.53  Simplification rules
% 3.40/1.53  ----------------------
% 3.40/1.53  #Subsume      : 12
% 3.40/1.53  #Demod        : 380
% 3.40/1.53  #Tautology    : 296
% 3.40/1.53  #SimpNegUnit  : 1
% 3.40/1.53  #BackRed      : 9
% 3.40/1.53  
% 3.40/1.53  #Partial instantiations: 0
% 3.40/1.53  #Strategies tried      : 1
% 3.40/1.53  
% 3.40/1.53  Timing (in seconds)
% 3.40/1.53  ----------------------
% 3.40/1.53  Preprocessing        : 0.29
% 3.40/1.53  Parsing              : 0.16
% 3.40/1.53  CNF conversion       : 0.02
% 3.40/1.53  Main loop            : 0.47
% 3.40/1.53  Inferencing          : 0.15
% 3.40/1.53  Reduction            : 0.20
% 3.40/1.53  Demodulation         : 0.16
% 3.40/1.53  BG Simplification    : 0.02
% 3.40/1.53  Subsumption          : 0.07
% 3.40/1.53  Abstraction          : 0.02
% 3.40/1.53  MUC search           : 0.00
% 3.40/1.53  Cooper               : 0.00
% 3.40/1.53  Total                : 0.80
% 3.40/1.53  Index Insertion      : 0.00
% 3.40/1.53  Index Deletion       : 0.00
% 3.40/1.53  Index Matching       : 0.00
% 3.40/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
