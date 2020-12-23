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
% DateTime   : Thu Dec  3 09:58:25 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 121 expanded)
%              Number of leaves         :   26 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 214 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k6_subset_1(k2_relat_1(A),k2_relat_1(B)),k2_relat_1(k6_subset_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_76,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k2_relat_1(A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k2_xboole_0(A_20,B_21))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_22,B_24] :
      ( r1_tarski(k2_relat_1(A_22),k2_relat_1(B_24))
      | ~ r1_tarski(A_22,B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_179,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_tarski(k4_xboole_0(A_55,C_56),B_57)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,k1_zfmisc_1(B_16))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_99,plain,(
    ! [B_41,A_42] :
      ( v1_relat_1(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(A_15)
      | ~ v1_relat_1(B_16)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_16,c_99])).

tff(c_218,plain,(
    ! [A_67,C_68,B_69] :
      ( v1_relat_1(k4_xboole_0(A_67,C_68))
      | ~ v1_relat_1(B_69)
      | ~ r1_tarski(A_67,B_69) ) ),
    inference(resolution,[status(thm)],[c_179,c_103])).

tff(c_247,plain,(
    ! [A_73,C_74,B_75] :
      ( v1_relat_1(k4_xboole_0(A_73,C_74))
      | ~ v1_relat_1(k2_xboole_0(A_73,B_75)) ) ),
    inference(resolution,[status(thm)],[c_10,c_218])).

tff(c_256,plain,(
    ! [A_20,C_74,B_21] :
      ( v1_relat_1(k4_xboole_0(A_20,C_74))
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_20,c_247])).

tff(c_257,plain,(
    ! [B_21] : ~ v1_relat_1(B_21) ),
    inference(splitLeft,[status(thm)],[c_256])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_30])).

tff(c_269,plain,(
    ! [A_20,C_74] :
      ( v1_relat_1(k4_xboole_0(A_20,C_74))
      | ~ v1_relat_1(A_20) ) ),
    inference(splitRight,[status(thm)],[c_256])).

tff(c_271,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k2_relat_1(A_78),k2_relat_1(B_79))
      | ~ r1_tarski(A_78,B_79)
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_12,plain,(
    ! [A_13,B_14] : k6_subset_1(A_13,B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ~ r1_tarski(k6_subset_1(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')),k2_relat_1(k6_subset_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_33,plain,(
    ~ r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'),k2_relat_1('#skF_2')),k2_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_28])).

tff(c_187,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k4_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_179,c_33])).

tff(c_276,plain,
    ( ~ r1_tarski('#skF_1',k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_271,c_187])).

tff(c_283,plain,
    ( ~ r1_tarski('#skF_1',k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_276])).

tff(c_285,plain,(
    ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_288,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_269,c_285])).

tff(c_292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_288])).

tff(c_294,plain,(
    v1_relat_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_377,plain,(
    ! [A_90,B_91] :
      ( k2_xboole_0(k2_relat_1(A_90),k2_relat_1(B_91)) = k2_relat_1(k2_xboole_0(A_90,B_91))
      | ~ v1_relat_1(B_91)
      | ~ v1_relat_1(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_208,plain,(
    ! [A_62,B_63,C_64] :
      ( r1_tarski(k4_xboole_0(A_62,B_63),C_64)
      | ~ r1_tarski(A_62,k2_xboole_0(B_63,C_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_216,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_xboole_0(k2_relat_1('#skF_2'),k2_relat_1(k4_xboole_0('#skF_1','#skF_2')))) ),
    inference(resolution,[status(thm)],[c_208,c_33])).

tff(c_397,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_2',k4_xboole_0('#skF_1','#skF_2'))))
    | ~ v1_relat_1(k4_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_216])).

tff(c_438,plain,(
    ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_294,c_2,c_6,c_397])).

tff(c_442,plain,
    ( ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_438])).

tff(c_445,plain,(
    ~ v1_relat_1(k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_10,c_442])).

tff(c_448,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_445])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:03:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  
% 2.69/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.40  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k6_subset_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.69/1.40  
% 2.69/1.40  %Foreground sorts:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Background operators:
% 2.69/1.40  
% 2.69/1.40  
% 2.69/1.40  %Foreground operators:
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.69/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.69/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.40  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 2.69/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.69/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.69/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.40  
% 2.69/1.42  tff(f_84, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k6_subset_1(k2_relat_1(A), k2_relat_1(B)), k2_relat_1(k6_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relat_1)).
% 2.69/1.42  tff(f_58, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_relat_1)).
% 2.69/1.42  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.69/1.42  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 2.69/1.42  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_xboole_1)).
% 2.69/1.42  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.69/1.42  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.69/1.42  tff(f_41, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 2.69/1.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.69/1.42  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.69/1.42  tff(f_76, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k2_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_relat_1)).
% 2.69/1.42  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.69/1.42  tff(c_32, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.42  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.42  tff(c_20, plain, (![A_20, B_21]: (v1_relat_1(k2_xboole_0(A_20, B_21)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.69/1.42  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.42  tff(c_22, plain, (![A_22, B_24]: (r1_tarski(k2_relat_1(A_22), k2_relat_1(B_24)) | ~r1_tarski(A_22, B_24) | ~v1_relat_1(B_24) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.42  tff(c_179, plain, (![A_55, C_56, B_57]: (r1_tarski(k4_xboole_0(A_55, C_56), B_57) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.42  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(A_15, k1_zfmisc_1(B_16)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.42  tff(c_99, plain, (![B_41, A_42]: (v1_relat_1(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.69/1.42  tff(c_103, plain, (![A_15, B_16]: (v1_relat_1(A_15) | ~v1_relat_1(B_16) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_16, c_99])).
% 2.69/1.42  tff(c_218, plain, (![A_67, C_68, B_69]: (v1_relat_1(k4_xboole_0(A_67, C_68)) | ~v1_relat_1(B_69) | ~r1_tarski(A_67, B_69))), inference(resolution, [status(thm)], [c_179, c_103])).
% 2.69/1.42  tff(c_247, plain, (![A_73, C_74, B_75]: (v1_relat_1(k4_xboole_0(A_73, C_74)) | ~v1_relat_1(k2_xboole_0(A_73, B_75)))), inference(resolution, [status(thm)], [c_10, c_218])).
% 2.69/1.42  tff(c_256, plain, (![A_20, C_74, B_21]: (v1_relat_1(k4_xboole_0(A_20, C_74)) | ~v1_relat_1(B_21) | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_20, c_247])).
% 2.69/1.42  tff(c_257, plain, (![B_21]: (~v1_relat_1(B_21))), inference(splitLeft, [status(thm)], [c_256])).
% 2.69/1.42  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_30])).
% 2.69/1.42  tff(c_269, plain, (![A_20, C_74]: (v1_relat_1(k4_xboole_0(A_20, C_74)) | ~v1_relat_1(A_20))), inference(splitRight, [status(thm)], [c_256])).
% 2.69/1.42  tff(c_271, plain, (![A_78, B_79]: (r1_tarski(k2_relat_1(A_78), k2_relat_1(B_79)) | ~r1_tarski(A_78, B_79) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.69/1.42  tff(c_12, plain, (![A_13, B_14]: (k6_subset_1(A_13, B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.42  tff(c_28, plain, (~r1_tarski(k6_subset_1(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')), k2_relat_1(k6_subset_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.69/1.42  tff(c_33, plain, (~r1_tarski(k4_xboole_0(k2_relat_1('#skF_1'), k2_relat_1('#skF_2')), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_28])).
% 2.69/1.42  tff(c_187, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_179, c_33])).
% 2.69/1.42  tff(c_276, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_271, c_187])).
% 2.69/1.42  tff(c_283, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_276])).
% 2.69/1.42  tff(c_285, plain, (~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_283])).
% 2.69/1.42  tff(c_288, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_269, c_285])).
% 2.69/1.42  tff(c_292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_288])).
% 2.69/1.42  tff(c_294, plain, (v1_relat_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_283])).
% 2.69/1.42  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.69/1.42  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.42  tff(c_377, plain, (![A_90, B_91]: (k2_xboole_0(k2_relat_1(A_90), k2_relat_1(B_91))=k2_relat_1(k2_xboole_0(A_90, B_91)) | ~v1_relat_1(B_91) | ~v1_relat_1(A_90))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.69/1.42  tff(c_208, plain, (![A_62, B_63, C_64]: (r1_tarski(k4_xboole_0(A_62, B_63), C_64) | ~r1_tarski(A_62, k2_xboole_0(B_63, C_64)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.69/1.42  tff(c_216, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_xboole_0(k2_relat_1('#skF_2'), k2_relat_1(k4_xboole_0('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_208, c_33])).
% 2.69/1.42  tff(c_397, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_2', k4_xboole_0('#skF_1', '#skF_2')))) | ~v1_relat_1(k4_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_377, c_216])).
% 2.69/1.42  tff(c_438, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_294, c_2, c_6, c_397])).
% 2.69/1.42  tff(c_442, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_22, c_438])).
% 2.69/1.42  tff(c_445, plain, (~v1_relat_1(k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_10, c_442])).
% 2.69/1.42  tff(c_448, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_20, c_445])).
% 2.69/1.42  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_448])).
% 2.69/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.42  
% 2.69/1.42  Inference rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Ref     : 0
% 2.69/1.42  #Sup     : 107
% 2.69/1.42  #Fact    : 0
% 2.69/1.42  #Define  : 0
% 2.69/1.42  #Split   : 2
% 2.69/1.42  #Chain   : 0
% 2.69/1.42  #Close   : 0
% 2.69/1.42  
% 2.69/1.42  Ordering : KBO
% 2.69/1.42  
% 2.69/1.42  Simplification rules
% 2.69/1.42  ----------------------
% 2.69/1.42  #Subsume      : 26
% 2.69/1.42  #Demod        : 25
% 2.69/1.42  #Tautology    : 30
% 2.69/1.42  #SimpNegUnit  : 10
% 2.69/1.42  #BackRed      : 2
% 2.69/1.42  
% 2.69/1.42  #Partial instantiations: 0
% 2.69/1.42  #Strategies tried      : 1
% 2.69/1.42  
% 2.69/1.42  Timing (in seconds)
% 2.69/1.42  ----------------------
% 2.69/1.42  Preprocessing        : 0.31
% 2.69/1.43  Parsing              : 0.16
% 2.69/1.43  CNF conversion       : 0.02
% 2.69/1.43  Main loop            : 0.33
% 2.69/1.43  Inferencing          : 0.11
% 2.69/1.43  Reduction            : 0.11
% 2.69/1.43  Demodulation         : 0.09
% 2.69/1.43  BG Simplification    : 0.02
% 2.69/1.43  Subsumption          : 0.07
% 2.69/1.43  Abstraction          : 0.02
% 2.69/1.43  MUC search           : 0.00
% 2.69/1.43  Cooper               : 0.00
% 2.69/1.43  Total                : 0.68
% 2.69/1.43  Index Insertion      : 0.00
% 2.69/1.43  Index Deletion       : 0.00
% 2.69/1.43  Index Matching       : 0.00
% 2.69/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
