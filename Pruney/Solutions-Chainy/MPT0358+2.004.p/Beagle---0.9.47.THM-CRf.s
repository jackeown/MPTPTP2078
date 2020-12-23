%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:00 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 125 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 163 expanded)
%              Number of equality atoms :   39 (  78 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_47,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_66,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_20,plain,(
    ! [A_15] : k1_subset_1(A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_40,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_43,plain,
    ( r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2'))
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_40])).

tff(c_145,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_43])).

tff(c_12,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_149,plain,(
    ! [A_11] : r1_tarski('#skF_2',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_12])).

tff(c_34,plain,
    ( k1_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_34])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_145,c_44])).

tff(c_195,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_194,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_43])).

tff(c_196,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_203,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_194,c_196])).

tff(c_414,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k4_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_434,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k5_xboole_0('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_414])).

tff(c_449,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_434])).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_588,plain,(
    ! [A_67,B_68] :
      ( k4_xboole_0(A_67,B_68) = k3_subset_1(A_67,B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_595,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_588])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ! [A_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = k2_subset_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_41,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_subset_1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_42,plain,(
    ! [A_19] : k3_subset_1(A_19,k1_xboole_0) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_41])).

tff(c_733,plain,(
    ! [C_73,A_74,B_75] :
      ( r1_tarski(C_73,k3_subset_1(A_74,B_75))
      | ~ r1_tarski(B_75,k3_subset_1(A_74,C_73))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_740,plain,(
    ! [C_73,A_74] :
      ( r1_tarski(C_73,k3_subset_1(A_74,k1_xboole_0))
      | ~ m1_subset_1(C_73,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_74)) ) ),
    inference(resolution,[status(thm)],[c_12,c_733])).

tff(c_753,plain,(
    ! [C_76,A_77] :
      ( r1_tarski(C_76,A_77)
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_77)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42,c_740])).

tff(c_760,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_753])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_766,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_760,c_10])).

tff(c_786,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_766])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_798,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_8])).

tff(c_804,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_595,c_798])).

tff(c_269,plain,(
    ! [A_52,B_53] : r1_xboole_0(k3_xboole_0(A_52,B_53),k5_xboole_0(A_52,B_53)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_806,plain,(
    ! [A_78,B_79] : r1_xboole_0(k3_xboole_0(A_78,B_79),k5_xboole_0(B_79,A_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_269])).

tff(c_815,plain,(
    r1_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_766,c_806])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k4_xboole_0(A_12,B_13) = A_12
      | ~ r1_xboole_0(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_868,plain,(
    k4_xboole_0('#skF_2',k5_xboole_0('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_815,c_14])).

tff(c_892,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_804,c_868])).

tff(c_893,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_195,c_892])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:49:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.37  
% 2.67/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.37  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.67/1.37  
% 2.67/1.37  %Foreground sorts:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Background operators:
% 2.67/1.37  
% 2.67/1.37  
% 2.67/1.37  %Foreground operators:
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.67/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.67/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.67/1.37  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.67/1.37  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.67/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.67/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.67/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.67/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.67/1.37  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 2.67/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.67/1.37  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.67/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.67/1.37  
% 2.67/1.39  tff(f_47, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 2.67/1.39  tff(f_73, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 2.67/1.39  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.67/1.39  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.67/1.39  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.67/1.39  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.67/1.39  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.67/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.67/1.39  tff(f_66, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.67/1.39  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.67/1.39  tff(f_55, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 2.67/1.39  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 2.67/1.39  tff(f_31, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 2.67/1.39  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.67/1.39  tff(c_20, plain, (![A_15]: (k1_subset_1(A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.67/1.39  tff(c_40, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.39  tff(c_43, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2')) | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_40])).
% 2.67/1.39  tff(c_145, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_43])).
% 2.67/1.39  tff(c_12, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.67/1.39  tff(c_149, plain, (![A_11]: (r1_tarski('#skF_2', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_12])).
% 2.67/1.39  tff(c_34, plain, (k1_subset_1('#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.39  tff(c_44, plain, (k1_xboole_0!='#skF_2' | ~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_34])).
% 2.67/1.39  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_145, c_44])).
% 2.67/1.39  tff(c_195, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_43])).
% 2.67/1.39  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.67/1.39  tff(c_194, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_43])).
% 2.67/1.39  tff(c_196, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.39  tff(c_203, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_194, c_196])).
% 2.67/1.39  tff(c_414, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k4_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.39  tff(c_434, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k5_xboole_0('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_203, c_414])).
% 2.67/1.39  tff(c_449, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_434])).
% 2.67/1.39  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.67/1.39  tff(c_588, plain, (![A_67, B_68]: (k4_xboole_0(A_67, B_68)=k3_subset_1(A_67, B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_67)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.67/1.39  tff(c_595, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_588])).
% 2.67/1.39  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.67/1.39  tff(c_30, plain, (![A_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.67/1.39  tff(c_22, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.67/1.39  tff(c_26, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=k2_subset_1(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.67/1.39  tff(c_41, plain, (![A_19]: (k3_subset_1(A_19, k1_subset_1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 2.67/1.39  tff(c_42, plain, (![A_19]: (k3_subset_1(A_19, k1_xboole_0)=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_41])).
% 2.67/1.39  tff(c_733, plain, (![C_73, A_74, B_75]: (r1_tarski(C_73, k3_subset_1(A_74, B_75)) | ~r1_tarski(B_75, k3_subset_1(A_74, C_73)) | ~m1_subset_1(C_73, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.67/1.39  tff(c_740, plain, (![C_73, A_74]: (r1_tarski(C_73, k3_subset_1(A_74, k1_xboole_0)) | ~m1_subset_1(C_73, k1_zfmisc_1(A_74)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_74)))), inference(resolution, [status(thm)], [c_12, c_733])).
% 2.67/1.39  tff(c_753, plain, (![C_76, A_77]: (r1_tarski(C_76, A_77) | ~m1_subset_1(C_76, k1_zfmisc_1(A_77)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42, c_740])).
% 2.67/1.39  tff(c_760, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_32, c_753])).
% 2.67/1.39  tff(c_10, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.67/1.39  tff(c_766, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_760, c_10])).
% 2.67/1.39  tff(c_786, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2, c_766])).
% 2.67/1.39  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.67/1.39  tff(c_798, plain, (k5_xboole_0('#skF_1', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_786, c_8])).
% 2.67/1.39  tff(c_804, plain, (k5_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_595, c_798])).
% 2.67/1.39  tff(c_269, plain, (![A_52, B_53]: (r1_xboole_0(k3_xboole_0(A_52, B_53), k5_xboole_0(A_52, B_53)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.67/1.39  tff(c_806, plain, (![A_78, B_79]: (r1_xboole_0(k3_xboole_0(A_78, B_79), k5_xboole_0(B_79, A_78)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_269])).
% 2.67/1.39  tff(c_815, plain, (r1_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_766, c_806])).
% 2.67/1.39  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, B_13)=A_12 | ~r1_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.67/1.39  tff(c_868, plain, (k4_xboole_0('#skF_2', k5_xboole_0('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_815, c_14])).
% 2.67/1.39  tff(c_892, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_449, c_804, c_868])).
% 2.67/1.39  tff(c_893, plain, $false, inference(negUnitSimplification, [status(thm)], [c_195, c_892])).
% 2.67/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.67/1.39  
% 2.67/1.39  Inference rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Ref     : 0
% 2.67/1.39  #Sup     : 201
% 2.67/1.39  #Fact    : 0
% 2.67/1.39  #Define  : 0
% 2.67/1.39  #Split   : 1
% 2.67/1.39  #Chain   : 0
% 2.67/1.39  #Close   : 0
% 2.67/1.39  
% 2.67/1.39  Ordering : KBO
% 2.67/1.39  
% 2.67/1.39  Simplification rules
% 2.67/1.39  ----------------------
% 2.67/1.39  #Subsume      : 1
% 2.67/1.39  #Demod        : 138
% 2.67/1.39  #Tautology    : 171
% 2.67/1.39  #SimpNegUnit  : 1
% 2.67/1.39  #BackRed      : 11
% 2.67/1.39  
% 2.67/1.39  #Partial instantiations: 0
% 2.67/1.39  #Strategies tried      : 1
% 2.67/1.39  
% 2.67/1.39  Timing (in seconds)
% 2.67/1.39  ----------------------
% 2.67/1.39  Preprocessing        : 0.31
% 2.67/1.39  Parsing              : 0.17
% 2.67/1.39  CNF conversion       : 0.02
% 2.67/1.39  Main loop            : 0.33
% 2.67/1.39  Inferencing          : 0.11
% 2.67/1.39  Reduction            : 0.12
% 2.67/1.39  Demodulation         : 0.10
% 2.67/1.39  BG Simplification    : 0.02
% 2.67/1.39  Subsumption          : 0.05
% 2.67/1.39  Abstraction          : 0.02
% 2.67/1.39  MUC search           : 0.00
% 2.67/1.39  Cooper               : 0.00
% 2.67/1.39  Total                : 0.67
% 2.67/1.39  Index Insertion      : 0.00
% 2.67/1.39  Index Deletion       : 0.00
% 2.67/1.39  Index Matching       : 0.00
% 2.67/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
