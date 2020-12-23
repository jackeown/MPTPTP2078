%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:32 EST 2020

% Result     : Theorem 23.94s
% Output     : CNFRefutation 23.94s
% Verified   : 
% Statistics : Number of formulae       :   65 (  77 expanded)
%              Number of leaves         :   30 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   84 ( 111 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => r1_tarski(k3_subset_1(A,B),k3_subset_1(A,k9_subset_1(A,B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_subset_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(c_12,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [A_24] : ~ v1_xboole_0(k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_139,plain,(
    ! [B_48,A_49] :
      ( r2_hidden(B_48,A_49)
      | ~ m1_subset_1(B_48,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_14,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,(
    ! [B_48,A_15] :
      ( r1_tarski(B_48,A_15)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_139,c_14])).

tff(c_148,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(B_50,A_51)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_143])).

tff(c_161,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_148])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_169,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_161,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_217,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,k2_xboole_0(C_57,B_58))
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_607,plain,(
    ! [A_86,A_87,B_88] :
      ( r1_tarski(A_86,k2_xboole_0(A_87,B_88))
      | ~ r1_tarski(A_86,A_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_646,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,'#skF_3')
      | ~ r1_tarski(A_86,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_607])).

tff(c_16,plain,(
    ! [C_19,A_15] :
      ( r2_hidden(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_196,plain,(
    ! [B_52,A_53] :
      ( m1_subset_1(B_52,A_53)
      | ~ r2_hidden(B_52,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_202,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(resolution,[status(thm)],[c_16,c_196])).

tff(c_206,plain,(
    ! [C_19,A_15] :
      ( m1_subset_1(C_19,k1_zfmisc_1(A_15))
      | ~ r1_tarski(C_19,A_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_202])).

tff(c_403,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = k3_subset_1(A_73,B_74)
      | ~ m1_subset_1(B_74,k1_zfmisc_1(A_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3840,plain,(
    ! [A_247,C_248] :
      ( k4_xboole_0(A_247,C_248) = k3_subset_1(A_247,C_248)
      | ~ r1_tarski(C_248,A_247) ) ),
    inference(resolution,[status(thm)],[c_206,c_403])).

tff(c_11480,plain,(
    ! [A_406] :
      ( k4_xboole_0('#skF_3',A_406) = k3_subset_1('#skF_3',A_406)
      | ~ r1_tarski(A_406,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_646,c_3840])).

tff(c_55555,plain,(
    ! [B_1013] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_4',B_1013)) = k3_subset_1('#skF_3',k4_xboole_0('#skF_4',B_1013)) ),
    inference(resolution,[status(thm)],[c_10,c_11480])).

tff(c_420,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_403])).

tff(c_508,plain,(
    ! [C_75,B_76,A_77] :
      ( r1_tarski(k4_xboole_0(C_75,B_76),k4_xboole_0(C_75,A_77))
      | ~ r1_tarski(A_77,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_514,plain,(
    ! [A_77] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k4_xboole_0('#skF_3',A_77))
      | ~ r1_tarski(A_77,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_508])).

tff(c_55770,plain,(
    ! [B_1013] :
      ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k4_xboole_0('#skF_4',B_1013)))
      | ~ r1_tarski(k4_xboole_0('#skF_4',B_1013),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55555,c_514])).

tff(c_56953,plain,(
    ! [B_1028] : r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k4_xboole_0('#skF_4',B_1028))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_55770])).

tff(c_56980,plain,(
    ! [B_14] : r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4',B_14))) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_56953])).

tff(c_42,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_546,plain,(
    ! [A_78,B_79,C_80] :
      ( k9_subset_1(A_78,B_79,C_80) = k3_xboole_0(B_79,C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_558,plain,(
    ! [B_79] : k9_subset_1('#skF_3',B_79,'#skF_5') = k3_xboole_0(B_79,'#skF_5') ),
    inference(resolution,[status(thm)],[c_42,c_546])).

tff(c_40,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k9_subset_1('#skF_3','#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_563,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),k3_subset_1('#skF_3',k3_xboole_0('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_558,c_40])).

tff(c_57215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56980,c_563])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 23.94/15.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.94/15.08  
% 23.94/15.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.94/15.08  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k9_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 23.94/15.08  
% 23.94/15.08  %Foreground sorts:
% 23.94/15.08  
% 23.94/15.08  
% 23.94/15.08  %Background operators:
% 23.94/15.08  
% 23.94/15.08  
% 23.94/15.08  %Foreground operators:
% 23.94/15.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.94/15.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 23.94/15.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 23.94/15.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.94/15.08  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 23.94/15.08  tff('#skF_5', type, '#skF_5': $i).
% 23.94/15.08  tff('#skF_3', type, '#skF_3': $i).
% 23.94/15.08  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.94/15.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.94/15.08  tff('#skF_4', type, '#skF_4': $i).
% 23.94/15.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.94/15.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 23.94/15.08  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 23.94/15.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 23.94/15.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 23.94/15.08  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.94/15.08  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 23.94/15.08  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.94/15.08  
% 23.94/15.09  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 23.94/15.09  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 23.94/15.09  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => r1_tarski(k3_subset_1(A, B), k3_subset_1(A, k9_subset_1(A, B, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_subset_1)).
% 23.94/15.09  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 23.94/15.09  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 23.94/15.09  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 23.94/15.09  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 23.94/15.09  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 23.94/15.09  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 23.94/15.09  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 23.94/15.09  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 23.94/15.09  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 23.94/15.09  tff(c_12, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 23.94/15.09  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 23.94/15.09  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.94/15.09  tff(c_36, plain, (![A_24]: (~v1_xboole_0(k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 23.94/15.09  tff(c_139, plain, (![B_48, A_49]: (r2_hidden(B_48, A_49) | ~m1_subset_1(B_48, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.94/15.09  tff(c_14, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 23.94/15.09  tff(c_143, plain, (![B_48, A_15]: (r1_tarski(B_48, A_15) | ~m1_subset_1(B_48, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_139, c_14])).
% 23.94/15.09  tff(c_148, plain, (![B_50, A_51]: (r1_tarski(B_50, A_51) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)))), inference(negUnitSimplification, [status(thm)], [c_36, c_143])).
% 23.94/15.09  tff(c_161, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_148])).
% 23.94/15.09  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 23.94/15.09  tff(c_169, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_161, c_6])).
% 23.94/15.09  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 23.94/15.09  tff(c_217, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, k2_xboole_0(C_57, B_58)) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 23.94/15.09  tff(c_607, plain, (![A_86, A_87, B_88]: (r1_tarski(A_86, k2_xboole_0(A_87, B_88)) | ~r1_tarski(A_86, A_87))), inference(superposition, [status(thm), theory('equality')], [c_2, c_217])).
% 23.94/15.09  tff(c_646, plain, (![A_86]: (r1_tarski(A_86, '#skF_3') | ~r1_tarski(A_86, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_607])).
% 23.94/15.09  tff(c_16, plain, (![C_19, A_15]: (r2_hidden(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 23.94/15.09  tff(c_196, plain, (![B_52, A_53]: (m1_subset_1(B_52, A_53) | ~r2_hidden(B_52, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 23.94/15.09  tff(c_202, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(resolution, [status(thm)], [c_16, c_196])).
% 23.94/15.09  tff(c_206, plain, (![C_19, A_15]: (m1_subset_1(C_19, k1_zfmisc_1(A_15)) | ~r1_tarski(C_19, A_15))), inference(negUnitSimplification, [status(thm)], [c_36, c_202])).
% 23.94/15.09  tff(c_403, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=k3_subset_1(A_73, B_74) | ~m1_subset_1(B_74, k1_zfmisc_1(A_73)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 23.94/15.09  tff(c_3840, plain, (![A_247, C_248]: (k4_xboole_0(A_247, C_248)=k3_subset_1(A_247, C_248) | ~r1_tarski(C_248, A_247))), inference(resolution, [status(thm)], [c_206, c_403])).
% 23.94/15.09  tff(c_11480, plain, (![A_406]: (k4_xboole_0('#skF_3', A_406)=k3_subset_1('#skF_3', A_406) | ~r1_tarski(A_406, '#skF_4'))), inference(resolution, [status(thm)], [c_646, c_3840])).
% 23.94/15.09  tff(c_55555, plain, (![B_1013]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_4', B_1013))=k3_subset_1('#skF_3', k4_xboole_0('#skF_4', B_1013)))), inference(resolution, [status(thm)], [c_10, c_11480])).
% 23.94/15.09  tff(c_420, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_403])).
% 23.94/15.09  tff(c_508, plain, (![C_75, B_76, A_77]: (r1_tarski(k4_xboole_0(C_75, B_76), k4_xboole_0(C_75, A_77)) | ~r1_tarski(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_39])).
% 23.94/15.09  tff(c_514, plain, (![A_77]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k4_xboole_0('#skF_3', A_77)) | ~r1_tarski(A_77, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_420, c_508])).
% 23.94/15.09  tff(c_55770, plain, (![B_1013]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k4_xboole_0('#skF_4', B_1013))) | ~r1_tarski(k4_xboole_0('#skF_4', B_1013), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_55555, c_514])).
% 23.94/15.09  tff(c_56953, plain, (![B_1028]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k4_xboole_0('#skF_4', B_1028))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_55770])).
% 23.94/15.09  tff(c_56980, plain, (![B_14]: (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', B_14))))), inference(superposition, [status(thm), theory('equality')], [c_12, c_56953])).
% 23.94/15.09  tff(c_42, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.94/15.09  tff(c_546, plain, (![A_78, B_79, C_80]: (k9_subset_1(A_78, B_79, C_80)=k3_xboole_0(B_79, C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 23.94/15.09  tff(c_558, plain, (![B_79]: (k9_subset_1('#skF_3', B_79, '#skF_5')=k3_xboole_0(B_79, '#skF_5'))), inference(resolution, [status(thm)], [c_42, c_546])).
% 23.94/15.09  tff(c_40, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k9_subset_1('#skF_3', '#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 23.94/15.09  tff(c_563, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), k3_subset_1('#skF_3', k3_xboole_0('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_558, c_40])).
% 23.94/15.09  tff(c_57215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56980, c_563])).
% 23.94/15.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.94/15.09  
% 23.94/15.09  Inference rules
% 23.94/15.09  ----------------------
% 23.94/15.09  #Ref     : 0
% 23.94/15.09  #Sup     : 14569
% 23.94/15.09  #Fact    : 0
% 23.94/15.09  #Define  : 0
% 23.94/15.09  #Split   : 22
% 23.94/15.09  #Chain   : 0
% 23.94/15.09  #Close   : 0
% 23.94/15.09  
% 23.94/15.09  Ordering : KBO
% 23.94/15.09  
% 23.94/15.09  Simplification rules
% 23.94/15.09  ----------------------
% 23.94/15.09  #Subsume      : 2385
% 23.94/15.09  #Demod        : 14046
% 23.94/15.09  #Tautology    : 3307
% 23.94/15.09  #SimpNegUnit  : 25
% 23.94/15.09  #BackRed      : 22
% 23.94/15.09  
% 23.94/15.09  #Partial instantiations: 0
% 23.94/15.09  #Strategies tried      : 1
% 23.94/15.09  
% 23.94/15.09  Timing (in seconds)
% 23.94/15.09  ----------------------
% 23.94/15.09  Preprocessing        : 0.31
% 23.94/15.09  Parsing              : 0.16
% 23.94/15.09  CNF conversion       : 0.02
% 23.94/15.09  Main loop            : 14.00
% 23.94/15.09  Inferencing          : 1.61
% 23.94/15.09  Reduction            : 7.93
% 23.94/15.09  Demodulation         : 7.11
% 23.94/15.09  BG Simplification    : 0.23
% 23.94/15.09  Subsumption          : 3.57
% 23.94/15.09  Abstraction          : 0.31
% 23.94/15.09  MUC search           : 0.00
% 23.94/15.09  Cooper               : 0.00
% 23.94/15.09  Total                : 14.34
% 23.94/15.09  Index Insertion      : 0.00
% 23.94/15.09  Index Deletion       : 0.00
% 23.94/15.09  Index Matching       : 0.00
% 23.94/15.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
