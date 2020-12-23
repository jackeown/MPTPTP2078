%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:04 EST 2020

% Result     : Theorem 8.35s
% Output     : CNFRefutation 8.35s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 134 expanded)
%              Number of leaves         :   31 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  109 ( 220 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => r1_tarski(k3_relat_1(C),k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_26,plain,(
    ! [A_23,B_24] : v1_relat_1(k2_zfmisc_1(A_23,B_24)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_104,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_107,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_104])).

tff(c_110,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_107])).

tff(c_317,plain,(
    ! [C_64,B_65,A_66] :
      ( v5_relat_1(C_64,B_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_321,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_317])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_37,plain,(
    ! [B_32,A_33] : k2_xboole_0(B_32,A_33) = k2_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [A_33,B_32] : r1_tarski(A_33,k2_xboole_0(B_32,A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_8])).

tff(c_95,plain,(
    ! [A_38,B_39] :
      ( k2_xboole_0(A_38,B_39) = B_39
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_890,plain,(
    ! [A_100,B_101] : k2_xboole_0(A_100,k2_xboole_0(B_101,A_100)) = k2_xboole_0(B_101,A_100) ),
    inference(resolution,[status(thm)],[c_52,c_95])).

tff(c_1009,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k2_xboole_0(A_1,B_2)) = k2_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_890])).

tff(c_233,plain,(
    ! [B_56,A_57] :
      ( r1_tarski(k2_relat_1(B_56),A_57)
      | ~ v5_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_778,plain,(
    ! [B_98,A_99] :
      ( k2_xboole_0(k2_relat_1(B_98),A_99) = A_99
      | ~ v5_relat_1(B_98,A_99)
      | ~ v1_relat_1(B_98) ) ),
    inference(resolution,[status(thm)],[c_233,c_6])).

tff(c_111,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(k2_xboole_0(A_42,B_44),C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_127,plain,(
    ! [A_42,B_44,B_9] : r1_tarski(A_42,k2_xboole_0(k2_xboole_0(A_42,B_44),B_9)) ),
    inference(resolution,[status(thm)],[c_8,c_111])).

tff(c_10413,plain,(
    ! [B_276,A_277,B_278] :
      ( r1_tarski(k2_relat_1(B_276),k2_xboole_0(A_277,B_278))
      | ~ v5_relat_1(B_276,A_277)
      | ~ v1_relat_1(B_276) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_127])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( v5_relat_1(B_21,A_20)
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_11161,plain,(
    ! [B_285,A_286,B_287] :
      ( v5_relat_1(B_285,k2_xboole_0(A_286,B_287))
      | ~ v5_relat_1(B_285,A_286)
      | ~ v1_relat_1(B_285) ) ),
    inference(resolution,[status(thm)],[c_10413,c_20])).

tff(c_17200,plain,(
    ! [B_347,B_348,A_349] :
      ( v5_relat_1(B_347,k2_xboole_0(B_348,A_349))
      | ~ v5_relat_1(B_347,A_349)
      | ~ v1_relat_1(B_347) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1009,c_11161])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_544,plain,(
    ! [C_83,A_84,B_85] :
      ( v4_relat_1(C_83,A_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_548,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_544])).

tff(c_331,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k1_relat_1(B_69),A_70)
      | ~ v4_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1449,plain,(
    ! [B_109,A_110] :
      ( k2_xboole_0(k1_relat_1(B_109),A_110) = A_110
      | ~ v4_relat_1(B_109,A_110)
      | ~ v1_relat_1(B_109) ) ),
    inference(resolution,[status(thm)],[c_331,c_6])).

tff(c_6226,plain,(
    ! [B_206,A_207,B_208] :
      ( r1_tarski(k1_relat_1(B_206),k2_xboole_0(A_207,B_208))
      | ~ v4_relat_1(B_206,A_207)
      | ~ v1_relat_1(B_206) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1449,c_127])).

tff(c_24,plain,(
    ! [A_22] :
      ( k2_xboole_0(k1_relat_1(A_22),k2_relat_1(A_22)) = k3_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_737,plain,(
    ! [A_92,C_93,B_94] :
      ( r1_tarski(k2_xboole_0(A_92,C_93),B_94)
      | ~ r1_tarski(C_93,B_94)
      | ~ r1_tarski(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2856,plain,(
    ! [A_146,B_147] :
      ( r1_tarski(k3_relat_1(A_146),B_147)
      | ~ r1_tarski(k2_relat_1(A_146),B_147)
      | ~ r1_tarski(k1_relat_1(A_146),B_147)
      | ~ v1_relat_1(A_146) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_737])).

tff(c_32,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2867,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2856,c_32])).

tff(c_2873,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2867])).

tff(c_3345,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_2873])).

tff(c_6229,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6226,c_3345])).

tff(c_6301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_548,c_6229])).

tff(c_6302,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_2873])).

tff(c_6306,plain,
    ( ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_6302])).

tff(c_6309,plain,(
    ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_6306])).

tff(c_17203,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_17200,c_6309])).

tff(c_17293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_321,c_17203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:42:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.35/3.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/3.07  
% 8.35/3.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/3.07  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 8.35/3.07  
% 8.35/3.07  %Foreground sorts:
% 8.35/3.07  
% 8.35/3.07  
% 8.35/3.07  %Background operators:
% 8.35/3.07  
% 8.35/3.07  
% 8.35/3.07  %Foreground operators:
% 8.35/3.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.35/3.07  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 8.35/3.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.35/3.07  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.35/3.07  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.35/3.07  tff('#skF_2', type, '#skF_2': $i).
% 8.35/3.07  tff('#skF_3', type, '#skF_3': $i).
% 8.35/3.07  tff('#skF_1', type, '#skF_1': $i).
% 8.35/3.07  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.35/3.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.35/3.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.35/3.07  tff(k3_tarski, type, k3_tarski: $i > $i).
% 8.35/3.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.35/3.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.35/3.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.35/3.07  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.35/3.07  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.35/3.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.35/3.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.35/3.07  
% 8.35/3.08  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.35/3.08  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 8.35/3.08  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.35/3.08  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.35/3.08  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 8.35/3.08  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 8.35/3.08  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 8.35/3.08  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 8.35/3.08  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 8.35/3.08  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 8.35/3.08  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 8.35/3.08  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 8.35/3.08  tff(c_26, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 8.35/3.08  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.35/3.08  tff(c_104, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 8.35/3.08  tff(c_107, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_104])).
% 8.35/3.08  tff(c_110, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_107])).
% 8.35/3.08  tff(c_317, plain, (![C_64, B_65, A_66]: (v5_relat_1(C_64, B_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.35/3.08  tff(c_321, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_317])).
% 8.35/3.08  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.35/3.08  tff(c_37, plain, (![B_32, A_33]: (k2_xboole_0(B_32, A_33)=k2_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 8.35/3.08  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 8.35/3.08  tff(c_52, plain, (![A_33, B_32]: (r1_tarski(A_33, k2_xboole_0(B_32, A_33)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_8])).
% 8.35/3.08  tff(c_95, plain, (![A_38, B_39]: (k2_xboole_0(A_38, B_39)=B_39 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.35/3.08  tff(c_890, plain, (![A_100, B_101]: (k2_xboole_0(A_100, k2_xboole_0(B_101, A_100))=k2_xboole_0(B_101, A_100))), inference(resolution, [status(thm)], [c_52, c_95])).
% 8.35/3.08  tff(c_1009, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k2_xboole_0(A_1, B_2))=k2_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_890])).
% 8.35/3.08  tff(c_233, plain, (![B_56, A_57]: (r1_tarski(k2_relat_1(B_56), A_57) | ~v5_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.35/3.08  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.35/3.08  tff(c_778, plain, (![B_98, A_99]: (k2_xboole_0(k2_relat_1(B_98), A_99)=A_99 | ~v5_relat_1(B_98, A_99) | ~v1_relat_1(B_98))), inference(resolution, [status(thm)], [c_233, c_6])).
% 8.35/3.08  tff(c_111, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(k2_xboole_0(A_42, B_44), C_43))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.35/3.08  tff(c_127, plain, (![A_42, B_44, B_9]: (r1_tarski(A_42, k2_xboole_0(k2_xboole_0(A_42, B_44), B_9)))), inference(resolution, [status(thm)], [c_8, c_111])).
% 8.35/3.08  tff(c_10413, plain, (![B_276, A_277, B_278]: (r1_tarski(k2_relat_1(B_276), k2_xboole_0(A_277, B_278)) | ~v5_relat_1(B_276, A_277) | ~v1_relat_1(B_276))), inference(superposition, [status(thm), theory('equality')], [c_778, c_127])).
% 8.35/3.08  tff(c_20, plain, (![B_21, A_20]: (v5_relat_1(B_21, A_20) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.35/3.08  tff(c_11161, plain, (![B_285, A_286, B_287]: (v5_relat_1(B_285, k2_xboole_0(A_286, B_287)) | ~v5_relat_1(B_285, A_286) | ~v1_relat_1(B_285))), inference(resolution, [status(thm)], [c_10413, c_20])).
% 8.35/3.08  tff(c_17200, plain, (![B_347, B_348, A_349]: (v5_relat_1(B_347, k2_xboole_0(B_348, A_349)) | ~v5_relat_1(B_347, A_349) | ~v1_relat_1(B_347))), inference(superposition, [status(thm), theory('equality')], [c_1009, c_11161])).
% 8.35/3.08  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.35/3.08  tff(c_544, plain, (![C_83, A_84, B_85]: (v4_relat_1(C_83, A_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 8.35/3.08  tff(c_548, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_544])).
% 8.35/3.08  tff(c_331, plain, (![B_69, A_70]: (r1_tarski(k1_relat_1(B_69), A_70) | ~v4_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.35/3.08  tff(c_1449, plain, (![B_109, A_110]: (k2_xboole_0(k1_relat_1(B_109), A_110)=A_110 | ~v4_relat_1(B_109, A_110) | ~v1_relat_1(B_109))), inference(resolution, [status(thm)], [c_331, c_6])).
% 8.35/3.08  tff(c_6226, plain, (![B_206, A_207, B_208]: (r1_tarski(k1_relat_1(B_206), k2_xboole_0(A_207, B_208)) | ~v4_relat_1(B_206, A_207) | ~v1_relat_1(B_206))), inference(superposition, [status(thm), theory('equality')], [c_1449, c_127])).
% 8.35/3.08  tff(c_24, plain, (![A_22]: (k2_xboole_0(k1_relat_1(A_22), k2_relat_1(A_22))=k3_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.35/3.08  tff(c_737, plain, (![A_92, C_93, B_94]: (r1_tarski(k2_xboole_0(A_92, C_93), B_94) | ~r1_tarski(C_93, B_94) | ~r1_tarski(A_92, B_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.35/3.08  tff(c_2856, plain, (![A_146, B_147]: (r1_tarski(k3_relat_1(A_146), B_147) | ~r1_tarski(k2_relat_1(A_146), B_147) | ~r1_tarski(k1_relat_1(A_146), B_147) | ~v1_relat_1(A_146))), inference(superposition, [status(thm), theory('equality')], [c_24, c_737])).
% 8.35/3.08  tff(c_32, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 8.35/3.08  tff(c_2867, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2856, c_32])).
% 8.35/3.08  tff(c_2873, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_2867])).
% 8.35/3.08  tff(c_3345, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_2873])).
% 8.35/3.08  tff(c_6229, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6226, c_3345])).
% 8.35/3.08  tff(c_6301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_548, c_6229])).
% 8.35/3.08  tff(c_6302, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_2873])).
% 8.35/3.08  tff(c_6306, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_6302])).
% 8.35/3.08  tff(c_6309, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_6306])).
% 8.35/3.08  tff(c_17203, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_17200, c_6309])).
% 8.35/3.08  tff(c_17293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_321, c_17203])).
% 8.35/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.35/3.08  
% 8.35/3.08  Inference rules
% 8.35/3.08  ----------------------
% 8.35/3.08  #Ref     : 0
% 8.35/3.08  #Sup     : 4241
% 8.35/3.08  #Fact    : 0
% 8.35/3.08  #Define  : 0
% 8.35/3.08  #Split   : 1
% 8.35/3.08  #Chain   : 0
% 8.35/3.08  #Close   : 0
% 8.35/3.08  
% 8.35/3.08  Ordering : KBO
% 8.35/3.08  
% 8.35/3.08  Simplification rules
% 8.35/3.08  ----------------------
% 8.35/3.08  #Subsume      : 893
% 8.35/3.08  #Demod        : 2714
% 8.35/3.08  #Tautology    : 2069
% 8.35/3.08  #SimpNegUnit  : 0
% 8.35/3.08  #BackRed      : 0
% 8.35/3.08  
% 8.35/3.08  #Partial instantiations: 0
% 8.35/3.08  #Strategies tried      : 1
% 8.35/3.08  
% 8.35/3.08  Timing (in seconds)
% 8.35/3.08  ----------------------
% 8.35/3.08  Preprocessing        : 0.31
% 8.35/3.08  Parsing              : 0.18
% 8.35/3.08  CNF conversion       : 0.02
% 8.35/3.08  Main loop            : 1.99
% 8.35/3.08  Inferencing          : 0.52
% 8.35/3.08  Reduction            : 0.94
% 8.35/3.08  Demodulation         : 0.80
% 8.35/3.08  BG Simplification    : 0.05
% 8.35/3.08  Subsumption          : 0.36
% 8.35/3.09  Abstraction          : 0.08
% 8.35/3.09  MUC search           : 0.00
% 8.35/3.09  Cooper               : 0.00
% 8.35/3.09  Total                : 2.33
% 8.35/3.09  Index Insertion      : 0.00
% 8.35/3.09  Index Deletion       : 0.00
% 8.35/3.09  Index Matching       : 0.00
% 8.35/3.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
