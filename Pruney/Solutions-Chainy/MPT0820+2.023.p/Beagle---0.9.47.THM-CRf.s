%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:03 EST 2020

% Result     : Theorem 7.49s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 131 expanded)
%              Number of leaves         :   32 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  108 ( 215 expanded)
%              Number of equality atoms :   13 (  18 expanded)
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

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_45,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
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

tff(f_41,axiom,(
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

tff(c_208,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_211,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_34,c_208])).

tff(c_214,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_211])).

tff(c_479,plain,(
    ! [C_74,B_75,A_76] :
      ( v5_relat_1(C_74,B_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_76,B_75))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_483,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_479])).

tff(c_10,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_75,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    ! [B_38,A_39] : k3_tarski(k2_tarski(B_38,A_39)) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_75])).

tff(c_12,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_96,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_12])).

tff(c_782,plain,(
    ! [B_93,A_94] :
      ( r1_tarski(k2_relat_1(B_93),A_94)
      | ~ v5_relat_1(B_93,A_94)
      | ~ v1_relat_1(B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k2_xboole_0(A_4,B_5) = B_5
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2231,plain,(
    ! [B_134,A_135] :
      ( k2_xboole_0(k2_relat_1(B_134),A_135) = A_135
      | ~ v5_relat_1(B_134,A_135)
      | ~ v1_relat_1(B_134) ) ),
    inference(resolution,[status(thm)],[c_782,c_4])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_152,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_tarski(A_42,C_43)
      | ~ r1_tarski(k2_xboole_0(A_42,B_44),C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_163,plain,(
    ! [A_42,B_44,B_7] : r1_tarski(A_42,k2_xboole_0(k2_xboole_0(A_42,B_44),B_7)) ),
    inference(resolution,[status(thm)],[c_6,c_152])).

tff(c_5963,plain,(
    ! [B_215,A_216,B_217] :
      ( r1_tarski(k2_relat_1(B_215),k2_xboole_0(A_216,B_217))
      | ~ v5_relat_1(B_215,A_216)
      | ~ v1_relat_1(B_215) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2231,c_163])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( v5_relat_1(B_21,A_20)
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_11189,plain,(
    ! [B_304,A_305,B_306] :
      ( v5_relat_1(B_304,k2_xboole_0(A_305,B_306))
      | ~ v5_relat_1(B_304,A_305)
      | ~ v1_relat_1(B_304) ) ),
    inference(resolution,[status(thm)],[c_5963,c_20])).

tff(c_11870,plain,(
    ! [B_324,B_325,A_326] :
      ( v5_relat_1(B_324,k2_xboole_0(B_325,A_326))
      | ~ v5_relat_1(B_324,A_326)
      | ~ v1_relat_1(B_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_11189])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_408,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_412,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_408])).

tff(c_242,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k1_relat_1(B_55),A_56)
      | ~ v4_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1442,plain,(
    ! [B_110,A_111] :
      ( k2_xboole_0(k1_relat_1(B_110),A_111) = A_111
      | ~ v4_relat_1(B_110,A_111)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_242,c_4])).

tff(c_5060,plain,(
    ! [B_198,A_199,B_200] :
      ( r1_tarski(k1_relat_1(B_198),k2_xboole_0(A_199,B_200))
      | ~ v4_relat_1(B_198,A_199)
      | ~ v1_relat_1(B_198) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_163])).

tff(c_24,plain,(
    ! [A_22] :
      ( k2_xboole_0(k1_relat_1(A_22),k2_relat_1(A_22)) = k3_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_813,plain,(
    ! [A_99,C_100,B_101] :
      ( r1_tarski(k2_xboole_0(A_99,C_100),B_101)
      | ~ r1_tarski(C_100,B_101)
      | ~ r1_tarski(A_99,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3545,plain,(
    ! [A_163,B_164] :
      ( r1_tarski(k3_relat_1(A_163),B_164)
      | ~ r1_tarski(k2_relat_1(A_163),B_164)
      | ~ r1_tarski(k1_relat_1(A_163),B_164)
      | ~ v1_relat_1(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_813])).

tff(c_32,plain,(
    ~ r1_tarski(k3_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_3554,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3545,c_32])).

tff(c_3559,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_3554])).

tff(c_3849,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_3559])).

tff(c_5063,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5060,c_3849])).

tff(c_5126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_412,c_5063])).

tff(c_5127,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),k2_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_3559])).

tff(c_5131,plain,
    ( ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_5127])).

tff(c_5134,plain,(
    ~ v5_relat_1('#skF_3',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_5131])).

tff(c_11873,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11870,c_5134])).

tff(c_11948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_483,c_11873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:21:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.49/2.66  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.67  
% 7.49/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.67  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 7.49/2.67  
% 7.49/2.67  %Foreground sorts:
% 7.49/2.67  
% 7.49/2.67  
% 7.49/2.67  %Background operators:
% 7.49/2.67  
% 7.49/2.67  
% 7.49/2.67  %Foreground operators:
% 7.49/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.49/2.67  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 7.49/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.49/2.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.49/2.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.49/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.49/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.49/2.67  tff('#skF_1', type, '#skF_1': $i).
% 7.49/2.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.49/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.49/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.49/2.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.49/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.49/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.49/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.49/2.67  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.49/2.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.49/2.67  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.49/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.49/2.67  
% 7.49/2.68  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.49/2.68  tff(f_81, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => r1_tarski(k3_relat_1(C), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relset_1)).
% 7.49/2.68  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.49/2.68  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.49/2.68  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.49/2.68  tff(f_45, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.49/2.68  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 7.49/2.68  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.49/2.68  tff(f_35, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.49/2.68  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 7.49/2.68  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 7.49/2.68  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 7.49/2.68  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.49/2.68  tff(c_26, plain, (![A_23, B_24]: (v1_relat_1(k2_zfmisc_1(A_23, B_24)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.49/2.68  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.49/2.68  tff(c_208, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.49/2.68  tff(c_211, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_34, c_208])).
% 7.49/2.68  tff(c_214, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_211])).
% 7.49/2.68  tff(c_479, plain, (![C_74, B_75, A_76]: (v5_relat_1(C_74, B_75) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_76, B_75))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.49/2.68  tff(c_483, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_479])).
% 7.49/2.68  tff(c_10, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.49/2.68  tff(c_75, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.49/2.68  tff(c_90, plain, (![B_38, A_39]: (k3_tarski(k2_tarski(B_38, A_39))=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_10, c_75])).
% 7.49/2.68  tff(c_12, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.49/2.68  tff(c_96, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(superposition, [status(thm), theory('equality')], [c_90, c_12])).
% 7.49/2.68  tff(c_782, plain, (![B_93, A_94]: (r1_tarski(k2_relat_1(B_93), A_94) | ~v5_relat_1(B_93, A_94) | ~v1_relat_1(B_93))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.49/2.68  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(A_4, B_5)=B_5 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.49/2.68  tff(c_2231, plain, (![B_134, A_135]: (k2_xboole_0(k2_relat_1(B_134), A_135)=A_135 | ~v5_relat_1(B_134, A_135) | ~v1_relat_1(B_134))), inference(resolution, [status(thm)], [c_782, c_4])).
% 7.49/2.68  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.49/2.68  tff(c_152, plain, (![A_42, C_43, B_44]: (r1_tarski(A_42, C_43) | ~r1_tarski(k2_xboole_0(A_42, B_44), C_43))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.49/2.68  tff(c_163, plain, (![A_42, B_44, B_7]: (r1_tarski(A_42, k2_xboole_0(k2_xboole_0(A_42, B_44), B_7)))), inference(resolution, [status(thm)], [c_6, c_152])).
% 7.49/2.68  tff(c_5963, plain, (![B_215, A_216, B_217]: (r1_tarski(k2_relat_1(B_215), k2_xboole_0(A_216, B_217)) | ~v5_relat_1(B_215, A_216) | ~v1_relat_1(B_215))), inference(superposition, [status(thm), theory('equality')], [c_2231, c_163])).
% 7.49/2.68  tff(c_20, plain, (![B_21, A_20]: (v5_relat_1(B_21, A_20) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.49/2.68  tff(c_11189, plain, (![B_304, A_305, B_306]: (v5_relat_1(B_304, k2_xboole_0(A_305, B_306)) | ~v5_relat_1(B_304, A_305) | ~v1_relat_1(B_304))), inference(resolution, [status(thm)], [c_5963, c_20])).
% 7.49/2.68  tff(c_11870, plain, (![B_324, B_325, A_326]: (v5_relat_1(B_324, k2_xboole_0(B_325, A_326)) | ~v5_relat_1(B_324, A_326) | ~v1_relat_1(B_324))), inference(superposition, [status(thm), theory('equality')], [c_96, c_11189])).
% 7.49/2.68  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.49/2.68  tff(c_408, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.49/2.68  tff(c_412, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_408])).
% 7.49/2.68  tff(c_242, plain, (![B_55, A_56]: (r1_tarski(k1_relat_1(B_55), A_56) | ~v4_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.49/2.68  tff(c_1442, plain, (![B_110, A_111]: (k2_xboole_0(k1_relat_1(B_110), A_111)=A_111 | ~v4_relat_1(B_110, A_111) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_242, c_4])).
% 7.49/2.68  tff(c_5060, plain, (![B_198, A_199, B_200]: (r1_tarski(k1_relat_1(B_198), k2_xboole_0(A_199, B_200)) | ~v4_relat_1(B_198, A_199) | ~v1_relat_1(B_198))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_163])).
% 7.49/2.68  tff(c_24, plain, (![A_22]: (k2_xboole_0(k1_relat_1(A_22), k2_relat_1(A_22))=k3_relat_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.49/2.68  tff(c_813, plain, (![A_99, C_100, B_101]: (r1_tarski(k2_xboole_0(A_99, C_100), B_101) | ~r1_tarski(C_100, B_101) | ~r1_tarski(A_99, B_101))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.49/2.68  tff(c_3545, plain, (![A_163, B_164]: (r1_tarski(k3_relat_1(A_163), B_164) | ~r1_tarski(k2_relat_1(A_163), B_164) | ~r1_tarski(k1_relat_1(A_163), B_164) | ~v1_relat_1(A_163))), inference(superposition, [status(thm), theory('equality')], [c_24, c_813])).
% 7.49/2.69  tff(c_32, plain, (~r1_tarski(k3_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 7.49/2.69  tff(c_3554, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_3545, c_32])).
% 7.49/2.69  tff(c_3559, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_3554])).
% 7.49/2.69  tff(c_3849, plain, (~r1_tarski(k1_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_3559])).
% 7.49/2.69  tff(c_5063, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5060, c_3849])).
% 7.49/2.69  tff(c_5126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_412, c_5063])).
% 7.49/2.69  tff(c_5127, plain, (~r1_tarski(k2_relat_1('#skF_3'), k2_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_3559])).
% 7.49/2.69  tff(c_5131, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_22, c_5127])).
% 7.49/2.69  tff(c_5134, plain, (~v5_relat_1('#skF_3', k2_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_5131])).
% 7.49/2.69  tff(c_11873, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11870, c_5134])).
% 7.49/2.69  tff(c_11948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_483, c_11873])).
% 7.49/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.69  
% 7.49/2.69  Inference rules
% 7.49/2.69  ----------------------
% 7.49/2.69  #Ref     : 0
% 7.49/2.69  #Sup     : 2974
% 7.49/2.69  #Fact    : 0
% 7.49/2.69  #Define  : 0
% 7.49/2.69  #Split   : 1
% 7.49/2.69  #Chain   : 0
% 7.49/2.69  #Close   : 0
% 7.49/2.69  
% 7.49/2.69  Ordering : KBO
% 7.49/2.69  
% 7.49/2.69  Simplification rules
% 7.49/2.69  ----------------------
% 7.49/2.69  #Subsume      : 623
% 7.49/2.69  #Demod        : 1567
% 7.49/2.69  #Tautology    : 1363
% 7.49/2.69  #SimpNegUnit  : 0
% 7.49/2.69  #BackRed      : 0
% 7.49/2.69  
% 7.49/2.69  #Partial instantiations: 0
% 7.49/2.69  #Strategies tried      : 1
% 7.49/2.69  
% 7.49/2.69  Timing (in seconds)
% 7.49/2.69  ----------------------
% 7.49/2.69  Preprocessing        : 0.28
% 7.49/2.69  Parsing              : 0.16
% 7.49/2.69  CNF conversion       : 0.02
% 7.49/2.69  Main loop            : 1.63
% 7.49/2.69  Inferencing          : 0.44
% 7.49/2.69  Reduction            : 0.74
% 7.49/2.69  Demodulation         : 0.62
% 7.49/2.69  BG Simplification    : 0.05
% 7.49/2.69  Subsumption          : 0.31
% 7.49/2.69  Abstraction          : 0.06
% 7.49/2.69  MUC search           : 0.00
% 7.49/2.69  Cooper               : 0.00
% 7.49/2.69  Total                : 1.95
% 7.49/2.69  Index Insertion      : 0.00
% 7.49/2.69  Index Deletion       : 0.00
% 7.49/2.69  Index Matching       : 0.00
% 7.49/2.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
