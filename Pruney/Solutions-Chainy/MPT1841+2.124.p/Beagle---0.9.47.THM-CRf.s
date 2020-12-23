%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:44 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   63 (  80 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 117 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D,E,F,G,H] : ~ v1_xboole_0(k6_enumset1(A,B,C,D,E,F,G,H)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_subset_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_70,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [A_82,F_85,E_84,B_88,G_86,C_83,D_87] : k6_enumset1(A_82,A_82,B_88,C_83,D_87,E_84,F_85,G_86) = k5_enumset1(A_82,B_88,C_83,D_87,E_84,F_85,G_86) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_16,plain,(
    ! [G_35,H_36,E_33,A_29,F_34,D_32,C_31,B_30] : ~ v1_xboole_0(k6_enumset1(A_29,B_30,C_31,D_32,E_33,F_34,G_35,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_144,plain,(
    ! [E_94,A_95,F_89,B_92,G_90,C_91,D_93] : ~ v1_xboole_0(k5_enumset1(A_95,B_92,C_91,D_93,E_94,F_89,G_90)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_16])).

tff(c_147,plain,(
    ! [F_96,A_99,D_100,E_98,C_101,B_97] : ~ v1_xboole_0(k4_enumset1(A_99,B_97,C_101,D_100,E_98,F_96)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_144])).

tff(c_150,plain,(
    ! [B_104,C_102,E_106,A_103,D_105] : ~ v1_xboole_0(k3_enumset1(A_103,B_104,C_102,D_105,E_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_180,plain,(
    ! [A_109,B_110,C_111,D_112] : ~ v1_xboole_0(k2_enumset1(A_109,B_110,C_111,D_112)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_150])).

tff(c_183,plain,(
    ! [A_113,B_114,C_115] : ~ v1_xboole_0(k1_enumset1(A_113,B_114,C_115)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_180])).

tff(c_186,plain,(
    ! [A_116,B_117] : ~ v1_xboole_0(k2_tarski(A_116,B_117)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_183])).

tff(c_188,plain,(
    ! [A_1] : ~ v1_xboole_0(k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_186])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_58,plain,(
    ! [A_51,B_52] :
      ( k6_domain_1(A_51,B_52) = k1_tarski(B_52)
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_58])).

tff(c_64,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_61])).

tff(c_26,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_65,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_71,plain,(
    ! [A_61,B_62] :
      ( m1_subset_1(k6_domain_1(A_61,B_62),k1_zfmisc_1(A_61))
      | ~ m1_subset_1(B_62,A_61)
      | v1_xboole_0(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_71])).

tff(c_80,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_77])).

tff(c_81,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_80])).

tff(c_96,plain,(
    ! [B_67,A_68] :
      ( ~ v1_subset_1(B_67,A_68)
      | v1_xboole_0(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_68))
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_99,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_81,c_96])).

tff(c_105,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_65,c_99])).

tff(c_106,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_105])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_106])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:06:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.32  
% 2.38/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.33  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.38/1.33  
% 2.38/1.33  %Foreground sorts:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Background operators:
% 2.38/1.33  
% 2.38/1.33  
% 2.38/1.33  %Foreground operators:
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.38/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.38/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.38/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.38/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.38/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.38/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.38/1.33  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.38/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.38/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.38/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.38/1.33  
% 2.38/1.34  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.38/1.34  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.38/1.34  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.38/1.34  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 2.38/1.34  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 2.38/1.34  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 2.38/1.34  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 2.38/1.34  tff(f_42, axiom, (![A, B, C, D, E, F, G, H]: ~v1_xboole_0(k6_enumset1(A, B, C, D, E, F, G, H))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_subset_1)).
% 2.38/1.34  tff(f_82, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.38/1.34  tff(f_56, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.38/1.34  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.38/1.34  tff(f_70, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.38/1.34  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.38/1.34  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.38/1.34  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.38/1.34  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.34  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.38/1.34  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.38/1.34  tff(c_133, plain, (![A_82, F_85, E_84, B_88, G_86, C_83, D_87]: (k6_enumset1(A_82, A_82, B_88, C_83, D_87, E_84, F_85, G_86)=k5_enumset1(A_82, B_88, C_83, D_87, E_84, F_85, G_86))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.38/1.34  tff(c_16, plain, (![G_35, H_36, E_33, A_29, F_34, D_32, C_31, B_30]: (~v1_xboole_0(k6_enumset1(A_29, B_30, C_31, D_32, E_33, F_34, G_35, H_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.38/1.34  tff(c_144, plain, (![E_94, A_95, F_89, B_92, G_90, C_91, D_93]: (~v1_xboole_0(k5_enumset1(A_95, B_92, C_91, D_93, E_94, F_89, G_90)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_16])).
% 2.38/1.34  tff(c_147, plain, (![F_96, A_99, D_100, E_98, C_101, B_97]: (~v1_xboole_0(k4_enumset1(A_99, B_97, C_101, D_100, E_98, F_96)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_144])).
% 2.38/1.34  tff(c_150, plain, (![B_104, C_102, E_106, A_103, D_105]: (~v1_xboole_0(k3_enumset1(A_103, B_104, C_102, D_105, E_106)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_147])).
% 2.38/1.34  tff(c_180, plain, (![A_109, B_110, C_111, D_112]: (~v1_xboole_0(k2_enumset1(A_109, B_110, C_111, D_112)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_150])).
% 2.38/1.34  tff(c_183, plain, (![A_113, B_114, C_115]: (~v1_xboole_0(k1_enumset1(A_113, B_114, C_115)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_180])).
% 2.38/1.34  tff(c_186, plain, (![A_116, B_117]: (~v1_xboole_0(k2_tarski(A_116, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_183])).
% 2.38/1.34  tff(c_188, plain, (![A_1]: (~v1_xboole_0(k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_186])).
% 2.38/1.34  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.38/1.34  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.38/1.34  tff(c_28, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.38/1.34  tff(c_58, plain, (![A_51, B_52]: (k6_domain_1(A_51, B_52)=k1_tarski(B_52) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.38/1.34  tff(c_61, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_58])).
% 2.38/1.34  tff(c_64, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_61])).
% 2.38/1.34  tff(c_26, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.38/1.34  tff(c_65, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26])).
% 2.38/1.34  tff(c_71, plain, (![A_61, B_62]: (m1_subset_1(k6_domain_1(A_61, B_62), k1_zfmisc_1(A_61)) | ~m1_subset_1(B_62, A_61) | v1_xboole_0(A_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.38/1.34  tff(c_77, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_64, c_71])).
% 2.38/1.34  tff(c_80, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_77])).
% 2.38/1.34  tff(c_81, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_30, c_80])).
% 2.38/1.34  tff(c_96, plain, (![B_67, A_68]: (~v1_subset_1(B_67, A_68) | v1_xboole_0(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(A_68)) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.38/1.34  tff(c_99, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_81, c_96])).
% 2.38/1.34  tff(c_105, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_65, c_99])).
% 2.38/1.34  tff(c_106, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_105])).
% 2.38/1.34  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_106])).
% 2.38/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.38/1.34  
% 2.38/1.34  Inference rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Ref     : 0
% 2.38/1.34  #Sup     : 37
% 2.38/1.34  #Fact    : 0
% 2.38/1.34  #Define  : 0
% 2.38/1.34  #Split   : 1
% 2.38/1.34  #Chain   : 0
% 2.38/1.34  #Close   : 0
% 2.38/1.34  
% 2.38/1.34  Ordering : KBO
% 2.38/1.34  
% 2.38/1.34  Simplification rules
% 2.38/1.34  ----------------------
% 2.38/1.34  #Subsume      : 0
% 2.38/1.34  #Demod        : 12
% 2.38/1.34  #Tautology    : 20
% 2.38/1.34  #SimpNegUnit  : 6
% 2.38/1.34  #BackRed      : 2
% 2.38/1.34  
% 2.38/1.34  #Partial instantiations: 0
% 2.38/1.34  #Strategies tried      : 1
% 2.38/1.34  
% 2.38/1.34  Timing (in seconds)
% 2.38/1.34  ----------------------
% 2.38/1.34  Preprocessing        : 0.37
% 2.38/1.34  Parsing              : 0.21
% 2.38/1.34  CNF conversion       : 0.02
% 2.38/1.35  Main loop            : 0.20
% 2.38/1.35  Inferencing          : 0.08
% 2.38/1.35  Reduction            : 0.06
% 2.38/1.35  Demodulation         : 0.04
% 2.38/1.35  BG Simplification    : 0.02
% 2.38/1.35  Subsumption          : 0.03
% 2.38/1.35  Abstraction          : 0.02
% 2.38/1.35  MUC search           : 0.00
% 2.38/1.35  Cooper               : 0.00
% 2.38/1.35  Total                : 0.60
% 2.38/1.35  Index Insertion      : 0.00
% 2.38/1.35  Index Deletion       : 0.00
% 2.38/1.35  Index Matching       : 0.00
% 2.38/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
