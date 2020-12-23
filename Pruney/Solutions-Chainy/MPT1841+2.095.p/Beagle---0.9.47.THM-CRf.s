%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:40 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   73 (  97 expanded)
%              Number of leaves         :   34 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   90 ( 148 expanded)
%              Number of equality atoms :   26 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_56,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_68,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_96,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20,plain,(
    ! [A_15] : v1_xboole_0('#skF_1'(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_64,plain,(
    ! [B_36,A_37] :
      ( ~ v1_xboole_0(B_36)
      | B_36 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_38] :
      ( k1_xboole_0 = A_38
      | ~ v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_78,plain,(
    ! [A_15] : '#skF_1'(A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_71])).

tff(c_22,plain,(
    ! [A_15] : m1_subset_1('#skF_1'(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_81,plain,(
    ! [A_15] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_22])).

tff(c_93,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | ~ m1_subset_1(A_41,k1_zfmisc_1(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_97,plain,(
    ! [A_15] : r1_tarski(k1_xboole_0,A_15) ),
    inference(resolution,[status(thm)],[c_81,c_93])).

tff(c_104,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_108,plain,(
    ! [A_15] : k3_xboole_0(k1_xboole_0,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_104])).

tff(c_134,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_143,plain,(
    ! [A_15] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_134])).

tff(c_147,plain,(
    ! [A_55] : k4_xboole_0(k1_xboole_0,A_55) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_143])).

tff(c_12,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,(
    ! [A_55] : k5_xboole_0(A_55,k1_xboole_0) = k2_xboole_0(A_55,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_12])).

tff(c_158,plain,(
    ! [A_56] : k2_xboole_0(A_56,k1_xboole_0) = A_56 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_152])).

tff(c_18,plain,(
    ! [A_13,B_14] : k2_xboole_0(k1_tarski(A_13),B_14) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_165,plain,(
    ! [A_13] : k1_tarski(A_13) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_18])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_40,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_187,plain,(
    ! [A_63,B_64] :
      ( k6_domain_1(A_63,B_64) = k1_tarski(B_64)
      | ~ m1_subset_1(B_64,A_63)
      | v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_196,plain,
    ( k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_187])).

tff(c_201,plain,(
    k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_196])).

tff(c_38,plain,(
    v1_subset_1(k6_domain_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_202,plain,(
    v1_subset_1(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_38])).

tff(c_228,plain,(
    ! [A_67,B_68] :
      ( m1_subset_1(k6_domain_1(A_67,B_68),k1_zfmisc_1(A_67))
      | ~ m1_subset_1(B_68,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_243,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_228])).

tff(c_250,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_243])).

tff(c_251,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_250])).

tff(c_34,plain,(
    ! [B_28,A_26] :
      ( ~ v1_subset_1(B_28,A_26)
      | v1_xboole_0(B_28)
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_26))
      | ~ v1_zfmisc_1(A_26)
      | v1_xboole_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_268,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_3'),'#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3'))
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_251,c_34])).

tff(c_280,plain,
    ( v1_xboole_0(k1_tarski('#skF_3'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_202,c_268])).

tff(c_281,plain,(
    v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_280])).

tff(c_70,plain,(
    ! [A_37] :
      ( k1_xboole_0 = A_37
      | ~ v1_xboole_0(A_37) ) ),
    inference(resolution,[status(thm)],[c_2,c_64])).

tff(c_289,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_281,c_70])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_289])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.32  
% 2.23/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.33  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.23/1.33  
% 2.23/1.33  %Foreground sorts:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Background operators:
% 2.23/1.33  
% 2.23/1.33  
% 2.23/1.33  %Foreground operators:
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.33  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.23/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.23/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.23/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.23/1.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.23/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.23/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.23/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.23/1.33  
% 2.23/1.34  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.23/1.34  tff(f_56, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.23/1.34  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.23/1.34  tff(f_42, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.23/1.34  tff(f_68, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.23/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.23/1.34  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.34  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.23/1.34  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.23/1.34  tff(f_108, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.23/1.34  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.23/1.34  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.23/1.34  tff(f_96, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.23/1.34  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.23/1.34  tff(c_20, plain, (![A_15]: (v1_xboole_0('#skF_1'(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.34  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.23/1.34  tff(c_64, plain, (![B_36, A_37]: (~v1_xboole_0(B_36) | B_36=A_37 | ~v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.23/1.34  tff(c_71, plain, (![A_38]: (k1_xboole_0=A_38 | ~v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_2, c_64])).
% 2.23/1.34  tff(c_78, plain, (![A_15]: ('#skF_1'(A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_71])).
% 2.23/1.34  tff(c_22, plain, (![A_15]: (m1_subset_1('#skF_1'(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.23/1.34  tff(c_81, plain, (![A_15]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_22])).
% 2.23/1.34  tff(c_93, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | ~m1_subset_1(A_41, k1_zfmisc_1(B_42)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.23/1.34  tff(c_97, plain, (![A_15]: (r1_tarski(k1_xboole_0, A_15))), inference(resolution, [status(thm)], [c_81, c_93])).
% 2.23/1.34  tff(c_104, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.23/1.34  tff(c_108, plain, (![A_15]: (k3_xboole_0(k1_xboole_0, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_104])).
% 2.23/1.34  tff(c_134, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.23/1.34  tff(c_143, plain, (![A_15]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_15))), inference(superposition, [status(thm), theory('equality')], [c_108, c_134])).
% 2.23/1.34  tff(c_147, plain, (![A_55]: (k4_xboole_0(k1_xboole_0, A_55)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_143])).
% 2.23/1.34  tff(c_12, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.23/1.34  tff(c_152, plain, (![A_55]: (k5_xboole_0(A_55, k1_xboole_0)=k2_xboole_0(A_55, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_147, c_12])).
% 2.23/1.34  tff(c_158, plain, (![A_56]: (k2_xboole_0(A_56, k1_xboole_0)=A_56)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_152])).
% 2.23/1.34  tff(c_18, plain, (![A_13, B_14]: (k2_xboole_0(k1_tarski(A_13), B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.34  tff(c_165, plain, (![A_13]: (k1_tarski(A_13)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_158, c_18])).
% 2.23/1.34  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.34  tff(c_36, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.34  tff(c_40, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.34  tff(c_187, plain, (![A_63, B_64]: (k6_domain_1(A_63, B_64)=k1_tarski(B_64) | ~m1_subset_1(B_64, A_63) | v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.34  tff(c_196, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_40, c_187])).
% 2.23/1.34  tff(c_201, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_196])).
% 2.23/1.34  tff(c_38, plain, (v1_subset_1(k6_domain_1('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_108])).
% 2.23/1.34  tff(c_202, plain, (v1_subset_1(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_38])).
% 2.23/1.34  tff(c_228, plain, (![A_67, B_68]: (m1_subset_1(k6_domain_1(A_67, B_68), k1_zfmisc_1(A_67)) | ~m1_subset_1(B_68, A_67) | v1_xboole_0(A_67))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.23/1.34  tff(c_243, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_201, c_228])).
% 2.23/1.34  tff(c_250, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_243])).
% 2.23/1.34  tff(c_251, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_250])).
% 2.23/1.34  tff(c_34, plain, (![B_28, A_26]: (~v1_subset_1(B_28, A_26) | v1_xboole_0(B_28) | ~m1_subset_1(B_28, k1_zfmisc_1(A_26)) | ~v1_zfmisc_1(A_26) | v1_xboole_0(A_26))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.23/1.34  tff(c_268, plain, (~v1_subset_1(k1_tarski('#skF_3'), '#skF_2') | v1_xboole_0(k1_tarski('#skF_3')) | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_251, c_34])).
% 2.23/1.34  tff(c_280, plain, (v1_xboole_0(k1_tarski('#skF_3')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_202, c_268])).
% 2.23/1.34  tff(c_281, plain, (v1_xboole_0(k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_280])).
% 2.23/1.34  tff(c_70, plain, (![A_37]: (k1_xboole_0=A_37 | ~v1_xboole_0(A_37))), inference(resolution, [status(thm)], [c_2, c_64])).
% 2.23/1.34  tff(c_289, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_281, c_70])).
% 2.23/1.34  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_289])).
% 2.23/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.34  
% 2.23/1.34  Inference rules
% 2.23/1.34  ----------------------
% 2.23/1.34  #Ref     : 0
% 2.23/1.34  #Sup     : 55
% 2.23/1.34  #Fact    : 0
% 2.23/1.34  #Define  : 0
% 2.23/1.34  #Split   : 0
% 2.23/1.34  #Chain   : 0
% 2.23/1.34  #Close   : 0
% 2.23/1.34  
% 2.23/1.34  Ordering : KBO
% 2.23/1.34  
% 2.23/1.34  Simplification rules
% 2.23/1.34  ----------------------
% 2.23/1.34  #Subsume      : 4
% 2.23/1.34  #Demod        : 13
% 2.23/1.34  #Tautology    : 27
% 2.23/1.34  #SimpNegUnit  : 4
% 2.23/1.34  #BackRed      : 3
% 2.23/1.34  
% 2.23/1.34  #Partial instantiations: 0
% 2.23/1.34  #Strategies tried      : 1
% 2.23/1.34  
% 2.23/1.34  Timing (in seconds)
% 2.23/1.34  ----------------------
% 2.23/1.34  Preprocessing        : 0.33
% 2.23/1.34  Parsing              : 0.18
% 2.23/1.34  CNF conversion       : 0.02
% 2.23/1.34  Main loop            : 0.18
% 2.23/1.34  Inferencing          : 0.08
% 2.23/1.34  Reduction            : 0.06
% 2.23/1.35  Demodulation         : 0.04
% 2.23/1.35  BG Simplification    : 0.01
% 2.23/1.35  Subsumption          : 0.03
% 2.23/1.35  Abstraction          : 0.01
% 2.23/1.35  MUC search           : 0.00
% 2.23/1.35  Cooper               : 0.00
% 2.23/1.35  Total                : 0.55
% 2.23/1.35  Index Insertion      : 0.00
% 2.23/1.35  Index Deletion       : 0.00
% 2.23/1.35  Index Matching       : 0.00
% 2.23/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
