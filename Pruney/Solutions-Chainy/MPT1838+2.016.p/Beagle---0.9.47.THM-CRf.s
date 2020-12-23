%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:16 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 184 expanded)
%              Number of leaves         :   25 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  150 ( 518 expanded)
%              Number of equality atoms :   73 ( 232 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_93,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_101,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_93])).

tff(c_38,plain,(
    ! [A_16] :
      ( m1_subset_1('#skF_1'(A_16),A_16)
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_260,plain,(
    ! [A_44,B_45] :
      ( k6_domain_1(A_44,B_45) = k1_tarski(B_45)
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_329,plain,(
    ! [A_57] :
      ( k6_domain_1(A_57,'#skF_1'(A_57)) = k1_tarski('#skF_1'(A_57))
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_38,c_260])).

tff(c_36,plain,(
    ! [A_16] :
      ( k6_domain_1(A_16,'#skF_1'(A_16)) = A_16
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_344,plain,(
    ! [A_58] :
      ( k1_tarski('#skF_1'(A_58)) = A_58
      | ~ v1_zfmisc_1(A_58)
      | v1_xboole_0(A_58)
      | ~ v1_zfmisc_1(A_58)
      | v1_xboole_0(A_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_36])).

tff(c_16,plain,(
    ! [A_11,C_13,B_12] :
      ( k1_tarski(A_11) = C_13
      | k1_xboole_0 = C_13
      | k2_xboole_0(B_12,C_13) != k1_tarski(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_403,plain,(
    ! [A_60,C_61,B_62] :
      ( k1_tarski('#skF_1'(A_60)) = C_61
      | k1_xboole_0 = C_61
      | k2_xboole_0(B_62,C_61) != A_60
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60)
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_16])).

tff(c_409,plain,(
    ! [A_60] :
      ( k1_tarski('#skF_1'(A_60)) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | A_60 != '#skF_3'
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60)
      | ~ v1_zfmisc_1(A_60)
      | v1_xboole_0(A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_403])).

tff(c_459,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_409])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_194,plain,(
    ! [B_34,A_35] :
      ( ~ r1_xboole_0(B_34,A_35)
      | ~ r1_tarski(B_34,A_35)
      | v1_xboole_0(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_208,plain,(
    ! [A_37,B_38] :
      ( ~ r1_tarski(A_37,B_38)
      | v1_xboole_0(A_37)
      | k4_xboole_0(A_37,B_38) != A_37 ) ),
    inference(resolution,[status(thm)],[c_14,c_194])).

tff(c_215,plain,(
    ! [A_5] :
      ( v1_xboole_0(k1_xboole_0)
      | k4_xboole_0(k1_xboole_0,A_5) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_208])).

tff(c_240,plain,(
    ! [A_42] : k4_xboole_0(k1_xboole_0,A_42) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_246,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_240])).

tff(c_247,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_464,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_459,c_247])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_464])).

tff(c_473,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_409])).

tff(c_44,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_100,plain,(
    ! [A_5] : k2_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_421,plain,(
    ! [A_63] :
      ( k1_tarski('#skF_1'(A_63)) = A_63
      | k1_xboole_0 = A_63
      | ~ v1_zfmisc_1(A_63)
      | v1_xboole_0(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_403])).

tff(c_578,plain,(
    ! [A_66,C_67,B_68] :
      ( k1_tarski('#skF_1'(A_66)) = C_67
      | k1_xboole_0 = C_67
      | k2_xboole_0(B_68,C_67) != A_66
      | k1_xboole_0 = A_66
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_16])).

tff(c_584,plain,(
    ! [A_66] :
      ( k1_tarski('#skF_1'(A_66)) = '#skF_3'
      | k1_xboole_0 = '#skF_3'
      | A_66 != '#skF_3'
      | k1_xboole_0 = A_66
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_578])).

tff(c_620,plain,(
    ! [A_72] :
      ( k1_tarski('#skF_1'(A_72)) = '#skF_3'
      | A_72 != '#skF_3'
      | k1_xboole_0 = A_72
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72) ) ),
    inference(negUnitSimplification,[status(thm)],[c_473,c_584])).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_219,plain,(
    ! [B_39,A_40,C_41] :
      ( k1_xboole_0 = B_39
      | k1_tarski(A_40) = B_39
      | k2_xboole_0(B_39,C_41) != k1_tarski(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_228,plain,(
    ! [A_40] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_40) = '#skF_2'
      | k1_tarski(A_40) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_219])).

tff(c_248,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_249,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_247])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_249])).

tff(c_257,plain,(
    ! [A_40] :
      ( k1_tarski(A_40) = '#skF_2'
      | k1_tarski(A_40) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_442,plain,(
    ! [A_63] :
      ( k1_tarski('#skF_1'(A_63)) = '#skF_2'
      | A_63 != '#skF_3'
      | k1_xboole_0 = A_63
      | ~ v1_zfmisc_1(A_63)
      | v1_xboole_0(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_257])).

tff(c_629,plain,(
    ! [A_72] :
      ( '#skF_2' = '#skF_3'
      | A_72 != '#skF_3'
      | k1_xboole_0 = A_72
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72)
      | A_72 != '#skF_3'
      | k1_xboole_0 = A_72
      | ~ v1_zfmisc_1(A_72)
      | v1_xboole_0(A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_442])).

tff(c_682,plain,(
    ! [A_73] :
      ( A_73 != '#skF_3'
      | k1_xboole_0 = A_73
      | ~ v1_zfmisc_1(A_73)
      | v1_xboole_0(A_73)
      | A_73 != '#skF_3'
      | k1_xboole_0 = A_73
      | ~ v1_zfmisc_1(A_73)
      | v1_xboole_0(A_73) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_629])).

tff(c_684,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_682])).

tff(c_687,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_684])).

tff(c_689,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_473,c_687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:13:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.39  
% 2.88/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.39  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.88/1.39  
% 2.88/1.39  %Foreground sorts:
% 2.88/1.39  
% 2.88/1.39  
% 2.88/1.39  %Background operators:
% 2.88/1.39  
% 2.88/1.39  
% 2.88/1.39  %Foreground operators:
% 2.88/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.88/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.88/1.39  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.88/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.88/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.88/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.88/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.88/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.88/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.88/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.88/1.39  
% 2.88/1.41  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.88/1.41  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.88/1.41  tff(f_82, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.88/1.41  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.88/1.41  tff(f_65, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.88/1.41  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.88/1.41  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.88/1.41  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.88/1.41  tff(f_43, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.88/1.41  tff(c_46, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.88/1.41  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.88/1.41  tff(c_93, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.41  tff(c_101, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_42, c_93])).
% 2.88/1.41  tff(c_38, plain, (![A_16]: (m1_subset_1('#skF_1'(A_16), A_16) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.88/1.41  tff(c_260, plain, (![A_44, B_45]: (k6_domain_1(A_44, B_45)=k1_tarski(B_45) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.41  tff(c_329, plain, (![A_57]: (k6_domain_1(A_57, '#skF_1'(A_57))=k1_tarski('#skF_1'(A_57)) | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_38, c_260])).
% 2.88/1.41  tff(c_36, plain, (![A_16]: (k6_domain_1(A_16, '#skF_1'(A_16))=A_16 | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.88/1.41  tff(c_344, plain, (![A_58]: (k1_tarski('#skF_1'(A_58))=A_58 | ~v1_zfmisc_1(A_58) | v1_xboole_0(A_58) | ~v1_zfmisc_1(A_58) | v1_xboole_0(A_58))), inference(superposition, [status(thm), theory('equality')], [c_329, c_36])).
% 2.88/1.41  tff(c_16, plain, (![A_11, C_13, B_12]: (k1_tarski(A_11)=C_13 | k1_xboole_0=C_13 | k2_xboole_0(B_12, C_13)!=k1_tarski(A_11))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.88/1.41  tff(c_403, plain, (![A_60, C_61, B_62]: (k1_tarski('#skF_1'(A_60))=C_61 | k1_xboole_0=C_61 | k2_xboole_0(B_62, C_61)!=A_60 | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60) | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_344, c_16])).
% 2.88/1.41  tff(c_409, plain, (![A_60]: (k1_tarski('#skF_1'(A_60))='#skF_3' | k1_xboole_0='#skF_3' | A_60!='#skF_3' | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60) | ~v1_zfmisc_1(A_60) | v1_xboole_0(A_60))), inference(superposition, [status(thm), theory('equality')], [c_101, c_403])).
% 2.88/1.41  tff(c_459, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_409])).
% 2.88/1.41  tff(c_8, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.88/1.41  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.88/1.41  tff(c_14, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.88/1.41  tff(c_194, plain, (![B_34, A_35]: (~r1_xboole_0(B_34, A_35) | ~r1_tarski(B_34, A_35) | v1_xboole_0(B_34))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.88/1.41  tff(c_208, plain, (![A_37, B_38]: (~r1_tarski(A_37, B_38) | v1_xboole_0(A_37) | k4_xboole_0(A_37, B_38)!=A_37)), inference(resolution, [status(thm)], [c_14, c_194])).
% 2.88/1.41  tff(c_215, plain, (![A_5]: (v1_xboole_0(k1_xboole_0) | k4_xboole_0(k1_xboole_0, A_5)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_208])).
% 2.88/1.41  tff(c_240, plain, (![A_42]: (k4_xboole_0(k1_xboole_0, A_42)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_215])).
% 2.88/1.41  tff(c_246, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_8, c_240])).
% 2.88/1.41  tff(c_247, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_215])).
% 2.88/1.41  tff(c_464, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_459, c_247])).
% 2.88/1.41  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_464])).
% 2.88/1.41  tff(c_473, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_409])).
% 2.88/1.41  tff(c_44, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.88/1.41  tff(c_40, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.88/1.41  tff(c_100, plain, (![A_5]: (k2_xboole_0(k1_xboole_0, A_5)=A_5)), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.88/1.41  tff(c_421, plain, (![A_63]: (k1_tarski('#skF_1'(A_63))=A_63 | k1_xboole_0=A_63 | ~v1_zfmisc_1(A_63) | v1_xboole_0(A_63))), inference(superposition, [status(thm), theory('equality')], [c_100, c_403])).
% 2.88/1.41  tff(c_578, plain, (![A_66, C_67, B_68]: (k1_tarski('#skF_1'(A_66))=C_67 | k1_xboole_0=C_67 | k2_xboole_0(B_68, C_67)!=A_66 | k1_xboole_0=A_66 | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66))), inference(superposition, [status(thm), theory('equality')], [c_421, c_16])).
% 2.88/1.41  tff(c_584, plain, (![A_66]: (k1_tarski('#skF_1'(A_66))='#skF_3' | k1_xboole_0='#skF_3' | A_66!='#skF_3' | k1_xboole_0=A_66 | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66))), inference(superposition, [status(thm), theory('equality')], [c_101, c_578])).
% 2.88/1.41  tff(c_620, plain, (![A_72]: (k1_tarski('#skF_1'(A_72))='#skF_3' | A_72!='#skF_3' | k1_xboole_0=A_72 | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72))), inference(negUnitSimplification, [status(thm)], [c_473, c_584])).
% 2.88/1.41  tff(c_48, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.88/1.41  tff(c_219, plain, (![B_39, A_40, C_41]: (k1_xboole_0=B_39 | k1_tarski(A_40)=B_39 | k2_xboole_0(B_39, C_41)!=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.88/1.41  tff(c_228, plain, (![A_40]: (k1_xboole_0='#skF_2' | k1_tarski(A_40)='#skF_2' | k1_tarski(A_40)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_101, c_219])).
% 2.88/1.41  tff(c_248, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_228])).
% 2.88/1.41  tff(c_249, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_248, c_247])).
% 2.88/1.41  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_249])).
% 2.88/1.41  tff(c_257, plain, (![A_40]: (k1_tarski(A_40)='#skF_2' | k1_tarski(A_40)!='#skF_3')), inference(splitRight, [status(thm)], [c_228])).
% 2.88/1.41  tff(c_442, plain, (![A_63]: (k1_tarski('#skF_1'(A_63))='#skF_2' | A_63!='#skF_3' | k1_xboole_0=A_63 | ~v1_zfmisc_1(A_63) | v1_xboole_0(A_63))), inference(superposition, [status(thm), theory('equality')], [c_421, c_257])).
% 2.88/1.41  tff(c_629, plain, (![A_72]: ('#skF_2'='#skF_3' | A_72!='#skF_3' | k1_xboole_0=A_72 | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72) | A_72!='#skF_3' | k1_xboole_0=A_72 | ~v1_zfmisc_1(A_72) | v1_xboole_0(A_72))), inference(superposition, [status(thm), theory('equality')], [c_620, c_442])).
% 2.88/1.41  tff(c_682, plain, (![A_73]: (A_73!='#skF_3' | k1_xboole_0=A_73 | ~v1_zfmisc_1(A_73) | v1_xboole_0(A_73) | A_73!='#skF_3' | k1_xboole_0=A_73 | ~v1_zfmisc_1(A_73) | v1_xboole_0(A_73))), inference(negUnitSimplification, [status(thm)], [c_40, c_629])).
% 2.88/1.41  tff(c_684, plain, (k1_xboole_0='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_44, c_682])).
% 2.88/1.41  tff(c_687, plain, (k1_xboole_0='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_684])).
% 2.88/1.41  tff(c_689, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_473, c_687])).
% 2.88/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.41  
% 2.88/1.41  Inference rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Ref     : 3
% 2.88/1.41  #Sup     : 162
% 2.88/1.41  #Fact    : 0
% 2.88/1.41  #Define  : 0
% 2.88/1.41  #Split   : 3
% 2.88/1.41  #Chain   : 0
% 2.88/1.41  #Close   : 0
% 2.88/1.41  
% 2.88/1.41  Ordering : KBO
% 2.88/1.41  
% 2.88/1.41  Simplification rules
% 2.88/1.41  ----------------------
% 2.88/1.41  #Subsume      : 31
% 2.88/1.41  #Demod        : 27
% 2.88/1.41  #Tautology    : 75
% 2.88/1.41  #SimpNegUnit  : 18
% 2.88/1.41  #BackRed      : 16
% 2.88/1.41  
% 2.88/1.41  #Partial instantiations: 0
% 2.88/1.41  #Strategies tried      : 1
% 2.88/1.41  
% 2.88/1.41  Timing (in seconds)
% 2.88/1.41  ----------------------
% 2.88/1.41  Preprocessing        : 0.31
% 2.88/1.41  Parsing              : 0.16
% 2.88/1.41  CNF conversion       : 0.02
% 2.88/1.41  Main loop            : 0.34
% 2.88/1.41  Inferencing          : 0.11
% 2.88/1.41  Reduction            : 0.10
% 2.88/1.41  Demodulation         : 0.07
% 2.88/1.41  BG Simplification    : 0.02
% 2.88/1.41  Subsumption          : 0.09
% 2.88/1.41  Abstraction          : 0.02
% 2.88/1.41  MUC search           : 0.00
% 2.88/1.41  Cooper               : 0.00
% 2.88/1.41  Total                : 0.68
% 2.88/1.41  Index Insertion      : 0.00
% 2.88/1.41  Index Deletion       : 0.00
% 2.88/1.41  Index Matching       : 0.00
% 2.88/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
