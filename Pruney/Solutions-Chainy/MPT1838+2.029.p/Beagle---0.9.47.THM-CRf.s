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
% DateTime   : Thu Dec  3 10:28:17 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 183 expanded)
%              Number of leaves         :   26 (  70 expanded)
%              Depth                    :   13
%              Number of atoms          :  169 ( 473 expanded)
%              Number of equality atoms :   64 ( 202 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_106,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_92,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_82,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_44,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_1'(A_20),A_20)
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_208,plain,(
    ! [A_46,B_47] :
      ( k6_domain_1(A_46,B_47) = k1_tarski(B_47)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_444,plain,(
    ! [A_86] :
      ( k6_domain_1(A_86,'#skF_1'(A_86)) = k1_tarski('#skF_1'(A_86))
      | ~ v1_zfmisc_1(A_86)
      | v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_42,c_208])).

tff(c_40,plain,(
    ! [A_20] :
      ( k6_domain_1(A_20,'#skF_1'(A_20)) = A_20
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_450,plain,(
    ! [A_86] :
      ( k1_tarski('#skF_1'(A_86)) = A_86
      | ~ v1_zfmisc_1(A_86)
      | v1_xboole_0(A_86)
      | ~ v1_zfmisc_1(A_86)
      | v1_xboole_0(A_86) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_40])).

tff(c_46,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_69,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_77,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_69])).

tff(c_106,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,k2_xboole_0(C_35,B_36))
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_459,plain,(
    ! [A_87,C_88,B_89] :
      ( k2_xboole_0(A_87,k2_xboole_0(C_88,B_89)) = k2_xboole_0(C_88,B_89)
      | ~ r1_tarski(A_87,B_89) ) ),
    inference(resolution,[status(thm)],[c_106,c_12])).

tff(c_34,plain,(
    ! [B_16,A_15,C_17] :
      ( k1_xboole_0 = B_16
      | k1_tarski(A_15) = B_16
      | k2_xboole_0(B_16,C_17) != k1_tarski(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_657,plain,(
    ! [A_104,A_105,C_106,B_107] :
      ( k1_xboole_0 = A_104
      | k1_tarski(A_105) = A_104
      | k2_xboole_0(C_106,B_107) != k1_tarski(A_105)
      | ~ r1_tarski(A_104,B_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_34])).

tff(c_672,plain,(
    ! [A_108,A_109] :
      ( k1_xboole_0 = A_108
      | k1_tarski(A_109) = A_108
      | k1_tarski(A_109) != '#skF_3'
      | ~ r1_tarski(A_108,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_657])).

tff(c_730,plain,(
    ! [A_119,A_120] :
      ( k1_xboole_0 = A_119
      | k1_tarski('#skF_1'(A_120)) = A_119
      | A_120 != '#skF_3'
      | ~ r1_tarski(A_119,'#skF_3')
      | ~ v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120)
      | ~ v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_672])).

tff(c_741,plain,(
    ! [A_120] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski('#skF_1'(A_120)) = '#skF_3'
      | A_120 != '#skF_3'
      | ~ v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120) ) ),
    inference(resolution,[status(thm)],[c_8,c_730])).

tff(c_744,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_14,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,k2_xboole_0(C_7,B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | ~ r1_tarski(B_39,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_537,plain,(
    ! [C_92,B_93,A_94] :
      ( k2_xboole_0(C_92,B_93) = A_94
      | ~ r1_tarski(k2_xboole_0(C_92,B_93),A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(resolution,[status(thm)],[c_10,c_125])).

tff(c_556,plain,(
    ! [A_10,A_94] :
      ( k2_xboole_0(A_10,k1_xboole_0) = A_94
      | ~ r1_tarski(A_10,A_94)
      | ~ r1_tarski(A_94,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_537])).

tff(c_568,plain,(
    ! [A_96,A_95] :
      ( A_96 = A_95
      | ~ r1_tarski(A_96,A_95)
      | ~ r1_tarski(A_95,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_556])).

tff(c_576,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_46,c_568])).

tff(c_583,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_576])).

tff(c_751,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_744,c_583])).

tff(c_768,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_751])).

tff(c_769,plain,(
    ! [A_120] :
      ( k1_tarski('#skF_1'(A_120)) = '#skF_3'
      | A_120 != '#skF_3'
      | ~ v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120) ) ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_772,plain,(
    ! [A_121] :
      ( k1_tarski('#skF_1'(A_121)) = '#skF_3'
      | A_121 != '#skF_3'
      | ~ v1_zfmisc_1(A_121)
      | v1_xboole_0(A_121) ) ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_213,plain,(
    ! [B_48,A_49,C_50] :
      ( k1_xboole_0 = B_48
      | k1_tarski(A_49) = B_48
      | k2_xboole_0(B_48,C_50) != k1_tarski(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_219,plain,(
    ! [A_49] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_49) = '#skF_2'
      | k1_tarski(A_49) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_213])).

tff(c_227,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_120,plain,(
    ! [A_37,A_38] :
      ( r1_tarski(A_37,A_38)
      | ~ r1_tarski(A_37,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_106])).

tff(c_124,plain,(
    ! [A_38] : r1_tarski(k1_xboole_0,A_38) ),
    inference(resolution,[status(thm)],[c_8,c_120])).

tff(c_246,plain,(
    ! [A_38] : r1_tarski('#skF_2',A_38) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_124])).

tff(c_16,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_65,plain,(
    ! [B_28,A_29] :
      ( r1_xboole_0(B_28,A_29)
      | ~ r1_xboole_0(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_68,plain,(
    ! [A_11] : r1_xboole_0(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_16,c_65])).

tff(c_248,plain,(
    ! [A_11] : r1_xboole_0('#skF_2',A_11) ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_68])).

tff(c_268,plain,(
    ! [A_56,B_57,C_58] :
      ( ~ r1_xboole_0(A_56,B_57)
      | ~ r1_tarski(C_58,B_57)
      | ~ r1_tarski(C_58,A_56)
      | v1_xboole_0(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_376,plain,(
    ! [C_70,A_71] :
      ( ~ r1_tarski(C_70,A_71)
      | ~ r1_tarski(C_70,'#skF_2')
      | v1_xboole_0(C_70) ) ),
    inference(resolution,[status(thm)],[c_248,c_268])).

tff(c_378,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_246,c_376])).

tff(c_385,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_378])).

tff(c_387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_385])).

tff(c_388,plain,(
    ! [A_49] :
      ( k1_tarski(A_49) = '#skF_2'
      | k1_tarski(A_49) != '#skF_3' ) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_816,plain,(
    ! [A_122] :
      ( k1_tarski('#skF_1'(A_122)) = '#skF_2'
      | A_122 != '#skF_3'
      | ~ v1_zfmisc_1(A_122)
      | v1_xboole_0(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_388])).

tff(c_850,plain,(
    ! [A_120] :
      ( '#skF_2' = '#skF_3'
      | A_120 != '#skF_3'
      | ~ v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120)
      | A_120 != '#skF_3'
      | ~ v1_zfmisc_1(A_120)
      | v1_xboole_0(A_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_816])).

tff(c_934,plain,(
    ! [A_135] :
      ( A_135 != '#skF_3'
      | ~ v1_zfmisc_1(A_135)
      | v1_xboole_0(A_135)
      | A_135 != '#skF_3'
      | ~ v1_zfmisc_1(A_135)
      | v1_xboole_0(A_135) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_850])).

tff(c_936,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_934])).

tff(c_939,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_936])).

tff(c_941,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_939])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.44  
% 3.01/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.44  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.01/1.44  
% 3.01/1.44  %Foreground sorts:
% 3.01/1.44  
% 3.01/1.44  
% 3.01/1.44  %Background operators:
% 3.01/1.44  
% 3.01/1.44  
% 3.01/1.44  %Foreground operators:
% 3.01/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.01/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.01/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.01/1.44  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.01/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.01/1.44  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.44  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.44  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.01/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.01/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.01/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.01/1.44  
% 3.17/1.46  tff(f_106, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 3.17/1.46  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.46  tff(f_92, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 3.17/1.46  tff(f_82, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.17/1.46  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.17/1.46  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.17/1.46  tff(f_75, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.17/1.46  tff(f_45, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.17/1.46  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.17/1.46  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.17/1.46  tff(f_57, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 3.17/1.46  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.17/1.46  tff(c_48, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.17/1.46  tff(c_44, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.17/1.46  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.46  tff(c_42, plain, (![A_20]: (m1_subset_1('#skF_1'(A_20), A_20) | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.17/1.46  tff(c_208, plain, (![A_46, B_47]: (k6_domain_1(A_46, B_47)=k1_tarski(B_47) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.17/1.46  tff(c_444, plain, (![A_86]: (k6_domain_1(A_86, '#skF_1'(A_86))=k1_tarski('#skF_1'(A_86)) | ~v1_zfmisc_1(A_86) | v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_42, c_208])).
% 3.17/1.46  tff(c_40, plain, (![A_20]: (k6_domain_1(A_20, '#skF_1'(A_20))=A_20 | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.17/1.46  tff(c_450, plain, (![A_86]: (k1_tarski('#skF_1'(A_86))=A_86 | ~v1_zfmisc_1(A_86) | v1_xboole_0(A_86) | ~v1_zfmisc_1(A_86) | v1_xboole_0(A_86))), inference(superposition, [status(thm), theory('equality')], [c_444, c_40])).
% 3.17/1.46  tff(c_46, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.17/1.46  tff(c_69, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.46  tff(c_77, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_46, c_69])).
% 3.17/1.46  tff(c_106, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, k2_xboole_0(C_35, B_36)) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.46  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.17/1.46  tff(c_459, plain, (![A_87, C_88, B_89]: (k2_xboole_0(A_87, k2_xboole_0(C_88, B_89))=k2_xboole_0(C_88, B_89) | ~r1_tarski(A_87, B_89))), inference(resolution, [status(thm)], [c_106, c_12])).
% 3.17/1.46  tff(c_34, plain, (![B_16, A_15, C_17]: (k1_xboole_0=B_16 | k1_tarski(A_15)=B_16 | k2_xboole_0(B_16, C_17)!=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.17/1.46  tff(c_657, plain, (![A_104, A_105, C_106, B_107]: (k1_xboole_0=A_104 | k1_tarski(A_105)=A_104 | k2_xboole_0(C_106, B_107)!=k1_tarski(A_105) | ~r1_tarski(A_104, B_107))), inference(superposition, [status(thm), theory('equality')], [c_459, c_34])).
% 3.17/1.46  tff(c_672, plain, (![A_108, A_109]: (k1_xboole_0=A_108 | k1_tarski(A_109)=A_108 | k1_tarski(A_109)!='#skF_3' | ~r1_tarski(A_108, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_77, c_657])).
% 3.17/1.46  tff(c_730, plain, (![A_119, A_120]: (k1_xboole_0=A_119 | k1_tarski('#skF_1'(A_120))=A_119 | A_120!='#skF_3' | ~r1_tarski(A_119, '#skF_3') | ~v1_zfmisc_1(A_120) | v1_xboole_0(A_120) | ~v1_zfmisc_1(A_120) | v1_xboole_0(A_120))), inference(superposition, [status(thm), theory('equality')], [c_450, c_672])).
% 3.17/1.46  tff(c_741, plain, (![A_120]: (k1_xboole_0='#skF_3' | k1_tarski('#skF_1'(A_120))='#skF_3' | A_120!='#skF_3' | ~v1_zfmisc_1(A_120) | v1_xboole_0(A_120))), inference(resolution, [status(thm)], [c_8, c_730])).
% 3.17/1.46  tff(c_744, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_741])).
% 3.17/1.46  tff(c_14, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.17/1.46  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, k2_xboole_0(C_7, B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.46  tff(c_125, plain, (![B_39, A_40]: (B_39=A_40 | ~r1_tarski(B_39, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.46  tff(c_537, plain, (![C_92, B_93, A_94]: (k2_xboole_0(C_92, B_93)=A_94 | ~r1_tarski(k2_xboole_0(C_92, B_93), A_94) | ~r1_tarski(A_94, B_93))), inference(resolution, [status(thm)], [c_10, c_125])).
% 3.17/1.46  tff(c_556, plain, (![A_10, A_94]: (k2_xboole_0(A_10, k1_xboole_0)=A_94 | ~r1_tarski(A_10, A_94) | ~r1_tarski(A_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_537])).
% 3.17/1.46  tff(c_568, plain, (![A_96, A_95]: (A_96=A_95 | ~r1_tarski(A_96, A_95) | ~r1_tarski(A_95, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_556])).
% 3.17/1.46  tff(c_576, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_568])).
% 3.17/1.46  tff(c_583, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_44, c_576])).
% 3.17/1.46  tff(c_751, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_744, c_583])).
% 3.17/1.46  tff(c_768, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_751])).
% 3.17/1.46  tff(c_769, plain, (![A_120]: (k1_tarski('#skF_1'(A_120))='#skF_3' | A_120!='#skF_3' | ~v1_zfmisc_1(A_120) | v1_xboole_0(A_120))), inference(splitRight, [status(thm)], [c_741])).
% 3.17/1.46  tff(c_772, plain, (![A_121]: (k1_tarski('#skF_1'(A_121))='#skF_3' | A_121!='#skF_3' | ~v1_zfmisc_1(A_121) | v1_xboole_0(A_121))), inference(splitRight, [status(thm)], [c_741])).
% 3.17/1.46  tff(c_52, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.17/1.46  tff(c_213, plain, (![B_48, A_49, C_50]: (k1_xboole_0=B_48 | k1_tarski(A_49)=B_48 | k2_xboole_0(B_48, C_50)!=k1_tarski(A_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.17/1.46  tff(c_219, plain, (![A_49]: (k1_xboole_0='#skF_2' | k1_tarski(A_49)='#skF_2' | k1_tarski(A_49)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_77, c_213])).
% 3.17/1.46  tff(c_227, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_219])).
% 3.17/1.46  tff(c_120, plain, (![A_37, A_38]: (r1_tarski(A_37, A_38) | ~r1_tarski(A_37, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_106])).
% 3.17/1.46  tff(c_124, plain, (![A_38]: (r1_tarski(k1_xboole_0, A_38))), inference(resolution, [status(thm)], [c_8, c_120])).
% 3.17/1.46  tff(c_246, plain, (![A_38]: (r1_tarski('#skF_2', A_38))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_124])).
% 3.17/1.46  tff(c_16, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.17/1.46  tff(c_65, plain, (![B_28, A_29]: (r1_xboole_0(B_28, A_29) | ~r1_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.17/1.46  tff(c_68, plain, (![A_11]: (r1_xboole_0(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_16, c_65])).
% 3.17/1.46  tff(c_248, plain, (![A_11]: (r1_xboole_0('#skF_2', A_11))), inference(demodulation, [status(thm), theory('equality')], [c_227, c_68])).
% 3.17/1.46  tff(c_268, plain, (![A_56, B_57, C_58]: (~r1_xboole_0(A_56, B_57) | ~r1_tarski(C_58, B_57) | ~r1_tarski(C_58, A_56) | v1_xboole_0(C_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.17/1.46  tff(c_376, plain, (![C_70, A_71]: (~r1_tarski(C_70, A_71) | ~r1_tarski(C_70, '#skF_2') | v1_xboole_0(C_70))), inference(resolution, [status(thm)], [c_248, c_268])).
% 3.17/1.46  tff(c_378, plain, (~r1_tarski('#skF_2', '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_246, c_376])).
% 3.17/1.46  tff(c_385, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_378])).
% 3.17/1.46  tff(c_387, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_385])).
% 3.17/1.46  tff(c_388, plain, (![A_49]: (k1_tarski(A_49)='#skF_2' | k1_tarski(A_49)!='#skF_3')), inference(splitRight, [status(thm)], [c_219])).
% 3.17/1.46  tff(c_816, plain, (![A_122]: (k1_tarski('#skF_1'(A_122))='#skF_2' | A_122!='#skF_3' | ~v1_zfmisc_1(A_122) | v1_xboole_0(A_122))), inference(superposition, [status(thm), theory('equality')], [c_772, c_388])).
% 3.17/1.46  tff(c_850, plain, (![A_120]: ('#skF_2'='#skF_3' | A_120!='#skF_3' | ~v1_zfmisc_1(A_120) | v1_xboole_0(A_120) | A_120!='#skF_3' | ~v1_zfmisc_1(A_120) | v1_xboole_0(A_120))), inference(superposition, [status(thm), theory('equality')], [c_769, c_816])).
% 3.17/1.46  tff(c_934, plain, (![A_135]: (A_135!='#skF_3' | ~v1_zfmisc_1(A_135) | v1_xboole_0(A_135) | A_135!='#skF_3' | ~v1_zfmisc_1(A_135) | v1_xboole_0(A_135))), inference(negUnitSimplification, [status(thm)], [c_44, c_850])).
% 3.17/1.46  tff(c_936, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_48, c_934])).
% 3.17/1.46  tff(c_939, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_936])).
% 3.17/1.46  tff(c_941, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_939])).
% 3.17/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/1.46  
% 3.17/1.46  Inference rules
% 3.17/1.46  ----------------------
% 3.17/1.46  #Ref     : 1
% 3.17/1.46  #Sup     : 212
% 3.17/1.46  #Fact    : 0
% 3.17/1.46  #Define  : 0
% 3.17/1.46  #Split   : 2
% 3.17/1.46  #Chain   : 0
% 3.17/1.46  #Close   : 0
% 3.17/1.46  
% 3.17/1.46  Ordering : KBO
% 3.17/1.46  
% 3.17/1.46  Simplification rules
% 3.17/1.46  ----------------------
% 3.17/1.46  #Subsume      : 47
% 3.17/1.46  #Demod        : 89
% 3.17/1.46  #Tautology    : 95
% 3.17/1.46  #SimpNegUnit  : 9
% 3.17/1.46  #BackRed      : 30
% 3.17/1.46  
% 3.17/1.46  #Partial instantiations: 0
% 3.17/1.46  #Strategies tried      : 1
% 3.17/1.46  
% 3.17/1.46  Timing (in seconds)
% 3.17/1.46  ----------------------
% 3.17/1.46  Preprocessing        : 0.31
% 3.17/1.46  Parsing              : 0.16
% 3.17/1.46  CNF conversion       : 0.02
% 3.17/1.46  Main loop            : 0.38
% 3.17/1.46  Inferencing          : 0.13
% 3.17/1.46  Reduction            : 0.11
% 3.17/1.46  Demodulation         : 0.07
% 3.17/1.46  BG Simplification    : 0.02
% 3.17/1.46  Subsumption          : 0.10
% 3.17/1.46  Abstraction          : 0.02
% 3.17/1.46  MUC search           : 0.00
% 3.17/1.46  Cooper               : 0.00
% 3.17/1.46  Total                : 0.72
% 3.17/1.46  Index Insertion      : 0.00
% 3.17/1.46  Index Deletion       : 0.00
% 3.17/1.46  Index Matching       : 0.00
% 3.17/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
