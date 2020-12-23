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
% DateTime   : Thu Dec  3 10:28:14 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 135 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :   14
%              Number of atoms          :  105 ( 215 expanded)
%              Number of equality atoms :   53 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_94,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_38,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_30,plain,(
    ! [A_20] :
      ( m1_subset_1('#skF_1'(A_20),A_20)
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_328,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_385,plain,(
    ! [A_65] :
      ( k6_domain_1(A_65,'#skF_1'(A_65)) = k1_tarski('#skF_1'(A_65))
      | ~ v1_zfmisc_1(A_65)
      | v1_xboole_0(A_65) ) ),
    inference(resolution,[status(thm)],[c_30,c_328])).

tff(c_28,plain,(
    ! [A_20] :
      ( k6_domain_1(A_20,'#skF_1'(A_20)) = A_20
      | ~ v1_zfmisc_1(A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_426,plain,(
    ! [A_69] :
      ( k1_tarski('#skF_1'(A_69)) = A_69
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69)
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_385,c_28])).

tff(c_32,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_16,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_93,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    ! [B_42,A_43] : k3_tarski(k2_tarski(B_42,A_43)) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_93])).

tff(c_20,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_20])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_194,plain,(
    ! [A_45] : k2_xboole_0(k1_xboole_0,A_45) = A_45 ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_6])).

tff(c_267,plain,(
    ! [A_48,B_49] : k2_xboole_0(A_48,k4_xboole_0(B_49,A_48)) = k2_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_274,plain,(
    ! [B_49] : k4_xboole_0(B_49,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_194])).

tff(c_286,plain,(
    ! [B_49] : k4_xboole_0(B_49,k1_xboole_0) = B_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_274])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_147,plain,(
    ! [B_40,A_41] :
      ( ~ r1_xboole_0(B_40,A_41)
      | ~ r1_tarski(B_40,A_41)
      | v1_xboole_0(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_317,plain,(
    ! [A_52,B_53] :
      ( ~ r1_tarski(A_52,B_53)
      | v1_xboole_0(A_52)
      | k4_xboole_0(A_52,B_53) != A_52 ) ),
    inference(resolution,[status(thm)],[c_14,c_147])).

tff(c_333,plain,(
    ! [A_56,B_57] :
      ( v1_xboole_0(A_56)
      | k4_xboole_0(A_56,B_57) != A_56
      | k4_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_317])).

tff(c_335,plain,(
    ! [B_49] :
      ( v1_xboole_0(B_49)
      | k4_xboole_0(B_49,k1_xboole_0) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_333])).

tff(c_344,plain,(
    ! [B_58] :
      ( v1_xboole_0(B_58)
      | k1_xboole_0 != B_58 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_335])).

tff(c_351,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(resolution,[status(thm)],[c_344,c_38])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_128,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_132,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_128])).

tff(c_323,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_317])).

tff(c_326,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_323])).

tff(c_327,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_326])).

tff(c_284,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_267])).

tff(c_289,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_284])).

tff(c_358,plain,(
    ! [C_61,B_62,A_63] :
      ( k1_xboole_0 = C_61
      | k1_xboole_0 = B_62
      | C_61 = B_62
      | k2_xboole_0(B_62,C_61) != k1_tarski(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_361,plain,(
    ! [A_63] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_3'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_63) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_358])).

tff(c_380,plain,(
    ! [A_63] : k1_tarski(A_63) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_351,c_327,c_361])).

tff(c_442,plain,(
    ! [A_70] :
      ( A_70 != '#skF_3'
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70)
      | ~ v1_zfmisc_1(A_70)
      | v1_xboole_0(A_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_380])).

tff(c_444,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_442])).

tff(c_447,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_444])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:54:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.27  
% 2.11/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.27  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.11/1.27  
% 2.11/1.27  %Foreground sorts:
% 2.11/1.27  
% 2.11/1.27  
% 2.11/1.27  %Background operators:
% 2.11/1.27  
% 2.11/1.27  
% 2.11/1.27  %Foreground operators:
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.11/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.27  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.27  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.11/1.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.11/1.27  
% 2.11/1.29  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.11/1.29  tff(f_80, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.11/1.29  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.11/1.29  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.11/1.29  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.11/1.29  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.11/1.29  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.11/1.29  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.11/1.29  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.11/1.29  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.11/1.29  tff(f_63, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.11/1.29  tff(c_38, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.11/1.29  tff(c_36, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.11/1.29  tff(c_30, plain, (![A_20]: (m1_subset_1('#skF_1'(A_20), A_20) | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.11/1.29  tff(c_328, plain, (![A_54, B_55]: (k6_domain_1(A_54, B_55)=k1_tarski(B_55) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.11/1.29  tff(c_385, plain, (![A_65]: (k6_domain_1(A_65, '#skF_1'(A_65))=k1_tarski('#skF_1'(A_65)) | ~v1_zfmisc_1(A_65) | v1_xboole_0(A_65))), inference(resolution, [status(thm)], [c_30, c_328])).
% 2.11/1.29  tff(c_28, plain, (![A_20]: (k6_domain_1(A_20, '#skF_1'(A_20))=A_20 | ~v1_zfmisc_1(A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.11/1.29  tff(c_426, plain, (![A_69]: (k1_tarski('#skF_1'(A_69))=A_69 | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69) | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69))), inference(superposition, [status(thm), theory('equality')], [c_385, c_28])).
% 2.11/1.29  tff(c_32, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.11/1.29  tff(c_16, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.11/1.29  tff(c_93, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.29  tff(c_152, plain, (![B_42, A_43]: (k3_tarski(k2_tarski(B_42, A_43))=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_16, c_93])).
% 2.11/1.29  tff(c_20, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.29  tff(c_178, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_152, c_20])).
% 2.11/1.29  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.29  tff(c_194, plain, (![A_45]: (k2_xboole_0(k1_xboole_0, A_45)=A_45)), inference(superposition, [status(thm), theory('equality')], [c_178, c_6])).
% 2.11/1.29  tff(c_267, plain, (![A_48, B_49]: (k2_xboole_0(A_48, k4_xboole_0(B_49, A_48))=k2_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.29  tff(c_274, plain, (![B_49]: (k4_xboole_0(B_49, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_49))), inference(superposition, [status(thm), theory('equality')], [c_267, c_194])).
% 2.11/1.29  tff(c_286, plain, (![B_49]: (k4_xboole_0(B_49, k1_xboole_0)=B_49)), inference(demodulation, [status(thm), theory('equality')], [c_194, c_274])).
% 2.11/1.29  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.29  tff(c_14, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.11/1.29  tff(c_147, plain, (![B_40, A_41]: (~r1_xboole_0(B_40, A_41) | ~r1_tarski(B_40, A_41) | v1_xboole_0(B_40))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.29  tff(c_317, plain, (![A_52, B_53]: (~r1_tarski(A_52, B_53) | v1_xboole_0(A_52) | k4_xboole_0(A_52, B_53)!=A_52)), inference(resolution, [status(thm)], [c_14, c_147])).
% 2.11/1.29  tff(c_333, plain, (![A_56, B_57]: (v1_xboole_0(A_56) | k4_xboole_0(A_56, B_57)!=A_56 | k4_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_317])).
% 2.11/1.29  tff(c_335, plain, (![B_49]: (v1_xboole_0(B_49) | k4_xboole_0(B_49, k1_xboole_0)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_286, c_333])).
% 2.11/1.29  tff(c_344, plain, (![B_58]: (v1_xboole_0(B_58) | k1_xboole_0!=B_58)), inference(demodulation, [status(thm), theory('equality')], [c_286, c_335])).
% 2.11/1.29  tff(c_351, plain, (k1_xboole_0!='#skF_3'), inference(resolution, [status(thm)], [c_344, c_38])).
% 2.11/1.29  tff(c_40, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.11/1.29  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.11/1.29  tff(c_128, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.11/1.29  tff(c_132, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_34, c_128])).
% 2.11/1.29  tff(c_323, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_34, c_317])).
% 2.11/1.29  tff(c_326, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_323])).
% 2.11/1.29  tff(c_327, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_326])).
% 2.11/1.29  tff(c_284, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_132, c_267])).
% 2.11/1.29  tff(c_289, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_284])).
% 2.11/1.29  tff(c_358, plain, (![C_61, B_62, A_63]: (k1_xboole_0=C_61 | k1_xboole_0=B_62 | C_61=B_62 | k2_xboole_0(B_62, C_61)!=k1_tarski(A_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.11/1.29  tff(c_361, plain, (![A_63]: (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | '#skF_2'='#skF_3' | k1_tarski(A_63)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_289, c_358])).
% 2.11/1.29  tff(c_380, plain, (![A_63]: (k1_tarski(A_63)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_351, c_327, c_361])).
% 2.11/1.29  tff(c_442, plain, (![A_70]: (A_70!='#skF_3' | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70) | ~v1_zfmisc_1(A_70) | v1_xboole_0(A_70))), inference(superposition, [status(thm), theory('equality')], [c_426, c_380])).
% 2.11/1.29  tff(c_444, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_36, c_442])).
% 2.11/1.29  tff(c_447, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_444])).
% 2.11/1.29  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_447])).
% 2.11/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  Inference rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Ref     : 0
% 2.11/1.29  #Sup     : 98
% 2.11/1.29  #Fact    : 0
% 2.11/1.29  #Define  : 0
% 2.11/1.29  #Split   : 0
% 2.11/1.29  #Chain   : 0
% 2.11/1.29  #Close   : 0
% 2.11/1.29  
% 2.11/1.29  Ordering : KBO
% 2.11/1.29  
% 2.11/1.29  Simplification rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Subsume      : 8
% 2.11/1.29  #Demod        : 20
% 2.11/1.29  #Tautology    : 67
% 2.11/1.29  #SimpNegUnit  : 5
% 2.11/1.29  #BackRed      : 0
% 2.11/1.29  
% 2.11/1.29  #Partial instantiations: 0
% 2.11/1.29  #Strategies tried      : 1
% 2.11/1.29  
% 2.11/1.29  Timing (in seconds)
% 2.11/1.29  ----------------------
% 2.11/1.29  Preprocessing        : 0.30
% 2.11/1.29  Parsing              : 0.16
% 2.11/1.29  CNF conversion       : 0.02
% 2.11/1.29  Main loop            : 0.23
% 2.11/1.29  Inferencing          : 0.10
% 2.11/1.29  Reduction            : 0.07
% 2.11/1.29  Demodulation         : 0.05
% 2.11/1.29  BG Simplification    : 0.01
% 2.11/1.29  Subsumption          : 0.03
% 2.11/1.29  Abstraction          : 0.01
% 2.11/1.29  MUC search           : 0.00
% 2.11/1.29  Cooper               : 0.00
% 2.11/1.29  Total                : 0.56
% 2.11/1.29  Index Insertion      : 0.00
% 2.11/1.29  Index Deletion       : 0.00
% 2.11/1.29  Index Matching       : 0.00
% 2.11/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
