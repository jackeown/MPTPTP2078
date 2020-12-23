%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:20 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 137 expanded)
%              Number of leaves         :   29 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  102 ( 260 expanded)
%              Number of equality atoms :   48 ( 114 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_83,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_32,plain,(
    ! [A_21] :
      ( m1_subset_1('#skF_1'(A_21),A_21)
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_184,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_220,plain,(
    ! [A_63] :
      ( k6_domain_1(A_63,'#skF_1'(A_63)) = k1_tarski('#skF_1'(A_63))
      | ~ v1_zfmisc_1(A_63)
      | v1_xboole_0(A_63) ) ),
    inference(resolution,[status(thm)],[c_32,c_184])).

tff(c_30,plain,(
    ! [A_21] :
      ( k6_domain_1(A_21,'#skF_1'(A_21)) = A_21
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_235,plain,(
    ! [A_64] :
      ( k1_tarski('#skF_1'(A_64)) = A_64
      | ~ v1_zfmisc_1(A_64)
      | v1_xboole_0(A_64)
      | ~ v1_zfmisc_1(A_64)
      | v1_xboole_0(A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_30])).

tff(c_34,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_73,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = k1_xboole_0
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_73])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [B_44,A_45] :
      ( ~ r1_xboole_0(B_44,A_45)
      | ~ r1_tarski(B_44,A_45)
      | v1_xboole_0(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_173,plain,(
    ! [A_51,B_52] :
      ( ~ r1_tarski(A_51,B_52)
      | v1_xboole_0(A_51)
      | k4_xboole_0(A_51,B_52) != A_51 ) ),
    inference(resolution,[status(thm)],[c_14,c_128])).

tff(c_179,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_173])).

tff(c_182,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_179])).

tff(c_183,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_182])).

tff(c_6,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_4] : k4_xboole_0(k1_xboole_0,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_134,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k4_xboole_0(B_48,A_47)) = k2_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_146,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = k2_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_134])).

tff(c_149,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_146])).

tff(c_143,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_134])).

tff(c_159,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_143])).

tff(c_205,plain,(
    ! [C_59,B_60,A_61] :
      ( k1_xboole_0 = C_59
      | k1_xboole_0 = B_60
      | C_59 = B_60
      | k2_xboole_0(B_60,C_59) != k1_tarski(A_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_208,plain,(
    ! [A_61] :
      ( k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = '#skF_3'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_61) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_205])).

tff(c_215,plain,(
    ! [A_61] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski(A_61) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_183,c_208])).

tff(c_218,plain,(
    ! [A_61] : k1_tarski(A_61) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_263,plain,(
    ! [A_66] :
      ( A_66 != '#skF_3'
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66)
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_218])).

tff(c_265,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_263])).

tff(c_268,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_265])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_268])).

tff(c_271,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_189,plain,(
    ! [A_55,B_56] :
      ( v1_xboole_0(A_55)
      | k4_xboole_0(A_55,B_56) != A_55
      | k4_xboole_0(A_55,B_56) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_173])).

tff(c_193,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_xboole_0)
      | k4_xboole_0(k1_xboole_0,A_4) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_189])).

tff(c_199,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_193])).

tff(c_273,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_199])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.32  
% 2.26/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.33  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.26/1.33  
% 2.26/1.33  %Foreground sorts:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Background operators:
% 2.26/1.33  
% 2.26/1.33  
% 2.26/1.33  %Foreground operators:
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.26/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.26/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.26/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.26/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.26/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.26/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.26/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.26/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.26/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.26/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.26/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.26/1.33  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.26/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.26/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.26/1.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.26/1.33  
% 2.26/1.34  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.26/1.34  tff(f_83, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.26/1.34  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.26/1.34  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.26/1.34  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.26/1.34  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.26/1.34  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.26/1.34  tff(f_33, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.26/1.34  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.26/1.34  tff(f_63, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.26/1.34  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.34  tff(c_38, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.34  tff(c_32, plain, (![A_21]: (m1_subset_1('#skF_1'(A_21), A_21) | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.26/1.34  tff(c_184, plain, (![A_53, B_54]: (k6_domain_1(A_53, B_54)=k1_tarski(B_54) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.26/1.34  tff(c_220, plain, (![A_63]: (k6_domain_1(A_63, '#skF_1'(A_63))=k1_tarski('#skF_1'(A_63)) | ~v1_zfmisc_1(A_63) | v1_xboole_0(A_63))), inference(resolution, [status(thm)], [c_32, c_184])).
% 2.26/1.34  tff(c_30, plain, (![A_21]: (k6_domain_1(A_21, '#skF_1'(A_21))=A_21 | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.26/1.34  tff(c_235, plain, (![A_64]: (k1_tarski('#skF_1'(A_64))=A_64 | ~v1_zfmisc_1(A_64) | v1_xboole_0(A_64) | ~v1_zfmisc_1(A_64) | v1_xboole_0(A_64))), inference(superposition, [status(thm), theory('equality')], [c_220, c_30])).
% 2.26/1.34  tff(c_34, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.34  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.34  tff(c_36, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.26/1.34  tff(c_73, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=k1_xboole_0 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.34  tff(c_77, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_73])).
% 2.26/1.34  tff(c_14, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=A_7)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.26/1.34  tff(c_128, plain, (![B_44, A_45]: (~r1_xboole_0(B_44, A_45) | ~r1_tarski(B_44, A_45) | v1_xboole_0(B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.26/1.34  tff(c_173, plain, (![A_51, B_52]: (~r1_tarski(A_51, B_52) | v1_xboole_0(A_51) | k4_xboole_0(A_51, B_52)!=A_51)), inference(resolution, [status(thm)], [c_14, c_128])).
% 2.26/1.34  tff(c_179, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_36, c_173])).
% 2.26/1.34  tff(c_182, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_179])).
% 2.26/1.34  tff(c_183, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_182])).
% 2.26/1.34  tff(c_6, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.26/1.34  tff(c_8, plain, (![A_4]: (k4_xboole_0(k1_xboole_0, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.34  tff(c_134, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k4_xboole_0(B_48, A_47))=k2_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.26/1.34  tff(c_146, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=k2_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_134])).
% 2.26/1.34  tff(c_149, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_146])).
% 2.26/1.34  tff(c_143, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_77, c_134])).
% 2.26/1.34  tff(c_159, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_143])).
% 2.26/1.34  tff(c_205, plain, (![C_59, B_60, A_61]: (k1_xboole_0=C_59 | k1_xboole_0=B_60 | C_59=B_60 | k2_xboole_0(B_60, C_59)!=k1_tarski(A_61))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.26/1.34  tff(c_208, plain, (![A_61]: (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | '#skF_2'='#skF_3' | k1_tarski(A_61)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_159, c_205])).
% 2.26/1.34  tff(c_215, plain, (![A_61]: (k1_xboole_0='#skF_3' | k1_tarski(A_61)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_183, c_208])).
% 2.26/1.34  tff(c_218, plain, (![A_61]: (k1_tarski(A_61)!='#skF_3')), inference(splitLeft, [status(thm)], [c_215])).
% 2.26/1.34  tff(c_263, plain, (![A_66]: (A_66!='#skF_3' | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66) | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66))), inference(superposition, [status(thm), theory('equality')], [c_235, c_218])).
% 2.26/1.34  tff(c_265, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_263])).
% 2.26/1.34  tff(c_268, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_265])).
% 2.26/1.34  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_268])).
% 2.26/1.34  tff(c_271, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_215])).
% 2.26/1.34  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.34  tff(c_189, plain, (![A_55, B_56]: (v1_xboole_0(A_55) | k4_xboole_0(A_55, B_56)!=A_55 | k4_xboole_0(A_55, B_56)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_173])).
% 2.26/1.34  tff(c_193, plain, (![A_4]: (v1_xboole_0(k1_xboole_0) | k4_xboole_0(k1_xboole_0, A_4)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_189])).
% 2.26/1.34  tff(c_199, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_193])).
% 2.26/1.34  tff(c_273, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_199])).
% 2.26/1.34  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_273])).
% 2.26/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.34  
% 2.26/1.34  Inference rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Ref     : 0
% 2.26/1.34  #Sup     : 53
% 2.26/1.34  #Fact    : 0
% 2.26/1.34  #Define  : 0
% 2.26/1.34  #Split   : 1
% 2.26/1.34  #Chain   : 0
% 2.26/1.34  #Close   : 0
% 2.26/1.34  
% 2.26/1.34  Ordering : KBO
% 2.26/1.34  
% 2.26/1.34  Simplification rules
% 2.26/1.34  ----------------------
% 2.26/1.34  #Subsume      : 2
% 2.26/1.34  #Demod        : 22
% 2.26/1.34  #Tautology    : 31
% 2.26/1.34  #SimpNegUnit  : 6
% 2.26/1.34  #BackRed      : 13
% 2.26/1.34  
% 2.26/1.34  #Partial instantiations: 0
% 2.26/1.34  #Strategies tried      : 1
% 2.26/1.34  
% 2.26/1.34  Timing (in seconds)
% 2.26/1.34  ----------------------
% 2.26/1.34  Preprocessing        : 0.33
% 2.26/1.34  Parsing              : 0.17
% 2.26/1.34  CNF conversion       : 0.02
% 2.26/1.35  Main loop            : 0.19
% 2.26/1.35  Inferencing          : 0.08
% 2.26/1.35  Reduction            : 0.06
% 2.26/1.35  Demodulation         : 0.04
% 2.26/1.35  BG Simplification    : 0.01
% 2.26/1.35  Subsumption          : 0.03
% 2.26/1.35  Abstraction          : 0.01
% 2.26/1.35  MUC search           : 0.00
% 2.26/1.35  Cooper               : 0.00
% 2.26/1.35  Total                : 0.56
% 2.26/1.35  Index Insertion      : 0.00
% 2.26/1.35  Index Deletion       : 0.00
% 2.26/1.35  Index Matching       : 0.00
% 2.26/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
