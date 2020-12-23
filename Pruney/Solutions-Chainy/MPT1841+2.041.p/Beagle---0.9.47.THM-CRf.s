%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:33 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 152 expanded)
%              Number of leaves         :   30 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  125 ( 305 expanded)
%              Number of equality atoms :   23 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_100,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_62,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,(
    ! [D_34,A_35] : r2_hidden(D_34,k2_tarski(A_35,D_34)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_71,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_68])).

tff(c_38,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(A_17,k1_zfmisc_1(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_123,plain,(
    ! [C_52,B_53,A_54] :
      ( ~ v1_xboole_0(C_52)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(C_52))
      | ~ r2_hidden(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_137,plain,(
    ! [B_59,A_60,A_61] :
      ( ~ v1_xboole_0(B_59)
      | ~ r2_hidden(A_60,A_61)
      | ~ r1_tarski(A_61,B_59) ) ),
    inference(resolution,[status(thm)],[c_38,c_123])).

tff(c_147,plain,(
    ! [B_62,A_63] :
      ( ~ v1_xboole_0(B_62)
      | ~ r1_tarski(k1_tarski(A_63),B_62) ) ),
    inference(resolution,[status(thm)],[c_71,c_137])).

tff(c_152,plain,(
    ! [A_63] : ~ v1_xboole_0(k1_tarski(A_63)) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_54,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_48,plain,(
    v1_zfmisc_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_52,plain,(
    m1_subset_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_154,plain,(
    ! [A_65,B_66] :
      ( k6_domain_1(A_65,B_66) = k1_tarski(B_66)
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_163,plain,
    ( k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_154])).

tff(c_168,plain,(
    k6_domain_1('#skF_4','#skF_5') = k1_tarski('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_163])).

tff(c_182,plain,(
    ! [A_70,B_71] :
      ( m1_subset_1(k6_domain_1(A_70,B_71),k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_71,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_193,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | ~ m1_subset_1('#skF_5','#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_182])).

tff(c_198,plain,
    ( m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4'))
    | v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_193])).

tff(c_199,plain,(
    m1_subset_1(k1_tarski('#skF_5'),k1_zfmisc_1('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_198])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(A_17,B_18)
      | ~ m1_subset_1(A_17,k1_zfmisc_1(B_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_213,plain,(
    r1_tarski(k1_tarski('#skF_5'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_199,c_36])).

tff(c_222,plain,(
    ! [B_74,A_75] :
      ( B_74 = A_75
      | ~ r1_tarski(A_75,B_74)
      | ~ v1_zfmisc_1(B_74)
      | v1_xboole_0(B_74)
      | v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_225,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ v1_zfmisc_1('#skF_4')
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_213,c_222])).

tff(c_234,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | v1_xboole_0('#skF_4')
    | v1_xboole_0(k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_225])).

tff(c_235,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_54,c_234])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_220,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_213,c_2])).

tff(c_221,plain,(
    ~ r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_220])).

tff(c_284,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_235,c_221])).

tff(c_285,plain,(
    k1_tarski('#skF_5') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_220])).

tff(c_50,plain,(
    v1_subset_1(k6_domain_1('#skF_4','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_169,plain,(
    v1_subset_1(k1_tarski('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_50])).

tff(c_289,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_169])).

tff(c_34,plain,(
    ! [A_15] : m1_subset_1('#skF_3'(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_78,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(A_39,B_40)
      | ~ m1_subset_1(A_39,k1_zfmisc_1(B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_82,plain,(
    ! [A_15] : r1_tarski('#skF_3'(A_15),A_15) ),
    inference(resolution,[status(thm)],[c_34,c_78])).

tff(c_309,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(A_77,B_76)
      | ~ v1_zfmisc_1(B_76)
      | v1_xboole_0(B_76)
      | v1_xboole_0(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_401,plain,(
    ! [A_87] :
      ( '#skF_3'(A_87) = A_87
      | ~ v1_zfmisc_1(A_87)
      | v1_xboole_0(A_87)
      | v1_xboole_0('#skF_3'(A_87)) ) ),
    inference(resolution,[status(thm)],[c_82,c_309])).

tff(c_32,plain,(
    ! [A_15] : ~ v1_subset_1('#skF_3'(A_15),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_356,plain,(
    ! [B_80,A_81] :
      ( ~ v1_xboole_0(B_80)
      | v1_subset_1(B_80,A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_368,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_3'(A_15))
      | v1_subset_1('#skF_3'(A_15),A_15)
      | v1_xboole_0(A_15) ) ),
    inference(resolution,[status(thm)],[c_34,c_356])).

tff(c_376,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0('#skF_3'(A_15))
      | v1_xboole_0(A_15) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_368])).

tff(c_406,plain,(
    ! [A_88] :
      ( '#skF_3'(A_88) = A_88
      | ~ v1_zfmisc_1(A_88)
      | v1_xboole_0(A_88) ) ),
    inference(resolution,[status(thm)],[c_401,c_376])).

tff(c_409,plain,
    ( '#skF_3'('#skF_4') = '#skF_4'
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_406])).

tff(c_412,plain,(
    '#skF_3'('#skF_4') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_409])).

tff(c_431,plain,(
    ~ v1_subset_1('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_32])).

tff(c_441,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.37  
% 2.59/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.38  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.59/1.38  
% 2.59/1.38  %Foreground sorts:
% 2.59/1.38  
% 2.59/1.38  
% 2.59/1.38  %Background operators:
% 2.59/1.38  
% 2.59/1.38  
% 2.59/1.38  %Foreground operators:
% 2.59/1.38  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.59/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.59/1.38  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.59/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.59/1.38  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.59/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.59/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.59/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.59/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.59/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.59/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.38  tff('#skF_3', type, '#skF_3': $i > $i).
% 2.59/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.38  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.59/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.59/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.38  
% 2.59/1.39  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.59/1.39  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.59/1.39  tff(f_40, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.59/1.39  tff(f_66, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.59/1.39  tff(f_73, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.59/1.39  tff(f_112, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.59/1.39  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.59/1.39  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.59/1.39  tff(f_100, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.59/1.39  tff(f_62, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.59/1.39  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.59/1.39  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.39  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.59/1.39  tff(c_68, plain, (![D_34, A_35]: (r2_hidden(D_34, k2_tarski(A_35, D_34)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.59/1.39  tff(c_71, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_68])).
% 2.59/1.39  tff(c_38, plain, (![A_17, B_18]: (m1_subset_1(A_17, k1_zfmisc_1(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.59/1.39  tff(c_123, plain, (![C_52, B_53, A_54]: (~v1_xboole_0(C_52) | ~m1_subset_1(B_53, k1_zfmisc_1(C_52)) | ~r2_hidden(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.59/1.39  tff(c_137, plain, (![B_59, A_60, A_61]: (~v1_xboole_0(B_59) | ~r2_hidden(A_60, A_61) | ~r1_tarski(A_61, B_59))), inference(resolution, [status(thm)], [c_38, c_123])).
% 2.59/1.39  tff(c_147, plain, (![B_62, A_63]: (~v1_xboole_0(B_62) | ~r1_tarski(k1_tarski(A_63), B_62))), inference(resolution, [status(thm)], [c_71, c_137])).
% 2.59/1.39  tff(c_152, plain, (![A_63]: (~v1_xboole_0(k1_tarski(A_63)))), inference(resolution, [status(thm)], [c_6, c_147])).
% 2.59/1.39  tff(c_54, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.59/1.39  tff(c_48, plain, (v1_zfmisc_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.59/1.39  tff(c_52, plain, (m1_subset_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.59/1.39  tff(c_154, plain, (![A_65, B_66]: (k6_domain_1(A_65, B_66)=k1_tarski(B_66) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.59/1.39  tff(c_163, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_154])).
% 2.59/1.39  tff(c_168, plain, (k6_domain_1('#skF_4', '#skF_5')=k1_tarski('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_163])).
% 2.59/1.39  tff(c_182, plain, (![A_70, B_71]: (m1_subset_1(k6_domain_1(A_70, B_71), k1_zfmisc_1(A_70)) | ~m1_subset_1(B_71, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.59/1.39  tff(c_193, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | ~m1_subset_1('#skF_5', '#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_168, c_182])).
% 2.59/1.39  tff(c_198, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4')) | v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_193])).
% 2.59/1.39  tff(c_199, plain, (m1_subset_1(k1_tarski('#skF_5'), k1_zfmisc_1('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_54, c_198])).
% 2.59/1.39  tff(c_36, plain, (![A_17, B_18]: (r1_tarski(A_17, B_18) | ~m1_subset_1(A_17, k1_zfmisc_1(B_18)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.59/1.39  tff(c_213, plain, (r1_tarski(k1_tarski('#skF_5'), '#skF_4')), inference(resolution, [status(thm)], [c_199, c_36])).
% 2.59/1.39  tff(c_222, plain, (![B_74, A_75]: (B_74=A_75 | ~r1_tarski(A_75, B_74) | ~v1_zfmisc_1(B_74) | v1_xboole_0(B_74) | v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.59/1.39  tff(c_225, plain, (k1_tarski('#skF_5')='#skF_4' | ~v1_zfmisc_1('#skF_4') | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_213, c_222])).
% 2.59/1.39  tff(c_234, plain, (k1_tarski('#skF_5')='#skF_4' | v1_xboole_0('#skF_4') | v1_xboole_0(k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_225])).
% 2.59/1.39  tff(c_235, plain, (k1_tarski('#skF_5')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_152, c_54, c_234])).
% 2.59/1.39  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.59/1.39  tff(c_220, plain, (k1_tarski('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_213, c_2])).
% 2.59/1.39  tff(c_221, plain, (~r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(splitLeft, [status(thm)], [c_220])).
% 2.59/1.39  tff(c_284, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_235, c_221])).
% 2.59/1.39  tff(c_285, plain, (k1_tarski('#skF_5')='#skF_4'), inference(splitRight, [status(thm)], [c_220])).
% 2.59/1.39  tff(c_50, plain, (v1_subset_1(k6_domain_1('#skF_4', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_112])).
% 2.59/1.39  tff(c_169, plain, (v1_subset_1(k1_tarski('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_50])).
% 2.59/1.39  tff(c_289, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_169])).
% 2.59/1.39  tff(c_34, plain, (![A_15]: (m1_subset_1('#skF_3'(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.59/1.39  tff(c_78, plain, (![A_39, B_40]: (r1_tarski(A_39, B_40) | ~m1_subset_1(A_39, k1_zfmisc_1(B_40)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.59/1.39  tff(c_82, plain, (![A_15]: (r1_tarski('#skF_3'(A_15), A_15))), inference(resolution, [status(thm)], [c_34, c_78])).
% 2.59/1.39  tff(c_309, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(A_77, B_76) | ~v1_zfmisc_1(B_76) | v1_xboole_0(B_76) | v1_xboole_0(A_77))), inference(cnfTransformation, [status(thm)], [f_100])).
% 2.59/1.39  tff(c_401, plain, (![A_87]: ('#skF_3'(A_87)=A_87 | ~v1_zfmisc_1(A_87) | v1_xboole_0(A_87) | v1_xboole_0('#skF_3'(A_87)))), inference(resolution, [status(thm)], [c_82, c_309])).
% 2.59/1.39  tff(c_32, plain, (![A_15]: (~v1_subset_1('#skF_3'(A_15), A_15))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.59/1.39  tff(c_356, plain, (![B_80, A_81]: (~v1_xboole_0(B_80) | v1_subset_1(B_80, A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.59/1.39  tff(c_368, plain, (![A_15]: (~v1_xboole_0('#skF_3'(A_15)) | v1_subset_1('#skF_3'(A_15), A_15) | v1_xboole_0(A_15))), inference(resolution, [status(thm)], [c_34, c_356])).
% 2.59/1.39  tff(c_376, plain, (![A_15]: (~v1_xboole_0('#skF_3'(A_15)) | v1_xboole_0(A_15))), inference(negUnitSimplification, [status(thm)], [c_32, c_368])).
% 2.59/1.39  tff(c_406, plain, (![A_88]: ('#skF_3'(A_88)=A_88 | ~v1_zfmisc_1(A_88) | v1_xboole_0(A_88))), inference(resolution, [status(thm)], [c_401, c_376])).
% 2.59/1.39  tff(c_409, plain, ('#skF_3'('#skF_4')='#skF_4' | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_48, c_406])).
% 2.59/1.39  tff(c_412, plain, ('#skF_3'('#skF_4')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_54, c_409])).
% 2.59/1.39  tff(c_431, plain, (~v1_subset_1('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_412, c_32])).
% 2.59/1.39  tff(c_441, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_289, c_431])).
% 2.59/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/1.39  
% 2.59/1.39  Inference rules
% 2.59/1.39  ----------------------
% 2.59/1.39  #Ref     : 0
% 2.59/1.39  #Sup     : 88
% 2.59/1.39  #Fact    : 0
% 2.59/1.39  #Define  : 0
% 2.59/1.39  #Split   : 2
% 2.59/1.39  #Chain   : 0
% 2.59/1.39  #Close   : 0
% 2.59/1.39  
% 2.59/1.39  Ordering : KBO
% 2.59/1.39  
% 2.59/1.39  Simplification rules
% 2.59/1.39  ----------------------
% 2.59/1.39  #Subsume      : 16
% 2.59/1.39  #Demod        : 37
% 2.59/1.39  #Tautology    : 37
% 2.59/1.39  #SimpNegUnit  : 10
% 2.59/1.39  #BackRed      : 9
% 2.59/1.39  
% 2.59/1.39  #Partial instantiations: 0
% 2.59/1.39  #Strategies tried      : 1
% 2.59/1.39  
% 2.59/1.39  Timing (in seconds)
% 2.59/1.39  ----------------------
% 2.59/1.40  Preprocessing        : 0.34
% 2.59/1.40  Parsing              : 0.18
% 2.59/1.40  CNF conversion       : 0.02
% 2.59/1.40  Main loop            : 0.24
% 2.59/1.40  Inferencing          : 0.09
% 2.59/1.40  Reduction            : 0.07
% 2.59/1.40  Demodulation         : 0.05
% 2.59/1.40  BG Simplification    : 0.02
% 2.59/1.40  Subsumption          : 0.05
% 2.59/1.40  Abstraction          : 0.01
% 2.59/1.40  MUC search           : 0.00
% 2.59/1.40  Cooper               : 0.00
% 2.59/1.40  Total                : 0.61
% 2.59/1.40  Index Insertion      : 0.00
% 2.59/1.40  Index Deletion       : 0.00
% 2.59/1.40  Index Matching       : 0.00
% 2.59/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
