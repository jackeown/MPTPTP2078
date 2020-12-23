%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:19 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 112 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   95 ( 234 expanded)
%              Number of equality atoms :   39 (  85 expanded)
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

tff(f_99,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    ! [A_21] :
      ( m1_subset_1('#skF_1'(A_21),A_21)
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_212,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_252,plain,(
    ! [A_66] :
      ( k6_domain_1(A_66,'#skF_1'(A_66)) = k1_tarski('#skF_1'(A_66))
      | ~ v1_zfmisc_1(A_66)
      | v1_xboole_0(A_66) ) ),
    inference(resolution,[status(thm)],[c_32,c_212])).

tff(c_30,plain,(
    ! [A_21] :
      ( k6_domain_1(A_21,'#skF_1'(A_21)) = A_21
      | ~ v1_zfmisc_1(A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_267,plain,(
    ! [A_67] :
      ( k1_tarski('#skF_1'(A_67)) = A_67
      | ~ v1_zfmisc_1(A_67)
      | v1_xboole_0(A_67)
      | ~ v1_zfmisc_1(A_67)
      | v1_xboole_0(A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_30])).

tff(c_34,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_36,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_145,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_157,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_145])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_169,plain,(
    ! [B_48,A_49] :
      ( ~ r1_xboole_0(B_48,A_49)
      | ~ r1_tarski(B_48,A_49)
      | v1_xboole_0(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_195,plain,(
    ! [A_54,B_55] :
      ( ~ r1_tarski(A_54,B_55)
      | v1_xboole_0(A_54)
      | k4_xboole_0(A_54,B_55) != A_54 ) ),
    inference(resolution,[status(thm)],[c_16,c_169])).

tff(c_204,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_195])).

tff(c_210,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_204])).

tff(c_211,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_210])).

tff(c_67,plain,(
    ! [A_31,B_32] :
      ( k2_xboole_0(A_31,B_32) = B_32
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_75,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_67])).

tff(c_228,plain,(
    ! [C_60,B_61,A_62] :
      ( k1_xboole_0 = C_60
      | k1_xboole_0 = B_61
      | C_60 = B_61
      | k2_xboole_0(B_61,C_60) != k1_tarski(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_234,plain,(
    ! [A_62] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_62) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_228])).

tff(c_242,plain,(
    ! [A_62] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski(A_62) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_211,c_234])).

tff(c_245,plain,(
    ! [A_62] : k1_tarski(A_62) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_295,plain,(
    ! [A_69] :
      ( A_69 != '#skF_3'
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69)
      | ~ v1_zfmisc_1(A_69)
      | v1_xboole_0(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_245])).

tff(c_297,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_295])).

tff(c_300,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_297])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_300])).

tff(c_303,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_10,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_156,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_145])).

tff(c_201,plain,(
    ! [A_6] :
      ( v1_xboole_0(k1_xboole_0)
      | k4_xboole_0(k1_xboole_0,A_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_195])).

tff(c_208,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_201])).

tff(c_307,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_303,c_208])).

tff(c_320,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_307])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:20:53 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.35  
% 2.28/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.35  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.28/1.35  
% 2.28/1.35  %Foreground sorts:
% 2.28/1.35  
% 2.28/1.35  
% 2.28/1.35  %Background operators:
% 2.28/1.35  
% 2.28/1.35  
% 2.28/1.35  %Foreground operators:
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.28/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.28/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.28/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.35  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.28/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.35  
% 2.28/1.37  tff(f_99, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.28/1.37  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.28/1.37  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.28/1.37  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.28/1.37  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.28/1.37  tff(f_45, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.28/1.37  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.28/1.37  tff(f_65, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.28/1.37  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.28/1.37  tff(c_40, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.28/1.37  tff(c_38, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.28/1.37  tff(c_32, plain, (![A_21]: (m1_subset_1('#skF_1'(A_21), A_21) | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.28/1.37  tff(c_212, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.28/1.37  tff(c_252, plain, (![A_66]: (k6_domain_1(A_66, '#skF_1'(A_66))=k1_tarski('#skF_1'(A_66)) | ~v1_zfmisc_1(A_66) | v1_xboole_0(A_66))), inference(resolution, [status(thm)], [c_32, c_212])).
% 2.28/1.37  tff(c_30, plain, (![A_21]: (k6_domain_1(A_21, '#skF_1'(A_21))=A_21 | ~v1_zfmisc_1(A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.28/1.37  tff(c_267, plain, (![A_67]: (k1_tarski('#skF_1'(A_67))=A_67 | ~v1_zfmisc_1(A_67) | v1_xboole_0(A_67) | ~v1_zfmisc_1(A_67) | v1_xboole_0(A_67))), inference(superposition, [status(thm), theory('equality')], [c_252, c_30])).
% 2.28/1.37  tff(c_34, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.28/1.37  tff(c_42, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.28/1.37  tff(c_36, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_99])).
% 2.28/1.37  tff(c_145, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.28/1.37  tff(c_157, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_145])).
% 2.28/1.37  tff(c_16, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.28/1.37  tff(c_169, plain, (![B_48, A_49]: (~r1_xboole_0(B_48, A_49) | ~r1_tarski(B_48, A_49) | v1_xboole_0(B_48))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.28/1.37  tff(c_195, plain, (![A_54, B_55]: (~r1_tarski(A_54, B_55) | v1_xboole_0(A_54) | k4_xboole_0(A_54, B_55)!=A_54)), inference(resolution, [status(thm)], [c_16, c_169])).
% 2.28/1.37  tff(c_204, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_36, c_195])).
% 2.28/1.37  tff(c_210, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_157, c_204])).
% 2.28/1.37  tff(c_211, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_210])).
% 2.28/1.37  tff(c_67, plain, (![A_31, B_32]: (k2_xboole_0(A_31, B_32)=B_32 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.37  tff(c_75, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_36, c_67])).
% 2.28/1.37  tff(c_228, plain, (![C_60, B_61, A_62]: (k1_xboole_0=C_60 | k1_xboole_0=B_61 | C_60=B_61 | k2_xboole_0(B_61, C_60)!=k1_tarski(A_62))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.28/1.37  tff(c_234, plain, (![A_62]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | '#skF_2'='#skF_3' | k1_tarski(A_62)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_75, c_228])).
% 2.28/1.37  tff(c_242, plain, (![A_62]: (k1_xboole_0='#skF_3' | k1_tarski(A_62)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_34, c_211, c_234])).
% 2.28/1.37  tff(c_245, plain, (![A_62]: (k1_tarski(A_62)!='#skF_3')), inference(splitLeft, [status(thm)], [c_242])).
% 2.28/1.37  tff(c_295, plain, (![A_69]: (A_69!='#skF_3' | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69) | ~v1_zfmisc_1(A_69) | v1_xboole_0(A_69))), inference(superposition, [status(thm), theory('equality')], [c_267, c_245])).
% 2.28/1.37  tff(c_297, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_38, c_295])).
% 2.28/1.37  tff(c_300, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_297])).
% 2.28/1.37  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_300])).
% 2.28/1.37  tff(c_303, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_242])).
% 2.28/1.37  tff(c_10, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.37  tff(c_156, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_145])).
% 2.28/1.37  tff(c_201, plain, (![A_6]: (v1_xboole_0(k1_xboole_0) | k4_xboole_0(k1_xboole_0, A_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_195])).
% 2.28/1.37  tff(c_208, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_156, c_201])).
% 2.28/1.37  tff(c_307, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_303, c_208])).
% 2.28/1.37  tff(c_320, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_307])).
% 2.28/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.37  
% 2.28/1.37  Inference rules
% 2.28/1.37  ----------------------
% 2.28/1.37  #Ref     : 0
% 2.28/1.37  #Sup     : 59
% 2.28/1.37  #Fact    : 0
% 2.28/1.37  #Define  : 0
% 2.28/1.37  #Split   : 1
% 2.28/1.37  #Chain   : 0
% 2.28/1.37  #Close   : 0
% 2.28/1.37  
% 2.28/1.37  Ordering : KBO
% 2.28/1.37  
% 2.28/1.37  Simplification rules
% 2.28/1.37  ----------------------
% 2.28/1.37  #Subsume      : 2
% 2.28/1.37  #Demod        : 26
% 2.28/1.37  #Tautology    : 35
% 2.28/1.37  #SimpNegUnit  : 6
% 2.28/1.37  #BackRed      : 15
% 2.28/1.37  
% 2.28/1.37  #Partial instantiations: 0
% 2.28/1.37  #Strategies tried      : 1
% 2.28/1.37  
% 2.28/1.37  Timing (in seconds)
% 2.28/1.37  ----------------------
% 2.39/1.37  Preprocessing        : 0.36
% 2.39/1.37  Parsing              : 0.18
% 2.39/1.37  CNF conversion       : 0.02
% 2.39/1.37  Main loop            : 0.20
% 2.39/1.37  Inferencing          : 0.08
% 2.39/1.37  Reduction            : 0.06
% 2.39/1.37  Demodulation         : 0.04
% 2.39/1.37  BG Simplification    : 0.02
% 2.39/1.37  Subsumption          : 0.03
% 2.39/1.37  Abstraction          : 0.01
% 2.39/1.37  MUC search           : 0.00
% 2.39/1.37  Cooper               : 0.00
% 2.39/1.37  Total                : 0.59
% 2.39/1.37  Index Insertion      : 0.00
% 2.39/1.37  Index Deletion       : 0.00
% 2.39/1.37  Index Matching       : 0.00
% 2.39/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
