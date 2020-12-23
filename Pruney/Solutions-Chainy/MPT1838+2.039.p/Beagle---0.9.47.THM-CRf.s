%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:19 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  71 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  104 ( 169 expanded)
%              Number of equality atoms :   42 (  56 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_80,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & ~ ( B = k1_tarski(A)
            & C = k1_tarski(A) )
        & ~ ( B = k1_xboole_0
            & C = k1_tarski(A) )
        & ~ ( B = k1_tarski(A)
            & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_40,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_34,plain,(
    ! [A_14] :
      ( m1_subset_1('#skF_1'(A_14),A_14)
      | ~ v1_zfmisc_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_97,plain,(
    ! [A_37,B_38] :
      ( k6_domain_1(A_37,B_38) = k1_tarski(B_38)
      | ~ m1_subset_1(B_38,A_37)
      | v1_xboole_0(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_115,plain,(
    ! [A_47] :
      ( k6_domain_1(A_47,'#skF_1'(A_47)) = k1_tarski('#skF_1'(A_47))
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_34,c_97])).

tff(c_32,plain,(
    ! [A_14] :
      ( k6_domain_1(A_14,'#skF_1'(A_14)) = A_14
      | ~ v1_zfmisc_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_121,plain,(
    ! [A_47] :
      ( k1_tarski('#skF_1'(A_47)) = A_47
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47)
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_32])).

tff(c_130,plain,(
    ! [A_48] :
      ( k1_tarski('#skF_1'(A_48)) = A_48
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48)
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_32])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_46])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_69,plain,(
    ! [B_27,A_28] :
      ( ~ r1_xboole_0(B_27,A_28)
      | ~ r1_tarski(B_27,A_28)
      | v1_xboole_0(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [A_31,B_32] :
      ( ~ r1_tarski(A_31,B_32)
      | v1_xboole_0(A_31)
      | k3_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_69])).

tff(c_87,plain,
    ( v1_xboole_0('#skF_2')
    | k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_84])).

tff(c_89,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_87])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_89])).

tff(c_55,plain,(
    ! [A_23,B_24] :
      ( k2_xboole_0(A_23,B_24) = B_24
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_38,c_55])).

tff(c_91,plain,(
    ! [B_33,A_34,C_35] :
      ( k1_xboole_0 = B_33
      | k1_tarski(A_34) = B_33
      | k2_xboole_0(B_33,C_35) != k1_tarski(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,(
    ! [A_34] :
      ( k1_xboole_0 = '#skF_2'
      | k1_tarski(A_34) = '#skF_2'
      | k1_tarski(A_34) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_91])).

tff(c_95,plain,(
    ! [A_34] :
      ( k1_tarski(A_34) = '#skF_2'
      | k1_tarski(A_34) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_94])).

tff(c_152,plain,(
    ! [A_49] :
      ( k1_tarski('#skF_1'(A_49)) = '#skF_2'
      | A_49 != '#skF_3'
      | ~ v1_zfmisc_1(A_49)
      | v1_xboole_0(A_49)
      | ~ v1_zfmisc_1(A_49)
      | v1_xboole_0(A_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_95])).

tff(c_261,plain,(
    ! [A_74] :
      ( A_74 = '#skF_2'
      | A_74 != '#skF_3'
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74)
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74)
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74)
      | ~ v1_zfmisc_1(A_74)
      | v1_xboole_0(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_152])).

tff(c_263,plain,
    ( '#skF_2' = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_261])).

tff(c_266,plain,
    ( '#skF_2' = '#skF_3'
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_263])).

tff(c_268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_36,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:04:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.45  
% 2.21/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.45  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.21/1.45  
% 2.21/1.45  %Foreground sorts:
% 2.21/1.45  
% 2.21/1.45  
% 2.21/1.45  %Background operators:
% 2.21/1.45  
% 2.21/1.45  
% 2.21/1.45  %Foreground operators:
% 2.21/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.21/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.21/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.21/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.45  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.21/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.21/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.21/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.45  
% 2.21/1.46  tff(f_94, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.21/1.46  tff(f_80, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.21/1.46  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.21/1.46  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.21/1.46  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.21/1.46  tff(f_45, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.21/1.46  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.21/1.46  tff(f_63, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.21/1.46  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.21/1.46  tff(c_36, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.21/1.46  tff(c_40, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.21/1.46  tff(c_34, plain, (![A_14]: (m1_subset_1('#skF_1'(A_14), A_14) | ~v1_zfmisc_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.46  tff(c_97, plain, (![A_37, B_38]: (k6_domain_1(A_37, B_38)=k1_tarski(B_38) | ~m1_subset_1(B_38, A_37) | v1_xboole_0(A_37))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.21/1.46  tff(c_115, plain, (![A_47]: (k6_domain_1(A_47, '#skF_1'(A_47))=k1_tarski('#skF_1'(A_47)) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_34, c_97])).
% 2.21/1.46  tff(c_32, plain, (![A_14]: (k6_domain_1(A_14, '#skF_1'(A_14))=A_14 | ~v1_zfmisc_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.46  tff(c_121, plain, (![A_47]: (k1_tarski('#skF_1'(A_47))=A_47 | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(superposition, [status(thm), theory('equality')], [c_115, c_32])).
% 2.21/1.46  tff(c_130, plain, (![A_48]: (k1_tarski('#skF_1'(A_48))=A_48 | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48) | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(superposition, [status(thm), theory('equality')], [c_115, c_32])).
% 2.21/1.46  tff(c_44, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.21/1.46  tff(c_38, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.21/1.46  tff(c_46, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.21/1.46  tff(c_50, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_46])).
% 2.21/1.46  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.21/1.46  tff(c_69, plain, (![B_27, A_28]: (~r1_xboole_0(B_27, A_28) | ~r1_tarski(B_27, A_28) | v1_xboole_0(B_27))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.21/1.46  tff(c_84, plain, (![A_31, B_32]: (~r1_tarski(A_31, B_32) | v1_xboole_0(A_31) | k3_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_69])).
% 2.21/1.46  tff(c_87, plain, (v1_xboole_0('#skF_2') | k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_84])).
% 2.21/1.46  tff(c_89, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_87])).
% 2.21/1.46  tff(c_90, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_44, c_89])).
% 2.21/1.46  tff(c_55, plain, (![A_23, B_24]: (k2_xboole_0(A_23, B_24)=B_24 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.46  tff(c_59, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_38, c_55])).
% 2.21/1.46  tff(c_91, plain, (![B_33, A_34, C_35]: (k1_xboole_0=B_33 | k1_tarski(A_34)=B_33 | k2_xboole_0(B_33, C_35)!=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.21/1.46  tff(c_94, plain, (![A_34]: (k1_xboole_0='#skF_2' | k1_tarski(A_34)='#skF_2' | k1_tarski(A_34)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_59, c_91])).
% 2.21/1.46  tff(c_95, plain, (![A_34]: (k1_tarski(A_34)='#skF_2' | k1_tarski(A_34)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_90, c_94])).
% 2.21/1.46  tff(c_152, plain, (![A_49]: (k1_tarski('#skF_1'(A_49))='#skF_2' | A_49!='#skF_3' | ~v1_zfmisc_1(A_49) | v1_xboole_0(A_49) | ~v1_zfmisc_1(A_49) | v1_xboole_0(A_49))), inference(superposition, [status(thm), theory('equality')], [c_130, c_95])).
% 2.21/1.46  tff(c_261, plain, (![A_74]: (A_74='#skF_2' | A_74!='#skF_3' | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74) | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74) | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74) | ~v1_zfmisc_1(A_74) | v1_xboole_0(A_74))), inference(superposition, [status(thm), theory('equality')], [c_121, c_152])).
% 2.21/1.46  tff(c_263, plain, ('#skF_2'='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_261])).
% 2.21/1.46  tff(c_266, plain, ('#skF_2'='#skF_3' | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_263])).
% 2.21/1.46  tff(c_268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_36, c_266])).
% 2.21/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.46  
% 2.21/1.46  Inference rules
% 2.21/1.46  ----------------------
% 2.21/1.46  #Ref     : 3
% 2.21/1.46  #Sup     : 50
% 2.21/1.46  #Fact    : 0
% 2.21/1.46  #Define  : 0
% 2.21/1.46  #Split   : 1
% 2.21/1.46  #Chain   : 0
% 2.21/1.46  #Close   : 0
% 2.21/1.46  
% 2.21/1.46  Ordering : KBO
% 2.21/1.46  
% 2.21/1.46  Simplification rules
% 2.21/1.46  ----------------------
% 2.21/1.46  #Subsume      : 17
% 2.21/1.46  #Demod        : 12
% 2.21/1.46  #Tautology    : 20
% 2.21/1.46  #SimpNegUnit  : 7
% 2.21/1.46  #BackRed      : 7
% 2.21/1.46  
% 2.21/1.46  #Partial instantiations: 0
% 2.21/1.46  #Strategies tried      : 1
% 2.21/1.46  
% 2.21/1.46  Timing (in seconds)
% 2.21/1.46  ----------------------
% 2.21/1.46  Preprocessing        : 0.41
% 2.21/1.46  Parsing              : 0.24
% 2.21/1.46  CNF conversion       : 0.02
% 2.21/1.46  Main loop            : 0.21
% 2.21/1.46  Inferencing          : 0.08
% 2.21/1.46  Reduction            : 0.05
% 2.21/1.46  Demodulation         : 0.03
% 2.21/1.46  BG Simplification    : 0.02
% 2.21/1.46  Subsumption          : 0.05
% 2.21/1.47  Abstraction          : 0.01
% 2.21/1.47  MUC search           : 0.00
% 2.21/1.47  Cooper               : 0.00
% 2.21/1.47  Total                : 0.65
% 2.21/1.47  Index Insertion      : 0.00
% 2.21/1.47  Index Deletion       : 0.00
% 2.21/1.47  Index Matching       : 0.00
% 2.21/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
