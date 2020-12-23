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
% DateTime   : Thu Dec  3 10:28:18 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   57 (  78 expanded)
%              Number of leaves         :   28 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 142 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_90,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    v1_zfmisc_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_38,plain,(
    ! [A_29] :
      ( k6_domain_1(A_29,'#skF_3'(A_29)) = A_29
      | ~ v1_zfmisc_1(A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_40,plain,(
    ! [A_29] :
      ( m1_subset_1('#skF_3'(A_29),A_29)
      | ~ v1_zfmisc_1(A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_408,plain,(
    ! [A_90,B_91] :
      ( k6_domain_1(A_90,B_91) = k1_tarski(B_91)
      | ~ m1_subset_1(B_91,A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1153,plain,(
    ! [A_143] :
      ( k6_domain_1(A_143,'#skF_3'(A_143)) = k1_tarski('#skF_3'(A_143))
      | ~ v1_zfmisc_1(A_143)
      | v1_xboole_0(A_143) ) ),
    inference(resolution,[status(thm)],[c_40,c_408])).

tff(c_1439,plain,(
    ! [A_168] :
      ( k1_tarski('#skF_3'(A_168)) = A_168
      | ~ v1_zfmisc_1(A_168)
      | v1_xboole_0(A_168)
      | ~ v1_zfmisc_1(A_168)
      | v1_xboole_0(A_168) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1153])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_108,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(k1_tarski(A_48),B_49)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k2_xboole_0(A_12,B_13) = B_13
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_348,plain,(
    ! [A_87,B_88] :
      ( k2_xboole_0(k1_tarski(A_87),B_88) = B_88
      | ~ r2_hidden(A_87,B_88) ) ),
    inference(resolution,[status(thm)],[c_108,c_16])).

tff(c_32,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_574,plain,(
    ! [B_101,A_102] :
      ( k1_xboole_0 != B_101
      | ~ r2_hidden(A_102,B_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_32])).

tff(c_589,plain,(
    ! [A_103] :
      ( k1_xboole_0 != A_103
      | v1_xboole_0(A_103) ) ),
    inference(resolution,[status(thm)],[c_4,c_574])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_607,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_589,c_50])).

tff(c_606,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(resolution,[status(thm)],[c_589,c_48])).

tff(c_42,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_44,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_90,plain,(
    ! [A_44,B_45] :
      ( k2_xboole_0(A_44,B_45) = B_45
      | ~ r1_tarski(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_94,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_44,c_90])).

tff(c_484,plain,(
    ! [C_95,B_96,A_97] :
      ( k1_xboole_0 = C_95
      | k1_xboole_0 = B_96
      | C_95 = B_96
      | k2_xboole_0(B_96,C_95) != k1_tarski(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_502,plain,(
    ! [A_97] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | '#skF_5' = '#skF_4'
      | k1_tarski(A_97) != '#skF_5' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_484])).

tff(c_510,plain,(
    ! [A_97] :
      ( k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_tarski(A_97) != '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_502])).

tff(c_851,plain,(
    ! [A_97] : k1_tarski(A_97) != '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_607,c_606,c_510])).

tff(c_1487,plain,(
    ! [A_169] :
      ( A_169 != '#skF_5'
      | ~ v1_zfmisc_1(A_169)
      | v1_xboole_0(A_169)
      | ~ v1_zfmisc_1(A_169)
      | v1_xboole_0(A_169) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1439,c_851])).

tff(c_1489,plain,
    ( ~ v1_zfmisc_1('#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_1487])).

tff(c_1492,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1489])).

tff(c_1494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_1492])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:59:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.55  
% 3.38/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.55  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_4 > #skF_3 > #skF_2
% 3.38/1.55  
% 3.38/1.55  %Foreground sorts:
% 3.38/1.55  
% 3.38/1.55  
% 3.38/1.55  %Background operators:
% 3.38/1.55  
% 3.38/1.55  
% 3.38/1.55  %Foreground operators:
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.55  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.38/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.55  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.38/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.38/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.38/1.55  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.38/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.55  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.38/1.55  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.38/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.55  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.38/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.38/1.55  
% 3.38/1.56  tff(f_104, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 3.38/1.56  tff(f_90, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.38/1.56  tff(f_80, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.38/1.56  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.38/1.56  tff(f_56, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.38/1.56  tff(f_46, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.38/1.56  tff(f_73, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.38/1.56  tff(f_70, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.38/1.56  tff(c_48, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.38/1.56  tff(c_46, plain, (v1_zfmisc_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.38/1.56  tff(c_38, plain, (![A_29]: (k6_domain_1(A_29, '#skF_3'(A_29))=A_29 | ~v1_zfmisc_1(A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.38/1.56  tff(c_40, plain, (![A_29]: (m1_subset_1('#skF_3'(A_29), A_29) | ~v1_zfmisc_1(A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.38/1.56  tff(c_408, plain, (![A_90, B_91]: (k6_domain_1(A_90, B_91)=k1_tarski(B_91) | ~m1_subset_1(B_91, A_90) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.38/1.56  tff(c_1153, plain, (![A_143]: (k6_domain_1(A_143, '#skF_3'(A_143))=k1_tarski('#skF_3'(A_143)) | ~v1_zfmisc_1(A_143) | v1_xboole_0(A_143))), inference(resolution, [status(thm)], [c_40, c_408])).
% 3.38/1.56  tff(c_1439, plain, (![A_168]: (k1_tarski('#skF_3'(A_168))=A_168 | ~v1_zfmisc_1(A_168) | v1_xboole_0(A_168) | ~v1_zfmisc_1(A_168) | v1_xboole_0(A_168))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1153])).
% 3.38/1.56  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.38/1.56  tff(c_108, plain, (![A_48, B_49]: (r1_tarski(k1_tarski(A_48), B_49) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.38/1.56  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(A_12, B_13)=B_13 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.38/1.56  tff(c_348, plain, (![A_87, B_88]: (k2_xboole_0(k1_tarski(A_87), B_88)=B_88 | ~r2_hidden(A_87, B_88))), inference(resolution, [status(thm)], [c_108, c_16])).
% 3.38/1.56  tff(c_32, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.38/1.56  tff(c_574, plain, (![B_101, A_102]: (k1_xboole_0!=B_101 | ~r2_hidden(A_102, B_101))), inference(superposition, [status(thm), theory('equality')], [c_348, c_32])).
% 3.38/1.56  tff(c_589, plain, (![A_103]: (k1_xboole_0!=A_103 | v1_xboole_0(A_103))), inference(resolution, [status(thm)], [c_4, c_574])).
% 3.38/1.56  tff(c_50, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.38/1.56  tff(c_607, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_589, c_50])).
% 3.38/1.56  tff(c_606, plain, (k1_xboole_0!='#skF_5'), inference(resolution, [status(thm)], [c_589, c_48])).
% 3.38/1.56  tff(c_42, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.38/1.56  tff(c_44, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.38/1.56  tff(c_90, plain, (![A_44, B_45]: (k2_xboole_0(A_44, B_45)=B_45 | ~r1_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.38/1.56  tff(c_94, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_44, c_90])).
% 3.38/1.56  tff(c_484, plain, (![C_95, B_96, A_97]: (k1_xboole_0=C_95 | k1_xboole_0=B_96 | C_95=B_96 | k2_xboole_0(B_96, C_95)!=k1_tarski(A_97))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.38/1.56  tff(c_502, plain, (![A_97]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | '#skF_5'='#skF_4' | k1_tarski(A_97)!='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_94, c_484])).
% 3.38/1.56  tff(c_510, plain, (![A_97]: (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_tarski(A_97)!='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_502])).
% 3.38/1.56  tff(c_851, plain, (![A_97]: (k1_tarski(A_97)!='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_607, c_606, c_510])).
% 3.38/1.56  tff(c_1487, plain, (![A_169]: (A_169!='#skF_5' | ~v1_zfmisc_1(A_169) | v1_xboole_0(A_169) | ~v1_zfmisc_1(A_169) | v1_xboole_0(A_169))), inference(superposition, [status(thm), theory('equality')], [c_1439, c_851])).
% 3.38/1.56  tff(c_1489, plain, (~v1_zfmisc_1('#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_46, c_1487])).
% 3.38/1.56  tff(c_1492, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1489])).
% 3.38/1.56  tff(c_1494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_1492])).
% 3.38/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.56  
% 3.38/1.56  Inference rules
% 3.38/1.56  ----------------------
% 3.38/1.56  #Ref     : 1
% 3.38/1.56  #Sup     : 353
% 3.38/1.56  #Fact    : 0
% 3.38/1.56  #Define  : 0
% 3.38/1.56  #Split   : 0
% 3.38/1.56  #Chain   : 0
% 3.38/1.56  #Close   : 0
% 3.38/1.56  
% 3.38/1.56  Ordering : KBO
% 3.38/1.56  
% 3.38/1.56  Simplification rules
% 3.38/1.56  ----------------------
% 3.38/1.56  #Subsume      : 140
% 3.38/1.56  #Demod        : 57
% 3.38/1.56  #Tautology    : 134
% 3.38/1.56  #SimpNegUnit  : 39
% 3.38/1.56  #BackRed      : 2
% 3.38/1.56  
% 3.38/1.56  #Partial instantiations: 0
% 3.38/1.56  #Strategies tried      : 1
% 3.38/1.56  
% 3.38/1.56  Timing (in seconds)
% 3.38/1.56  ----------------------
% 3.38/1.57  Preprocessing        : 0.29
% 3.38/1.57  Parsing              : 0.15
% 3.38/1.57  CNF conversion       : 0.02
% 3.38/1.57  Main loop            : 0.45
% 3.38/1.57  Inferencing          : 0.17
% 3.38/1.57  Reduction            : 0.14
% 3.38/1.57  Demodulation         : 0.09
% 3.38/1.57  BG Simplification    : 0.02
% 3.38/1.57  Subsumption          : 0.09
% 3.38/1.57  Abstraction          : 0.02
% 3.38/1.57  MUC search           : 0.00
% 3.38/1.57  Cooper               : 0.00
% 3.38/1.57  Total                : 0.77
% 3.38/1.57  Index Insertion      : 0.00
% 3.38/1.57  Index Deletion       : 0.00
% 3.38/1.57  Index Matching       : 0.00
% 3.38/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
