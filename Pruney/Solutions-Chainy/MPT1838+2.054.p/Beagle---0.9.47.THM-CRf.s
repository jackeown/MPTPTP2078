%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:21 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 111 expanded)
%              Number of leaves         :   26 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 229 expanded)
%              Number of equality atoms :   41 (  93 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_76,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

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

tff(f_59,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    ! [A_16] :
      ( m1_subset_1('#skF_1'(A_16),A_16)
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_114,plain,(
    ! [A_38,B_39] :
      ( k6_domain_1(A_38,B_39) = k1_tarski(B_39)
      | ~ m1_subset_1(B_39,A_38)
      | v1_xboole_0(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,(
    ! [A_46] :
      ( k6_domain_1(A_46,'#skF_1'(A_46)) = k1_tarski('#skF_1'(A_46))
      | ~ v1_zfmisc_1(A_46)
      | v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_22,plain,(
    ! [A_16] :
      ( k6_domain_1(A_16,'#skF_1'(A_16)) = A_16
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_150,plain,(
    ! [A_47] :
      ( k1_tarski('#skF_1'(A_47)) = A_47
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47)
      | ~ v1_zfmisc_1(A_47)
      | v1_xboole_0(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_22])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_76,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_6,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k2_xboole_0(A_4,B_5)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_6])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_92,plain,(
    ! [B_32,A_33] :
      ( ~ r1_xboole_0(B_32,A_33)
      | ~ r1_tarski(B_32,A_33)
      | v1_xboole_0(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_36,B_37] :
      ( ~ r1_tarski(A_36,B_37)
      | v1_xboole_0(A_36)
      | k4_xboole_0(A_36,B_37) != A_36 ) ),
    inference(resolution,[status(thm)],[c_12,c_92])).

tff(c_110,plain,
    ( v1_xboole_0('#skF_2')
    | k4_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_107])).

tff(c_112,plain,
    ( v1_xboole_0('#skF_2')
    | k1_xboole_0 != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_110])).

tff(c_113,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_112])).

tff(c_124,plain,(
    ! [C_42,B_43,A_44] :
      ( k1_xboole_0 = C_42
      | k1_xboole_0 = B_43
      | C_42 = B_43
      | k2_xboole_0(B_43,C_42) != k1_tarski(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_127,plain,(
    ! [A_44] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | '#skF_2' = '#skF_3'
      | k1_tarski(A_44) != '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_124])).

tff(c_131,plain,(
    ! [A_44] :
      ( k1_xboole_0 = '#skF_3'
      | k1_tarski(A_44) != '#skF_3' ) ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_113,c_127])).

tff(c_133,plain,(
    ! [A_44] : k1_tarski(A_44) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_131])).

tff(c_164,plain,(
    ! [A_48] :
      ( A_48 != '#skF_3'
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48)
      | ~ v1_zfmisc_1(A_48)
      | v1_xboole_0(A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_133])).

tff(c_166,plain,
    ( ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_164])).

tff(c_169,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_166])).

tff(c_171,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_169])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_131])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_187,plain,(
    ! [A_49] : k2_xboole_0(A_49,'#skF_3') = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_4])).

tff(c_193,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_80])).

tff(c_202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_193])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:11:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.22  
% 2.19/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.22  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.19/1.22  
% 2.19/1.22  %Foreground sorts:
% 2.19/1.22  
% 2.19/1.22  
% 2.19/1.22  %Background operators:
% 2.19/1.22  
% 2.19/1.22  
% 2.19/1.22  %Foreground operators:
% 2.19/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.19/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.19/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.22  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.19/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.22  
% 2.19/1.24  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.19/1.24  tff(f_76, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.19/1.24  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.19/1.24  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.19/1.24  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.19/1.24  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.19/1.24  tff(f_41, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.19/1.24  tff(f_59, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.19/1.24  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.19/1.24  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.24  tff(c_32, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.24  tff(c_30, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.24  tff(c_24, plain, (![A_16]: (m1_subset_1('#skF_1'(A_16), A_16) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.24  tff(c_114, plain, (![A_38, B_39]: (k6_domain_1(A_38, B_39)=k1_tarski(B_39) | ~m1_subset_1(B_39, A_38) | v1_xboole_0(A_38))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.19/1.24  tff(c_135, plain, (![A_46]: (k6_domain_1(A_46, '#skF_1'(A_46))=k1_tarski('#skF_1'(A_46)) | ~v1_zfmisc_1(A_46) | v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_24, c_114])).
% 2.19/1.24  tff(c_22, plain, (![A_16]: (k6_domain_1(A_16, '#skF_1'(A_16))=A_16 | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.19/1.24  tff(c_150, plain, (![A_47]: (k1_tarski('#skF_1'(A_47))=A_47 | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47) | ~v1_zfmisc_1(A_47) | v1_xboole_0(A_47))), inference(superposition, [status(thm), theory('equality')], [c_135, c_22])).
% 2.19/1.24  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.24  tff(c_28, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.19/1.24  tff(c_76, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.24  tff(c_80, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_28, c_76])).
% 2.19/1.24  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k2_xboole_0(A_4, B_5))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.24  tff(c_84, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_80, c_6])).
% 2.19/1.24  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.19/1.24  tff(c_92, plain, (![B_32, A_33]: (~r1_xboole_0(B_32, A_33) | ~r1_tarski(B_32, A_33) | v1_xboole_0(B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.24  tff(c_107, plain, (![A_36, B_37]: (~r1_tarski(A_36, B_37) | v1_xboole_0(A_36) | k4_xboole_0(A_36, B_37)!=A_36)), inference(resolution, [status(thm)], [c_12, c_92])).
% 2.19/1.24  tff(c_110, plain, (v1_xboole_0('#skF_2') | k4_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(resolution, [status(thm)], [c_28, c_107])).
% 2.19/1.24  tff(c_112, plain, (v1_xboole_0('#skF_2') | k1_xboole_0!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_110])).
% 2.19/1.24  tff(c_113, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_112])).
% 2.19/1.24  tff(c_124, plain, (![C_42, B_43, A_44]: (k1_xboole_0=C_42 | k1_xboole_0=B_43 | C_42=B_43 | k2_xboole_0(B_43, C_42)!=k1_tarski(A_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.24  tff(c_127, plain, (![A_44]: (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | '#skF_2'='#skF_3' | k1_tarski(A_44)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_80, c_124])).
% 2.19/1.24  tff(c_131, plain, (![A_44]: (k1_xboole_0='#skF_3' | k1_tarski(A_44)!='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_26, c_113, c_127])).
% 2.19/1.24  tff(c_133, plain, (![A_44]: (k1_tarski(A_44)!='#skF_3')), inference(splitLeft, [status(thm)], [c_131])).
% 2.19/1.24  tff(c_164, plain, (![A_48]: (A_48!='#skF_3' | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48) | ~v1_zfmisc_1(A_48) | v1_xboole_0(A_48))), inference(superposition, [status(thm), theory('equality')], [c_150, c_133])).
% 2.19/1.24  tff(c_166, plain, (~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_30, c_164])).
% 2.19/1.24  tff(c_169, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_166])).
% 2.19/1.24  tff(c_171, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_169])).
% 2.19/1.24  tff(c_172, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_131])).
% 2.19/1.24  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.24  tff(c_187, plain, (![A_49]: (k2_xboole_0(A_49, '#skF_3')=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_172, c_4])).
% 2.19/1.24  tff(c_193, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_187, c_80])).
% 2.19/1.24  tff(c_202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_193])).
% 2.19/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.24  
% 2.19/1.24  Inference rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Ref     : 0
% 2.19/1.24  #Sup     : 41
% 2.19/1.24  #Fact    : 0
% 2.19/1.24  #Define  : 0
% 2.19/1.24  #Split   : 1
% 2.19/1.24  #Chain   : 0
% 2.19/1.24  #Close   : 0
% 2.19/1.24  
% 2.19/1.24  Ordering : KBO
% 2.19/1.24  
% 2.19/1.24  Simplification rules
% 2.19/1.24  ----------------------
% 2.19/1.24  #Subsume      : 1
% 2.19/1.24  #Demod        : 9
% 2.19/1.24  #Tautology    : 26
% 2.19/1.24  #SimpNegUnit  : 4
% 2.19/1.24  #BackRed      : 6
% 2.19/1.24  
% 2.19/1.24  #Partial instantiations: 0
% 2.19/1.24  #Strategies tried      : 1
% 2.19/1.24  
% 2.19/1.24  Timing (in seconds)
% 2.19/1.24  ----------------------
% 2.19/1.24  Preprocessing        : 0.31
% 2.19/1.24  Parsing              : 0.17
% 2.19/1.24  CNF conversion       : 0.02
% 2.19/1.24  Main loop            : 0.16
% 2.19/1.24  Inferencing          : 0.06
% 2.19/1.24  Reduction            : 0.05
% 2.19/1.24  Demodulation         : 0.03
% 2.19/1.24  BG Simplification    : 0.01
% 2.19/1.24  Subsumption          : 0.02
% 2.19/1.24  Abstraction          : 0.01
% 2.19/1.24  MUC search           : 0.00
% 2.19/1.24  Cooper               : 0.00
% 2.19/1.24  Total                : 0.50
% 2.19/1.24  Index Insertion      : 0.00
% 2.19/1.24  Index Deletion       : 0.00
% 2.19/1.24  Index Matching       : 0.00
% 2.19/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
