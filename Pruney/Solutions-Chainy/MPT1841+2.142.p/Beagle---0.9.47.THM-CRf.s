%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:47 EST 2020

% Result     : Theorem 2.20s
% Output     : CNFRefutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of leaves         :   31 (  50 expanded)
%              Depth                    :   14
%              Number of atoms          :   81 ( 202 expanded)
%              Number of equality atoms :   17 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_47,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_31,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_22,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_24,plain,(
    ! [A_12] : ~ v1_subset_1(k2_subset_1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_45,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_4,plain,(
    ! [A_2] : r1_tarski(k1_xboole_0,A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_42,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_95,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_101,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_95])).

tff(c_105,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_101])).

tff(c_111,plain,(
    ! [A_44,B_45] :
      ( m1_subset_1(k6_domain_1(A_44,B_45),k1_zfmisc_1(A_44))
      | ~ m1_subset_1(B_45,A_44)
      | v1_xboole_0(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_120,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_111])).

tff(c_124,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_120])).

tff(c_125,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_124])).

tff(c_26,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_133,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_26])).

tff(c_141,plain,(
    ! [B_48,A_49] :
      ( B_48 = A_49
      | ~ r1_tarski(A_49,B_48)
      | ~ v1_zfmisc_1(B_48)
      | v1_xboole_0(B_48)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_147,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_133,c_141])).

tff(c_154,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0('#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_147])).

tff(c_155,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_154])).

tff(c_157,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_162,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_157,c_2])).

tff(c_8,plain,(
    ! [C_7] : r2_hidden(C_7,k1_tarski(C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    ! [C_7] : ~ r1_tarski(k1_tarski(C_7),C_7) ),
    inference(resolution,[status(thm)],[c_8,c_68])).

tff(c_175,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_72])).

tff(c_183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_175])).

tff(c_184,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_40,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_106,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_40])).

tff(c_188,plain,(
    v1_subset_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_106])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:26:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.20/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.34  
% 2.20/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.35  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.20/1.35  
% 2.20/1.35  %Foreground sorts:
% 2.20/1.35  
% 2.20/1.35  
% 2.20/1.35  %Background operators:
% 2.20/1.35  
% 2.20/1.35  
% 2.20/1.35  %Foreground operators:
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.20/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.20/1.35  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.20/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.20/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.20/1.35  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.20/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.20/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.20/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.20/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.20/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.20/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.20/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.20/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.20/1.35  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.20/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.20/1.35  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.20/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.20/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.20/1.35  
% 2.20/1.36  tff(f_44, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.20/1.36  tff(f_47, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.20/1.36  tff(f_31, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.20/1.36  tff(f_95, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.20/1.36  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.20/1.36  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.20/1.36  tff(f_51, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.20/1.36  tff(f_83, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.20/1.36  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.20/1.36  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.20/1.36  tff(f_56, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 2.20/1.36  tff(c_22, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.20/1.36  tff(c_24, plain, (![A_12]: (~v1_subset_1(k2_subset_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.20/1.36  tff(c_45, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 2.20/1.36  tff(c_4, plain, (![A_2]: (r1_tarski(k1_xboole_0, A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.20/1.36  tff(c_44, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.20/1.36  tff(c_38, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.20/1.36  tff(c_42, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.20/1.36  tff(c_95, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.20/1.36  tff(c_101, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_95])).
% 2.20/1.36  tff(c_105, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_44, c_101])).
% 2.20/1.36  tff(c_111, plain, (![A_44, B_45]: (m1_subset_1(k6_domain_1(A_44, B_45), k1_zfmisc_1(A_44)) | ~m1_subset_1(B_45, A_44) | v1_xboole_0(A_44))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.20/1.36  tff(c_120, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_105, c_111])).
% 2.20/1.36  tff(c_124, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_120])).
% 2.20/1.36  tff(c_125, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_44, c_124])).
% 2.20/1.36  tff(c_26, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.20/1.36  tff(c_133, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_125, c_26])).
% 2.20/1.36  tff(c_141, plain, (![B_48, A_49]: (B_48=A_49 | ~r1_tarski(A_49, B_48) | ~v1_zfmisc_1(B_48) | v1_xboole_0(B_48) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.20/1.36  tff(c_147, plain, (k1_tarski('#skF_4')='#skF_3' | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_133, c_141])).
% 2.20/1.36  tff(c_154, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0('#skF_3') | v1_xboole_0(k1_tarski('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_147])).
% 2.20/1.36  tff(c_155, plain, (k1_tarski('#skF_4')='#skF_3' | v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_44, c_154])).
% 2.20/1.36  tff(c_157, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(splitLeft, [status(thm)], [c_155])).
% 2.20/1.36  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.20/1.36  tff(c_162, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_157, c_2])).
% 2.20/1.36  tff(c_8, plain, (![C_7]: (r2_hidden(C_7, k1_tarski(C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.20/1.36  tff(c_68, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.20/1.36  tff(c_72, plain, (![C_7]: (~r1_tarski(k1_tarski(C_7), C_7))), inference(resolution, [status(thm)], [c_8, c_68])).
% 2.20/1.36  tff(c_175, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_162, c_72])).
% 2.20/1.36  tff(c_183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_175])).
% 2.20/1.36  tff(c_184, plain, (k1_tarski('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_155])).
% 2.20/1.36  tff(c_40, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.20/1.36  tff(c_106, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_40])).
% 2.20/1.36  tff(c_188, plain, (v1_subset_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_106])).
% 2.20/1.36  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_188])).
% 2.20/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.20/1.36  
% 2.20/1.36  Inference rules
% 2.20/1.36  ----------------------
% 2.20/1.36  #Ref     : 0
% 2.20/1.36  #Sup     : 28
% 2.20/1.36  #Fact    : 0
% 2.20/1.36  #Define  : 0
% 2.20/1.36  #Split   : 1
% 2.20/1.36  #Chain   : 0
% 2.20/1.36  #Close   : 0
% 2.20/1.36  
% 2.20/1.36  Ordering : KBO
% 2.20/1.36  
% 2.20/1.36  Simplification rules
% 2.20/1.36  ----------------------
% 2.20/1.36  #Subsume      : 0
% 2.20/1.36  #Demod        : 17
% 2.20/1.36  #Tautology    : 13
% 2.20/1.36  #SimpNegUnit  : 5
% 2.20/1.36  #BackRed      : 10
% 2.20/1.36  
% 2.20/1.36  #Partial instantiations: 0
% 2.20/1.36  #Strategies tried      : 1
% 2.20/1.36  
% 2.20/1.36  Timing (in seconds)
% 2.20/1.36  ----------------------
% 2.20/1.36  Preprocessing        : 0.37
% 2.20/1.36  Parsing              : 0.18
% 2.20/1.36  CNF conversion       : 0.02
% 2.20/1.36  Main loop            : 0.16
% 2.20/1.36  Inferencing          : 0.05
% 2.20/1.36  Reduction            : 0.05
% 2.20/1.36  Demodulation         : 0.04
% 2.20/1.36  BG Simplification    : 0.02
% 2.20/1.36  Subsumption          : 0.02
% 2.20/1.36  Abstraction          : 0.01
% 2.20/1.36  MUC search           : 0.00
% 2.20/1.36  Cooper               : 0.00
% 2.20/1.36  Total                : 0.56
% 2.20/1.36  Index Insertion      : 0.00
% 2.20/1.37  Index Deletion       : 0.00
% 2.20/1.37  Index Matching       : 0.00
% 2.20/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
