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
% DateTime   : Thu Dec  3 10:28:35 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   55 (  78 expanded)
%              Number of leaves         :   29 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   67 ( 127 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_56,axiom,(
    ! [A] : A != k1_ordinal1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_96,negated_conjecture,(
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

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(c_22,plain,(
    ! [A_16] : k1_ordinal1(A_16) != A_16 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    ! [A_36,B_37] : k5_xboole_0(A_36,k4_xboole_0(B_37,A_36)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_143,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k2_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_134])).

tff(c_149,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_34,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_221,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_224,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_221])).

tff(c_227,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_224])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_238,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_32])).

tff(c_24,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k6_domain_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_416,plain,(
    ! [B_52,A_53] :
      ( ~ v1_subset_1(B_52,A_53)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_434,plain,(
    ! [A_54,B_55] :
      ( ~ v1_subset_1(k6_domain_1(A_54,B_55),A_54)
      | v1_xboole_0(k6_domain_1(A_54,B_55))
      | ~ v1_zfmisc_1(A_54)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_24,c_416])).

tff(c_440,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_434])).

tff(c_445,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_30,c_227,c_238,c_440])).

tff(c_446,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_445])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_450,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_446,c_4])).

tff(c_20,plain,(
    ! [A_15] : k2_xboole_0(A_15,k1_tarski(A_15)) = k1_ordinal1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_463,plain,(
    k2_xboole_0('#skF_2',k1_xboole_0) = k1_ordinal1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_20])).

tff(c_466,plain,(
    k1_ordinal1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_463])).

tff(c_468,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_466])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:59:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.27  
% 2.28/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.27  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_ordinal1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.28/1.27  
% 2.28/1.27  %Foreground sorts:
% 2.28/1.27  
% 2.28/1.27  
% 2.28/1.27  %Background operators:
% 2.28/1.27  
% 2.28/1.27  
% 2.28/1.27  %Foreground operators:
% 2.28/1.27  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.27  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.28/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.27  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.28/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.27  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.28/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.28  
% 2.28/1.29  tff(f_56, axiom, (![A]: ~(A = k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_ordinal1)).
% 2.28/1.29  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.28/1.29  tff(f_37, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.28/1.29  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.28/1.29  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.28/1.29  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.28/1.29  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.28/1.29  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.28/1.29  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.28/1.29  tff(f_53, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.28/1.29  tff(c_22, plain, (![A_16]: (k1_ordinal1(A_16)!=A_16)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.28/1.29  tff(c_12, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.29  tff(c_10, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.29  tff(c_134, plain, (![A_36, B_37]: (k5_xboole_0(A_36, k4_xboole_0(B_37, A_36))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.29  tff(c_143, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k2_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_134])).
% 2.28/1.29  tff(c_149, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_143])).
% 2.28/1.29  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.29  tff(c_34, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.29  tff(c_30, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.29  tff(c_221, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.28/1.29  tff(c_224, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_221])).
% 2.28/1.29  tff(c_227, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_224])).
% 2.28/1.29  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.28/1.29  tff(c_238, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_227, c_32])).
% 2.28/1.29  tff(c_24, plain, (![A_17, B_18]: (m1_subset_1(k6_domain_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.28/1.29  tff(c_416, plain, (![B_52, A_53]: (~v1_subset_1(B_52, A_53) | v1_xboole_0(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.28/1.29  tff(c_434, plain, (![A_54, B_55]: (~v1_subset_1(k6_domain_1(A_54, B_55), A_54) | v1_xboole_0(k6_domain_1(A_54, B_55)) | ~v1_zfmisc_1(A_54) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_24, c_416])).
% 2.28/1.29  tff(c_440, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_227, c_434])).
% 2.28/1.29  tff(c_445, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_30, c_227, c_238, c_440])).
% 2.28/1.29  tff(c_446, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_445])).
% 2.28/1.29  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.28/1.29  tff(c_450, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_446, c_4])).
% 2.28/1.29  tff(c_20, plain, (![A_15]: (k2_xboole_0(A_15, k1_tarski(A_15))=k1_ordinal1(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.28/1.29  tff(c_463, plain, (k2_xboole_0('#skF_2', k1_xboole_0)=k1_ordinal1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_450, c_20])).
% 2.28/1.29  tff(c_466, plain, (k1_ordinal1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_149, c_463])).
% 2.28/1.29  tff(c_468, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_466])).
% 2.28/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  Inference rules
% 2.28/1.29  ----------------------
% 2.28/1.29  #Ref     : 0
% 2.28/1.29  #Sup     : 94
% 2.28/1.29  #Fact    : 0
% 2.28/1.29  #Define  : 0
% 2.28/1.29  #Split   : 1
% 2.28/1.29  #Chain   : 0
% 2.28/1.29  #Close   : 0
% 2.28/1.29  
% 2.28/1.29  Ordering : KBO
% 2.28/1.29  
% 2.28/1.29  Simplification rules
% 2.28/1.29  ----------------------
% 2.28/1.29  #Subsume      : 3
% 2.28/1.29  #Demod        : 58
% 2.28/1.29  #Tautology    : 67
% 2.28/1.29  #SimpNegUnit  : 11
% 2.28/1.29  #BackRed      : 13
% 2.28/1.29  
% 2.28/1.29  #Partial instantiations: 0
% 2.28/1.29  #Strategies tried      : 1
% 2.28/1.29  
% 2.28/1.29  Timing (in seconds)
% 2.28/1.29  ----------------------
% 2.28/1.29  Preprocessing        : 0.30
% 2.28/1.29  Parsing              : 0.16
% 2.28/1.29  CNF conversion       : 0.02
% 2.28/1.29  Main loop            : 0.23
% 2.28/1.29  Inferencing          : 0.09
% 2.28/1.29  Reduction            : 0.08
% 2.28/1.29  Demodulation         : 0.06
% 2.28/1.29  BG Simplification    : 0.01
% 2.28/1.29  Subsumption          : 0.03
% 2.28/1.29  Abstraction          : 0.02
% 2.28/1.29  MUC search           : 0.00
% 2.28/1.29  Cooper               : 0.00
% 2.28/1.29  Total                : 0.55
% 2.28/1.29  Index Insertion      : 0.00
% 2.28/1.29  Index Deletion       : 0.00
% 2.28/1.29  Index Matching       : 0.00
% 2.28/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
