%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:50 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 2.00s
% Verified   : 
% Statistics : Number of formulae       :   51 (  81 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 172 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_zfmisc_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(c_24,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,(
    ! [A_20,B_21] :
      ( v1_zfmisc_1(A_20)
      | k6_domain_1(A_20,B_21) != A_20
      | ~ m1_subset_1(B_21,A_20)
      | v1_xboole_0(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_59,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') != u1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_72,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_60,plain,(
    ! [A_22,B_23] :
      ( m1_subset_1(k6_domain_1(A_22,B_23),k1_zfmisc_1(A_22))
      | ~ m1_subset_1(B_23,A_22)
      | v1_xboole_0(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( v1_subset_1(B_10,A_9)
      | B_10 = A_9
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    ! [A_27,B_28] :
      ( v1_subset_1(k6_domain_1(A_27,B_28),A_27)
      | k6_domain_1(A_27,B_28) = A_27
      | ~ m1_subset_1(B_28,A_27)
      | v1_xboole_0(A_27) ) ),
    inference(resolution,[status(thm)],[c_60,c_14])).

tff(c_18,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_96,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_93,c_18])).

tff(c_102,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_96])).

tff(c_103,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_102])).

tff(c_2,plain,(
    ! [A_1] :
      ( v1_zfmisc_1(A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    ! [A_14] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_14))
      | ~ l1_struct_0(A_14)
      | v7_struct_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_33,plain,(
    ! [A_14] :
      ( ~ l1_struct_0(A_14)
      | v7_struct_0(A_14)
      | ~ v1_xboole_0(u1_struct_0(A_14)) ) ),
    inference(resolution,[status(thm)],[c_2,c_29])).

tff(c_106,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_103,c_33])).

tff(c_109,plain,(
    v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_106])).

tff(c_111,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_109])).

tff(c_112,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_114,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v7_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_117,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_114,c_4])).

tff(c_120,plain,(
    v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_120])).

tff(c_123,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_127,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_123,c_33])).

tff(c_130,plain,(
    v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_127])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  
% 1.88/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.22  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 1.88/1.22  
% 1.88/1.22  %Foreground sorts:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Background operators:
% 1.88/1.22  
% 1.88/1.22  
% 1.88/1.22  %Foreground operators:
% 1.88/1.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.22  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.88/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.88/1.22  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.88/1.22  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.88/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.88/1.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.22  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.88/1.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.88/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.88/1.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.88/1.22  
% 2.00/1.23  tff(f_75, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tex_2)).
% 2.00/1.23  tff(f_54, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 2.00/1.23  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.00/1.23  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 2.00/1.23  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => v1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_zfmisc_1)).
% 2.00/1.23  tff(f_37, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.00/1.23  tff(c_24, plain, (~v7_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.23  tff(c_22, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.23  tff(c_20, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.23  tff(c_51, plain, (![A_20, B_21]: (v1_zfmisc_1(A_20) | k6_domain_1(A_20, B_21)!=A_20 | ~m1_subset_1(B_21, A_20) | v1_xboole_0(A_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.00/1.23  tff(c_59, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')!=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_51])).
% 2.00/1.23  tff(c_72, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')!=u1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_59])).
% 2.00/1.23  tff(c_60, plain, (![A_22, B_23]: (m1_subset_1(k6_domain_1(A_22, B_23), k1_zfmisc_1(A_22)) | ~m1_subset_1(B_23, A_22) | v1_xboole_0(A_22))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.00/1.23  tff(c_14, plain, (![B_10, A_9]: (v1_subset_1(B_10, A_9) | B_10=A_9 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.00/1.23  tff(c_93, plain, (![A_27, B_28]: (v1_subset_1(k6_domain_1(A_27, B_28), A_27) | k6_domain_1(A_27, B_28)=A_27 | ~m1_subset_1(B_28, A_27) | v1_xboole_0(A_27))), inference(resolution, [status(thm)], [c_60, c_14])).
% 2.00/1.23  tff(c_18, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.00/1.23  tff(c_96, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_93, c_18])).
% 2.00/1.23  tff(c_102, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_96])).
% 2.00/1.23  tff(c_103, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_72, c_102])).
% 2.00/1.23  tff(c_2, plain, (![A_1]: (v1_zfmisc_1(A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.00/1.23  tff(c_29, plain, (![A_14]: (~v1_zfmisc_1(u1_struct_0(A_14)) | ~l1_struct_0(A_14) | v7_struct_0(A_14))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.23  tff(c_33, plain, (![A_14]: (~l1_struct_0(A_14) | v7_struct_0(A_14) | ~v1_xboole_0(u1_struct_0(A_14)))), inference(resolution, [status(thm)], [c_2, c_29])).
% 2.00/1.23  tff(c_106, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_103, c_33])).
% 2.00/1.23  tff(c_109, plain, (v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_106])).
% 2.00/1.23  tff(c_111, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_109])).
% 2.00/1.23  tff(c_112, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_59])).
% 2.00/1.23  tff(c_114, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_112])).
% 2.00/1.23  tff(c_4, plain, (![A_2]: (~v1_zfmisc_1(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v7_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.00/1.23  tff(c_117, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_114, c_4])).
% 2.00/1.23  tff(c_120, plain, (v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_117])).
% 2.00/1.23  tff(c_122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_120])).
% 2.00/1.23  tff(c_123, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_112])).
% 2.00/1.23  tff(c_127, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_123, c_33])).
% 2.00/1.23  tff(c_130, plain, (v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_127])).
% 2.00/1.23  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_130])).
% 2.00/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.00/1.23  
% 2.00/1.23  Inference rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Ref     : 0
% 2.00/1.23  #Sup     : 18
% 2.00/1.23  #Fact    : 0
% 2.00/1.23  #Define  : 0
% 2.00/1.23  #Split   : 2
% 2.00/1.23  #Chain   : 0
% 2.00/1.23  #Close   : 0
% 2.00/1.23  
% 2.00/1.23  Ordering : KBO
% 2.00/1.23  
% 2.00/1.23  Simplification rules
% 2.00/1.23  ----------------------
% 2.00/1.23  #Subsume      : 2
% 2.00/1.23  #Demod        : 4
% 2.00/1.23  #Tautology    : 4
% 2.00/1.23  #SimpNegUnit  : 4
% 2.00/1.23  #BackRed      : 0
% 2.00/1.23  
% 2.00/1.23  #Partial instantiations: 0
% 2.00/1.23  #Strategies tried      : 1
% 2.00/1.23  
% 2.00/1.23  Timing (in seconds)
% 2.00/1.23  ----------------------
% 2.00/1.23  Preprocessing        : 0.29
% 2.00/1.23  Parsing              : 0.17
% 2.00/1.23  CNF conversion       : 0.02
% 2.00/1.23  Main loop            : 0.15
% 2.00/1.24  Inferencing          : 0.06
% 2.00/1.24  Reduction            : 0.04
% 2.00/1.24  Demodulation         : 0.03
% 2.00/1.24  BG Simplification    : 0.01
% 2.00/1.24  Subsumption          : 0.03
% 2.00/1.24  Abstraction          : 0.01
% 2.00/1.24  MUC search           : 0.00
% 2.00/1.24  Cooper               : 0.00
% 2.00/1.24  Total                : 0.47
% 2.00/1.24  Index Insertion      : 0.00
% 2.00/1.24  Index Deletion       : 0.00
% 2.00/1.24  Index Matching       : 0.00
% 2.00/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
