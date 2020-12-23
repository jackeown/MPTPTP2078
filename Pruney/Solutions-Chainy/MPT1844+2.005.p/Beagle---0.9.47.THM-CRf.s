%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:51 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   50 (  75 expanded)
%              Number of leaves         :   22 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   72 ( 158 expanded)
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

tff(f_79,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_58,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_33,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_41,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

tff(c_26,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_22,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_24,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_54,plain,(
    ! [A_21,B_22] :
      ( v1_zfmisc_1(A_21)
      | k6_domain_1(A_21,B_22) != A_21
      | ~ m1_subset_1(B_22,A_21)
      | v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_66,plain,
    ( v1_zfmisc_1(u1_struct_0('#skF_2'))
    | k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') != u1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_54])).

tff(c_67,plain,(
    k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') != u1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(k6_domain_1(A_19,B_20),k1_zfmisc_1(A_19))
      | ~ m1_subset_1(B_20,A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( v1_subset_1(B_10,A_9)
      | B_10 = A_9
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_88,plain,(
    ! [A_26,B_27] :
      ( v1_subset_1(k6_domain_1(A_26,B_27),A_26)
      | k6_domain_1(A_26,B_27) = A_26
      | ~ m1_subset_1(B_27,A_26)
      | v1_xboole_0(A_26) ) ),
    inference(resolution,[status(thm)],[c_46,c_14])).

tff(c_18,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_91,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | ~ m1_subset_1('#skF_3',u1_struct_0('#skF_2'))
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_88,c_18])).

tff(c_97,plain,
    ( k6_domain_1(u1_struct_0('#skF_2'),'#skF_3') = u1_struct_0('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_91])).

tff(c_98,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_97])).

tff(c_2,plain,(
    ! [A_1] :
      ( ~ v1_xboole_0(u1_struct_0(A_1))
      | ~ l1_struct_0(A_1)
      | v2_struct_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_104,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_101])).

tff(c_106,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_104])).

tff(c_107,plain,
    ( v1_xboole_0(u1_struct_0('#skF_2'))
    | v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_109,plain,(
    v1_zfmisc_1(u1_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_4,plain,(
    ! [A_2] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_2))
      | ~ l1_struct_0(A_2)
      | v7_struct_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,
    ( ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_109,c_4])).

tff(c_115,plain,(
    v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_112])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_115])).

tff(c_118,plain,(
    v1_xboole_0(u1_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_122,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_118,c_2])).

tff(c_125,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_122])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_125])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_1 > #skF_2 > #skF_3
% 1.87/1.18  
% 1.87/1.18  %Foreground sorts:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Background operators:
% 1.87/1.18  
% 1.87/1.18  
% 1.87/1.18  %Foreground operators:
% 1.87/1.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.18  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 1.87/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.87/1.18  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 1.87/1.18  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 1.87/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.87/1.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.18  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 1.87/1.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 1.87/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.87/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.87/1.18  
% 1.87/1.19  tff(f_79, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_tex_2)).
% 1.87/1.19  tff(f_58, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 1.87/1.19  tff(f_48, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 1.87/1.19  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_subset_1)).
% 1.87/1.19  tff(f_33, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 1.87/1.19  tff(f_41, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_struct_0)).
% 1.87/1.19  tff(c_26, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.19  tff(c_22, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.19  tff(c_24, plain, (~v7_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.19  tff(c_20, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.19  tff(c_54, plain, (![A_21, B_22]: (v1_zfmisc_1(A_21) | k6_domain_1(A_21, B_22)!=A_21 | ~m1_subset_1(B_22, A_21) | v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.19  tff(c_66, plain, (v1_zfmisc_1(u1_struct_0('#skF_2')) | k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')!=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_20, c_54])).
% 1.87/1.19  tff(c_67, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')!=u1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_66])).
% 1.87/1.19  tff(c_46, plain, (![A_19, B_20]: (m1_subset_1(k6_domain_1(A_19, B_20), k1_zfmisc_1(A_19)) | ~m1_subset_1(B_20, A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.87/1.19  tff(c_14, plain, (![B_10, A_9]: (v1_subset_1(B_10, A_9) | B_10=A_9 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.19  tff(c_88, plain, (![A_26, B_27]: (v1_subset_1(k6_domain_1(A_26, B_27), A_26) | k6_domain_1(A_26, B_27)=A_26 | ~m1_subset_1(B_27, A_26) | v1_xboole_0(A_26))), inference(resolution, [status(thm)], [c_46, c_14])).
% 1.87/1.19  tff(c_18, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.87/1.19  tff(c_91, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | ~m1_subset_1('#skF_3', u1_struct_0('#skF_2')) | v1_xboole_0(u1_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_88, c_18])).
% 1.87/1.19  tff(c_97, plain, (k6_domain_1(u1_struct_0('#skF_2'), '#skF_3')=u1_struct_0('#skF_2') | v1_xboole_0(u1_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_91])).
% 1.87/1.19  tff(c_98, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_67, c_97])).
% 1.87/1.19  tff(c_2, plain, (![A_1]: (~v1_xboole_0(u1_struct_0(A_1)) | ~l1_struct_0(A_1) | v2_struct_0(A_1))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.87/1.19  tff(c_101, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_98, c_2])).
% 1.87/1.19  tff(c_104, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_101])).
% 1.87/1.19  tff(c_106, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_104])).
% 1.87/1.19  tff(c_107, plain, (v1_xboole_0(u1_struct_0('#skF_2')) | v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_66])).
% 1.87/1.19  tff(c_109, plain, (v1_zfmisc_1(u1_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_107])).
% 1.87/1.19  tff(c_4, plain, (![A_2]: (~v1_zfmisc_1(u1_struct_0(A_2)) | ~l1_struct_0(A_2) | v7_struct_0(A_2))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.87/1.19  tff(c_112, plain, (~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_109, c_4])).
% 1.87/1.19  tff(c_115, plain, (v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_112])).
% 1.87/1.19  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_115])).
% 1.87/1.19  tff(c_118, plain, (v1_xboole_0(u1_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_107])).
% 1.87/1.19  tff(c_122, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_118, c_2])).
% 1.87/1.19  tff(c_125, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_122])).
% 1.87/1.19  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_125])).
% 1.87/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  Inference rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Ref     : 0
% 1.87/1.19  #Sup     : 17
% 1.87/1.19  #Fact    : 0
% 1.87/1.19  #Define  : 0
% 1.87/1.19  #Split   : 2
% 1.87/1.19  #Chain   : 0
% 1.87/1.19  #Close   : 0
% 1.87/1.19  
% 1.87/1.19  Ordering : KBO
% 1.87/1.19  
% 1.87/1.19  Simplification rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Subsume      : 2
% 1.87/1.19  #Demod        : 4
% 1.87/1.19  #Tautology    : 4
% 1.87/1.19  #SimpNegUnit  : 4
% 1.87/1.19  #BackRed      : 0
% 1.87/1.19  
% 1.87/1.19  #Partial instantiations: 0
% 1.87/1.19  #Strategies tried      : 1
% 1.87/1.19  
% 1.87/1.19  Timing (in seconds)
% 1.87/1.19  ----------------------
% 1.87/1.19  Preprocessing        : 0.28
% 1.87/1.19  Parsing              : 0.16
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.14
% 1.87/1.19  Inferencing          : 0.06
% 1.87/1.19  Reduction            : 0.04
% 1.87/1.19  Demodulation         : 0.03
% 1.87/1.19  BG Simplification    : 0.01
% 1.87/1.19  Subsumption          : 0.02
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.45
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
