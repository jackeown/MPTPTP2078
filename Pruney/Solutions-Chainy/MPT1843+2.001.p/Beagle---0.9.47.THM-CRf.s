%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:50 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  85 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 166 expanded)
%              Number of equality atoms :    6 (  19 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v7_struct_0,type,(
    v7_struct_0: $i > $o )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ~ ( v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A))
                & v7_struct_0(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

tff(f_54,axiom,(
    ! [A] :
      ( ( v7_struct_0(A)
        & l1_struct_0(A) )
     => v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_32,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_82,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(c_20,plain,(
    v7_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_26,plain,(
    l1_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_10] :
      ( v1_zfmisc_1(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | ~ v7_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_54,plain,(
    ! [A_29,B_30] :
      ( k6_domain_1(A_29,B_30) = k1_tarski(B_30)
      | ~ m1_subset_1(B_30,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_58,plain,
    ( k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_24,c_54])).

tff(c_59,plain,(
    v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_10,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(u1_struct_0(A_9))
      | ~ l1_struct_0(A_9)
      | v2_struct_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,
    ( ~ l1_struct_0('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_59,c_10])).

tff(c_65,plain,(
    v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_62])).

tff(c_67,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_65])).

tff(c_69,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_30,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4,B_5] : ~ v1_xboole_0(k2_tarski(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_35,plain,(
    ! [A_21] : ~ v1_xboole_0(k1_tarski(A_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_6])).

tff(c_68,plain,(
    k6_domain_1(u1_struct_0('#skF_1'),'#skF_2') = k1_tarski('#skF_2') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_22,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'),'#skF_2'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_79,plain,(
    v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_22])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(k6_domain_1(A_11,B_12),k1_zfmisc_1(A_11))
      | ~ m1_subset_1(B_12,A_11)
      | v1_xboole_0(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_83,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | ~ m1_subset_1('#skF_2',u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_14])).

tff(c_87,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1')))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_83])).

tff(c_88,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1(u1_struct_0('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_87])).

tff(c_100,plain,(
    ! [B_33,A_34] :
      ( ~ v1_subset_1(B_33,A_34)
      | v1_xboole_0(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_zfmisc_1(A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_103,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),u1_struct_0('#skF_1'))
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(resolution,[status(thm)],[c_88,c_100])).

tff(c_109,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1(u1_struct_0('#skF_1'))
    | v1_xboole_0(u1_struct_0('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_103])).

tff(c_110,plain,(
    ~ v1_zfmisc_1(u1_struct_0('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_35,c_109])).

tff(c_114,plain,
    ( ~ l1_struct_0('#skF_1')
    | ~ v7_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_12,c_110])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_26,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n021.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 14:10:04 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.24  
% 2.21/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.24  %$ v1_subset_1 > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k1_enumset1 > k6_domain_1 > k2_tarski > #nlpp > u1_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_2 > #skF_1
% 2.21/1.24  
% 2.21/1.24  %Foreground sorts:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Background operators:
% 2.21/1.24  
% 2.21/1.24  
% 2.21/1.24  %Foreground operators:
% 2.21/1.24  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.24  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.21/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.21/1.24  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.21/1.24  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.21/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.21/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.21/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.21/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.21/1.24  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.24  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.21/1.24  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.21/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.21/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.21/1.24  
% 2.21/1.25  tff(f_96, negated_conjecture, ~(![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => ~(v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)) & v7_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_tex_2)).
% 2.21/1.25  tff(f_54, axiom, (![A]: ((v7_struct_0(A) & l1_struct_0(A)) => v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc7_struct_0)).
% 2.21/1.25  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.21/1.25  tff(f_48, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.21/1.25  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.21/1.25  tff(f_32, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 2.21/1.25  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.21/1.25  tff(f_82, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.21/1.25  tff(c_20, plain, (v7_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.25  tff(c_26, plain, (l1_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.25  tff(c_12, plain, (![A_10]: (v1_zfmisc_1(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | ~v7_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.21/1.25  tff(c_28, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.25  tff(c_24, plain, (m1_subset_1('#skF_2', u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.25  tff(c_54, plain, (![A_29, B_30]: (k6_domain_1(A_29, B_30)=k1_tarski(B_30) | ~m1_subset_1(B_30, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.21/1.25  tff(c_58, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_24, c_54])).
% 2.21/1.25  tff(c_59, plain, (v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitLeft, [status(thm)], [c_58])).
% 2.21/1.25  tff(c_10, plain, (![A_9]: (~v1_xboole_0(u1_struct_0(A_9)) | ~l1_struct_0(A_9) | v2_struct_0(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.21/1.25  tff(c_62, plain, (~l1_struct_0('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_59, c_10])).
% 2.21/1.25  tff(c_65, plain, (v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_62])).
% 2.21/1.25  tff(c_67, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_65])).
% 2.21/1.25  tff(c_69, plain, (~v1_xboole_0(u1_struct_0('#skF_1'))), inference(splitRight, [status(thm)], [c_58])).
% 2.21/1.25  tff(c_30, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.25  tff(c_6, plain, (![A_4, B_5]: (~v1_xboole_0(k2_tarski(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.25  tff(c_35, plain, (![A_21]: (~v1_xboole_0(k1_tarski(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_6])).
% 2.21/1.25  tff(c_68, plain, (k6_domain_1(u1_struct_0('#skF_1'), '#skF_2')=k1_tarski('#skF_2')), inference(splitRight, [status(thm)], [c_58])).
% 2.21/1.25  tff(c_22, plain, (v1_subset_1(k6_domain_1(u1_struct_0('#skF_1'), '#skF_2'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.21/1.25  tff(c_79, plain, (v1_subset_1(k1_tarski('#skF_2'), u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_22])).
% 2.21/1.25  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(k6_domain_1(A_11, B_12), k1_zfmisc_1(A_11)) | ~m1_subset_1(B_12, A_11) | v1_xboole_0(A_11))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.21/1.25  tff(c_83, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | ~m1_subset_1('#skF_2', u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_68, c_14])).
% 2.21/1.25  tff(c_87, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1'))) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_83])).
% 2.21/1.25  tff(c_88, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1(u1_struct_0('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_69, c_87])).
% 2.21/1.25  tff(c_100, plain, (![B_33, A_34]: (~v1_subset_1(B_33, A_34) | v1_xboole_0(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_zfmisc_1(A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.21/1.25  tff(c_103, plain, (~v1_subset_1(k1_tarski('#skF_2'), u1_struct_0('#skF_1')) | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_88, c_100])).
% 2.21/1.25  tff(c_109, plain, (v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1(u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_103])).
% 2.21/1.25  tff(c_110, plain, (~v1_zfmisc_1(u1_struct_0('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_69, c_35, c_109])).
% 2.21/1.25  tff(c_114, plain, (~l1_struct_0('#skF_1') | ~v7_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_12, c_110])).
% 2.21/1.25  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_26, c_114])).
% 2.21/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.25  
% 2.21/1.25  Inference rules
% 2.21/1.25  ----------------------
% 2.21/1.25  #Ref     : 0
% 2.21/1.25  #Sup     : 17
% 2.21/1.25  #Fact    : 0
% 2.21/1.25  #Define  : 0
% 2.21/1.25  #Split   : 1
% 2.21/1.25  #Chain   : 0
% 2.21/1.25  #Close   : 0
% 2.21/1.25  
% 2.21/1.25  Ordering : KBO
% 2.21/1.25  
% 2.21/1.25  Simplification rules
% 2.21/1.25  ----------------------
% 2.21/1.25  #Subsume      : 1
% 2.21/1.25  #Demod        : 7
% 2.21/1.25  #Tautology    : 7
% 2.21/1.25  #SimpNegUnit  : 3
% 2.21/1.25  #BackRed      : 1
% 2.21/1.25  
% 2.21/1.25  #Partial instantiations: 0
% 2.21/1.25  #Strategies tried      : 1
% 2.21/1.25  
% 2.21/1.25  Timing (in seconds)
% 2.21/1.25  ----------------------
% 2.21/1.25  Preprocessing        : 0.32
% 2.21/1.25  Parsing              : 0.17
% 2.21/1.25  CNF conversion       : 0.02
% 2.21/1.25  Main loop            : 0.13
% 2.21/1.25  Inferencing          : 0.05
% 2.21/1.25  Reduction            : 0.04
% 2.21/1.25  Demodulation         : 0.03
% 2.21/1.25  BG Simplification    : 0.01
% 2.21/1.25  Subsumption          : 0.02
% 2.21/1.25  Abstraction          : 0.01
% 2.21/1.25  MUC search           : 0.00
% 2.21/1.25  Cooper               : 0.00
% 2.21/1.25  Total                : 0.48
% 2.21/1.26  Index Insertion      : 0.00
% 2.21/1.26  Index Deletion       : 0.00
% 2.21/1.26  Index Matching       : 0.00
% 2.21/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
