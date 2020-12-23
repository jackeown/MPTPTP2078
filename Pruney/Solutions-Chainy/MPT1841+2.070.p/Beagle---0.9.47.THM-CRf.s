%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:37 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.07s
% Verified   : 
% Statistics : Number of formulae       :   53 (  70 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 ( 116 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_68,plain,(
    ! [A_38,B_39] :
      ( r1_tarski(A_38,B_39)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_76,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_18,c_68])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_40,plain,(
    m1_subset_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_101,plain,(
    ! [A_51,B_52] :
      ( k6_domain_1(A_51,B_52) = k1_tarski(B_52)
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_110,plain,
    ( k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_101])).

tff(c_115,plain,(
    k6_domain_1('#skF_3','#skF_4') = k1_tarski('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_110])).

tff(c_38,plain,(
    v1_subset_1(k6_domain_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_116,plain,(
    v1_subset_1(k1_tarski('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_38])).

tff(c_135,plain,(
    ! [A_59,B_60] :
      ( m1_subset_1(k6_domain_1(A_59,B_60),k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,A_59)
      | v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_149,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4','#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_135])).

tff(c_155,plain,
    ( m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_149])).

tff(c_156,plain,(
    m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_155])).

tff(c_1090,plain,(
    ! [B_118,A_119] :
      ( ~ v1_subset_1(B_118,A_119)
      | v1_xboole_0(B_118)
      | ~ m1_subset_1(B_118,k1_zfmisc_1(A_119))
      | ~ v1_zfmisc_1(A_119)
      | v1_xboole_0(A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1103,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_4'),'#skF_3')
    | v1_xboole_0(k1_tarski('#skF_4'))
    | ~ v1_zfmisc_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_156,c_1090])).

tff(c_1122,plain,
    ( v1_xboole_0(k1_tarski('#skF_4'))
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_116,c_1103])).

tff(c_1123,plain,(
    v1_xboole_0(k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1122])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1130,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1123,c_2])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    ! [B_31,A_32] :
      ( ~ r1_tarski(B_31,A_32)
      | ~ r2_hidden(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_59,plain,(
    ! [C_6] : ~ r1_tarski(k1_tarski(C_6),C_6) ),
    inference(resolution,[status(thm)],[c_6,c_55])).

tff(c_1156,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1130,c_59])).

tff(c_1169,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1156])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:49:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.47  
% 3.07/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.48  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.07/1.48  
% 3.07/1.48  %Foreground sorts:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Background operators:
% 3.07/1.48  
% 3.07/1.48  
% 3.07/1.48  %Foreground operators:
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.07/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.07/1.48  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.07/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.07/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.07/1.48  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.07/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.07/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.07/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.07/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.07/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.07/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.07/1.48  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.07/1.48  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.07/1.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.07/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.07/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.07/1.48  
% 3.07/1.49  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.07/1.49  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.07/1.49  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 3.07/1.49  tff(f_77, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.07/1.49  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 3.07/1.49  tff(f_91, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 3.07/1.49  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.07/1.49  tff(f_36, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.07/1.49  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.07/1.49  tff(c_18, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.07/1.49  tff(c_68, plain, (![A_38, B_39]: (r1_tarski(A_38, B_39) | ~m1_subset_1(A_38, k1_zfmisc_1(B_39)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.07/1.49  tff(c_76, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_18, c_68])).
% 3.07/1.49  tff(c_42, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.49  tff(c_36, plain, (v1_zfmisc_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.49  tff(c_40, plain, (m1_subset_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.49  tff(c_101, plain, (![A_51, B_52]: (k6_domain_1(A_51, B_52)=k1_tarski(B_52) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.07/1.49  tff(c_110, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_40, c_101])).
% 3.07/1.49  tff(c_115, plain, (k6_domain_1('#skF_3', '#skF_4')=k1_tarski('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_42, c_110])).
% 3.07/1.49  tff(c_38, plain, (v1_subset_1(k6_domain_1('#skF_3', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.07/1.49  tff(c_116, plain, (v1_subset_1(k1_tarski('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_115, c_38])).
% 3.07/1.49  tff(c_135, plain, (![A_59, B_60]: (m1_subset_1(k6_domain_1(A_59, B_60), k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, A_59) | v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.07/1.49  tff(c_149, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', '#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_115, c_135])).
% 3.07/1.49  tff(c_155, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_149])).
% 3.07/1.49  tff(c_156, plain, (m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_42, c_155])).
% 3.07/1.49  tff(c_1090, plain, (![B_118, A_119]: (~v1_subset_1(B_118, A_119) | v1_xboole_0(B_118) | ~m1_subset_1(B_118, k1_zfmisc_1(A_119)) | ~v1_zfmisc_1(A_119) | v1_xboole_0(A_119))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.07/1.49  tff(c_1103, plain, (~v1_subset_1(k1_tarski('#skF_4'), '#skF_3') | v1_xboole_0(k1_tarski('#skF_4')) | ~v1_zfmisc_1('#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_156, c_1090])).
% 3.07/1.49  tff(c_1122, plain, (v1_xboole_0(k1_tarski('#skF_4')) | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_116, c_1103])).
% 3.07/1.49  tff(c_1123, plain, (v1_xboole_0(k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_42, c_1122])).
% 3.07/1.49  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.07/1.49  tff(c_1130, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_1123, c_2])).
% 3.07/1.49  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.07/1.49  tff(c_55, plain, (![B_31, A_32]: (~r1_tarski(B_31, A_32) | ~r2_hidden(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.07/1.49  tff(c_59, plain, (![C_6]: (~r1_tarski(k1_tarski(C_6), C_6))), inference(resolution, [status(thm)], [c_6, c_55])).
% 3.07/1.49  tff(c_1156, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1130, c_59])).
% 3.07/1.49  tff(c_1169, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_1156])).
% 3.07/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.49  
% 3.07/1.49  Inference rules
% 3.07/1.49  ----------------------
% 3.07/1.49  #Ref     : 0
% 3.07/1.49  #Sup     : 235
% 3.07/1.49  #Fact    : 0
% 3.07/1.49  #Define  : 0
% 3.07/1.49  #Split   : 1
% 3.07/1.49  #Chain   : 0
% 3.07/1.49  #Close   : 0
% 3.07/1.49  
% 3.07/1.49  Ordering : KBO
% 3.07/1.49  
% 3.07/1.49  Simplification rules
% 3.07/1.49  ----------------------
% 3.07/1.49  #Subsume      : 16
% 3.07/1.49  #Demod        : 143
% 3.07/1.49  #Tautology    : 124
% 3.07/1.49  #SimpNegUnit  : 25
% 3.07/1.49  #BackRed      : 22
% 3.07/1.49  
% 3.07/1.49  #Partial instantiations: 0
% 3.07/1.49  #Strategies tried      : 1
% 3.07/1.49  
% 3.07/1.49  Timing (in seconds)
% 3.07/1.49  ----------------------
% 3.07/1.49  Preprocessing        : 0.31
% 3.07/1.49  Parsing              : 0.16
% 3.07/1.49  CNF conversion       : 0.02
% 3.07/1.49  Main loop            : 0.39
% 3.07/1.49  Inferencing          : 0.14
% 3.07/1.49  Reduction            : 0.12
% 3.07/1.49  Demodulation         : 0.08
% 3.07/1.49  BG Simplification    : 0.02
% 3.07/1.49  Subsumption          : 0.07
% 3.07/1.49  Abstraction          : 0.02
% 3.07/1.49  MUC search           : 0.00
% 3.07/1.49  Cooper               : 0.00
% 3.07/1.49  Total                : 0.72
% 3.07/1.49  Index Insertion      : 0.00
% 3.07/1.49  Index Deletion       : 0.00
% 3.07/1.49  Index Matching       : 0.00
% 3.07/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
