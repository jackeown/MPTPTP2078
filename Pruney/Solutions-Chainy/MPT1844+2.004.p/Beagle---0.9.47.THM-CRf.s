%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:51 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 149 expanded)
%              Number of leaves         :   28 (  62 expanded)
%              Depth                    :   11
%              Number of atoms          :   92 ( 299 expanded)
%              Number of equality atoms :   16 (  56 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & ~ v7_struct_0(A)
          & l1_struct_0(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => v1_subset_1(k6_domain_1(u1_struct_0(A),B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_tex_2)).

tff(f_39,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(k2_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_55,axiom,(
    ! [A] :
      ( ( ~ v7_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_zfmisc_1(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

tff(f_72,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(c_32,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_28,plain,(
    l1_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_33,plain,(
    ! [A_17] :
      ( u1_struct_0(A_17) = k2_struct_0(A_17)
      | ~ l1_struct_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_37,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_33])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_39,plain,(
    m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_26])).

tff(c_81,plain,(
    ! [A_30,B_31] :
      ( k6_domain_1(A_30,B_31) = k1_tarski(B_31)
      | ~ m1_subset_1(B_31,A_30)
      | v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_93,plain,
    ( k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_39,c_81])).

tff(c_94,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_93])).

tff(c_8,plain,(
    ! [A_6] :
      ( ~ v1_xboole_0(k2_struct_0(A_6))
      | ~ l1_struct_0(A_6)
      | v2_struct_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_94,c_8])).

tff(c_100,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_97])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_100])).

tff(c_104,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ v7_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_44,plain,(
    ! [A_19] :
      ( ~ v1_zfmisc_1(u1_struct_0(A_19))
      | ~ l1_struct_0(A_19)
      | v7_struct_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_47,plain,
    ( ~ v1_zfmisc_1(k2_struct_0('#skF_2'))
    | ~ l1_struct_0('#skF_2')
    | v7_struct_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_44])).

tff(c_49,plain,
    ( ~ v1_zfmisc_1(k2_struct_0('#skF_2'))
    | v7_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_47])).

tff(c_50,plain,(
    ~ v1_zfmisc_1(k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_49])).

tff(c_103,plain,(
    k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_93])).

tff(c_121,plain,(
    ! [A_34,B_35] :
      ( v1_zfmisc_1(A_34)
      | k6_domain_1(A_34,B_35) != A_34
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_130,plain,
    ( v1_zfmisc_1(k2_struct_0('#skF_2'))
    | k6_domain_1(k2_struct_0('#skF_2'),'#skF_3') != k2_struct_0('#skF_2')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_39,c_121])).

tff(c_134,plain,
    ( v1_zfmisc_1(k2_struct_0('#skF_2'))
    | k2_struct_0('#skF_2') != k1_tarski('#skF_3')
    | v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_130])).

tff(c_135,plain,(
    k2_struct_0('#skF_2') != k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_50,c_134])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(k1_tarski(A_1),k1_zfmisc_1(B_2))
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_61,plain,(
    ! [B_26,A_27] :
      ( v1_subset_1(B_26,A_27)
      | B_26 = A_27
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_110,plain,(
    ! [A_32,B_33] :
      ( v1_subset_1(k1_tarski(A_32),B_33)
      | k1_tarski(A_32) = B_33
      | ~ r2_hidden(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_2,c_61])).

tff(c_24,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'),'#skF_3'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_51,plain,(
    ~ v1_subset_1(k6_domain_1(k2_struct_0('#skF_2'),'#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_37,c_24])).

tff(c_105,plain,(
    ~ v1_subset_1(k1_tarski('#skF_3'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_51])).

tff(c_118,plain,
    ( k2_struct_0('#skF_2') = k1_tarski('#skF_3')
    | ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_110,c_105])).

tff(c_136,plain,(
    ~ r2_hidden('#skF_3',k2_struct_0('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_118])).

tff(c_139,plain,
    ( v1_xboole_0(k2_struct_0('#skF_2'))
    | ~ m1_subset_1('#skF_3',k2_struct_0('#skF_2')) ),
    inference(resolution,[status(thm)],[c_4,c_136])).

tff(c_142,plain,(
    v1_xboole_0(k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_139])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_104,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:23:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.28  %$ v1_subset_1 > r2_hidden > m1_subset_1 > v7_struct_0 > v2_struct_0 > v1_zfmisc_1 > v1_xboole_0 > l1_struct_0 > k6_domain_1 > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2 > #skF_3
% 2.08/1.28  
% 2.08/1.28  %Foreground sorts:
% 2.08/1.28  
% 2.08/1.28  
% 2.08/1.28  %Background operators:
% 2.08/1.28  
% 2.08/1.28  
% 2.08/1.28  %Foreground operators:
% 2.08/1.28  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.28  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.08/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.28  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.08/1.28  tff(v7_struct_0, type, v7_struct_0: $i > $o).
% 2.08/1.28  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.08/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.28  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.28  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.08/1.28  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.08/1.28  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 2.08/1.28  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.28  
% 2.08/1.29  tff(f_93, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & ~v7_struct_0(A)) & l1_struct_0(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => v1_subset_1(k6_domain_1(u1_struct_0(A), B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_tex_2)).
% 2.08/1.29  tff(f_39, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 2.08/1.29  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.08/1.29  tff(f_47, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(k2_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_struct_0)).
% 2.08/1.29  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.08/1.29  tff(f_55, axiom, (![A]: ((~v7_struct_0(A) & l1_struct_0(A)) => ~v1_zfmisc_1(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_struct_0)).
% 2.08/1.29  tff(f_72, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.08/1.29  tff(f_29, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 2.08/1.29  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 2.08/1.29  tff(c_32, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.29  tff(c_28, plain, (l1_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.29  tff(c_33, plain, (![A_17]: (u1_struct_0(A_17)=k2_struct_0(A_17) | ~l1_struct_0(A_17))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.29  tff(c_37, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_28, c_33])).
% 2.08/1.29  tff(c_26, plain, (m1_subset_1('#skF_3', u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.29  tff(c_39, plain, (m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_26])).
% 2.08/1.29  tff(c_81, plain, (![A_30, B_31]: (k6_domain_1(A_30, B_31)=k1_tarski(B_31) | ~m1_subset_1(B_31, A_30) | v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.08/1.29  tff(c_93, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_39, c_81])).
% 2.08/1.29  tff(c_94, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitLeft, [status(thm)], [c_93])).
% 2.08/1.29  tff(c_8, plain, (![A_6]: (~v1_xboole_0(k2_struct_0(A_6)) | ~l1_struct_0(A_6) | v2_struct_0(A_6))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.29  tff(c_97, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_94, c_8])).
% 2.08/1.29  tff(c_100, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_97])).
% 2.08/1.29  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_100])).
% 2.08/1.29  tff(c_104, plain, (~v1_xboole_0(k2_struct_0('#skF_2'))), inference(splitRight, [status(thm)], [c_93])).
% 2.08/1.29  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.29  tff(c_30, plain, (~v7_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.29  tff(c_44, plain, (![A_19]: (~v1_zfmisc_1(u1_struct_0(A_19)) | ~l1_struct_0(A_19) | v7_struct_0(A_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.08/1.29  tff(c_47, plain, (~v1_zfmisc_1(k2_struct_0('#skF_2')) | ~l1_struct_0('#skF_2') | v7_struct_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_37, c_44])).
% 2.08/1.29  tff(c_49, plain, (~v1_zfmisc_1(k2_struct_0('#skF_2')) | v7_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_47])).
% 2.08/1.29  tff(c_50, plain, (~v1_zfmisc_1(k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_49])).
% 2.08/1.29  tff(c_103, plain, (k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_93])).
% 2.08/1.29  tff(c_121, plain, (![A_34, B_35]: (v1_zfmisc_1(A_34) | k6_domain_1(A_34, B_35)!=A_34 | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.08/1.29  tff(c_130, plain, (v1_zfmisc_1(k2_struct_0('#skF_2')) | k6_domain_1(k2_struct_0('#skF_2'), '#skF_3')!=k2_struct_0('#skF_2') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_39, c_121])).
% 2.08/1.29  tff(c_134, plain, (v1_zfmisc_1(k2_struct_0('#skF_2')) | k2_struct_0('#skF_2')!=k1_tarski('#skF_3') | v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_130])).
% 2.08/1.29  tff(c_135, plain, (k2_struct_0('#skF_2')!=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_104, c_50, c_134])).
% 2.08/1.29  tff(c_2, plain, (![A_1, B_2]: (m1_subset_1(k1_tarski(A_1), k1_zfmisc_1(B_2)) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.29  tff(c_61, plain, (![B_26, A_27]: (v1_subset_1(B_26, A_27) | B_26=A_27 | ~m1_subset_1(B_26, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.08/1.29  tff(c_110, plain, (![A_32, B_33]: (v1_subset_1(k1_tarski(A_32), B_33) | k1_tarski(A_32)=B_33 | ~r2_hidden(A_32, B_33))), inference(resolution, [status(thm)], [c_2, c_61])).
% 2.08/1.29  tff(c_24, plain, (~v1_subset_1(k6_domain_1(u1_struct_0('#skF_2'), '#skF_3'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.29  tff(c_51, plain, (~v1_subset_1(k6_domain_1(k2_struct_0('#skF_2'), '#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_37, c_24])).
% 2.08/1.29  tff(c_105, plain, (~v1_subset_1(k1_tarski('#skF_3'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_51])).
% 2.08/1.29  tff(c_118, plain, (k2_struct_0('#skF_2')=k1_tarski('#skF_3') | ~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_110, c_105])).
% 2.08/1.29  tff(c_136, plain, (~r2_hidden('#skF_3', k2_struct_0('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_135, c_118])).
% 2.08/1.29  tff(c_139, plain, (v1_xboole_0(k2_struct_0('#skF_2')) | ~m1_subset_1('#skF_3', k2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_4, c_136])).
% 2.08/1.29  tff(c_142, plain, (v1_xboole_0(k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_39, c_139])).
% 2.08/1.29  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_104, c_142])).
% 2.08/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.08/1.29  
% 2.08/1.29  Inference rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Ref     : 0
% 2.08/1.29  #Sup     : 21
% 2.08/1.29  #Fact    : 0
% 2.08/1.29  #Define  : 0
% 2.08/1.29  #Split   : 1
% 2.08/1.29  #Chain   : 0
% 2.08/1.29  #Close   : 0
% 2.08/1.29  
% 2.08/1.29  Ordering : KBO
% 2.08/1.29  
% 2.08/1.29  Simplification rules
% 2.08/1.29  ----------------------
% 2.08/1.29  #Subsume      : 0
% 2.08/1.29  #Demod        : 8
% 2.08/1.29  #Tautology    : 8
% 2.08/1.29  #SimpNegUnit  : 5
% 2.08/1.29  #BackRed      : 2
% 2.08/1.29  
% 2.08/1.29  #Partial instantiations: 0
% 2.08/1.29  #Strategies tried      : 1
% 2.08/1.29  
% 2.08/1.29  Timing (in seconds)
% 2.08/1.29  ----------------------
% 2.08/1.29  Preprocessing        : 0.34
% 2.08/1.29  Parsing              : 0.18
% 2.08/1.29  CNF conversion       : 0.02
% 2.08/1.29  Main loop            : 0.15
% 2.08/1.29  Inferencing          : 0.06
% 2.08/1.29  Reduction            : 0.05
% 2.08/1.29  Demodulation         : 0.03
% 2.08/1.29  BG Simplification    : 0.01
% 2.08/1.29  Subsumption          : 0.02
% 2.08/1.29  Abstraction          : 0.01
% 2.08/1.29  MUC search           : 0.00
% 2.08/1.29  Cooper               : 0.00
% 2.08/1.29  Total                : 0.53
% 2.08/1.29  Index Insertion      : 0.00
% 2.08/1.29  Index Deletion       : 0.00
% 2.08/1.29  Index Matching       : 0.00
% 2.08/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
