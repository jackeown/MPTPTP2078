%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:59 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 108 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 208 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => ( ( r1_tarski(A,B)
            & r1_tarski(C,D) )
         => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(c_14,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [B_21,A_22] :
      ( v1_relat_1(B_21)
      | ~ m1_subset_1(B_21,k1_zfmisc_1(A_22))
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_33,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_30])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_33])).

tff(c_77,plain,(
    ! [C_34,B_35,A_36] :
      ( v5_relat_1(C_34,B_35)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_36,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_81,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_77])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [A_25,C_26,B_27] :
      ( r1_tarski(A_25,C_26)
      | ~ r1_tarski(B_27,C_26)
      | ~ r1_tarski(A_25,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_48,plain,(
    ! [A_28] :
      ( r1_tarski(A_28,'#skF_4')
      | ~ r1_tarski(A_28,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_24,c_38])).

tff(c_53,plain,(
    ! [B_10] :
      ( r1_tarski(k2_relat_1(B_10),'#skF_4')
      | ~ v5_relat_1(B_10,'#skF_3')
      | ~ v1_relat_1(B_10) ) ),
    inference(resolution,[status(thm)],[c_12,c_48])).

tff(c_82,plain,(
    ! [C_37,A_38,B_39] :
      ( v4_relat_1(C_37,A_38)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_86,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_82])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k1_relat_1(B_8),A_7)
      | ~ v4_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_26,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_47,plain,(
    ! [A_25] :
      ( r1_tarski(A_25,'#skF_2')
      | ~ r1_tarski(A_25,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_26,c_38])).

tff(c_58,plain,(
    ! [B_30,A_31] :
      ( v4_relat_1(B_30,A_31)
      | ~ r1_tarski(k1_relat_1(B_30),A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_97,plain,(
    ! [B_42] :
      ( v4_relat_1(B_42,'#skF_2')
      | ~ v1_relat_1(B_42)
      | ~ r1_tarski(k1_relat_1(B_42),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_47,c_58])).

tff(c_102,plain,(
    ! [B_8] :
      ( v4_relat_1(B_8,'#skF_2')
      | ~ v4_relat_1(B_8,'#skF_1')
      | ~ v1_relat_1(B_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_97])).

tff(c_128,plain,(
    ! [C_49,A_50,B_51] :
      ( m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51)))
      | ~ r1_tarski(k2_relat_1(C_49),B_51)
      | ~ r1_tarski(k1_relat_1(C_49),A_50)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_140,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_22])).

tff(c_148,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_140])).

tff(c_149,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_152,plain,
    ( ~ v4_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_8,c_149])).

tff(c_158,plain,(
    ~ v4_relat_1('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_152])).

tff(c_162,plain,
    ( ~ v4_relat_1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_102,c_158])).

tff(c_166,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_86,c_162])).

tff(c_167,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_194,plain,
    ( ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_53,c_167])).

tff(c_201,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_81,c_194])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:52:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  
% 2.10/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.24  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.10/1.24  
% 2.10/1.24  %Foreground sorts:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Background operators:
% 2.10/1.24  
% 2.10/1.24  
% 2.10/1.24  %Foreground operators:
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.10/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.10/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.10/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.10/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.10/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.10/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.10/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.10/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.10/1.24  
% 2.10/1.25  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.10/1.25  tff(f_75, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 2.10/1.25  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.10/1.25  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.10/1.25  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.10/1.25  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.10/1.25  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.10/1.25  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.10/1.25  tff(c_14, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.25  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.25  tff(c_30, plain, (![B_21, A_22]: (v1_relat_1(B_21) | ~m1_subset_1(B_21, k1_zfmisc_1(A_22)) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.10/1.25  tff(c_33, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_30])).
% 2.10/1.25  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_33])).
% 2.10/1.25  tff(c_77, plain, (![C_34, B_35, A_36]: (v5_relat_1(C_34, B_35) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_36, B_35))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.25  tff(c_81, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_28, c_77])).
% 2.10/1.25  tff(c_12, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.10/1.25  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.25  tff(c_38, plain, (![A_25, C_26, B_27]: (r1_tarski(A_25, C_26) | ~r1_tarski(B_27, C_26) | ~r1_tarski(A_25, B_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.25  tff(c_48, plain, (![A_28]: (r1_tarski(A_28, '#skF_4') | ~r1_tarski(A_28, '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_38])).
% 2.10/1.25  tff(c_53, plain, (![B_10]: (r1_tarski(k2_relat_1(B_10), '#skF_4') | ~v5_relat_1(B_10, '#skF_3') | ~v1_relat_1(B_10))), inference(resolution, [status(thm)], [c_12, c_48])).
% 2.10/1.26  tff(c_82, plain, (![C_37, A_38, B_39]: (v4_relat_1(C_37, A_38) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.10/1.26  tff(c_86, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_82])).
% 2.10/1.26  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k1_relat_1(B_8), A_7) | ~v4_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.26  tff(c_26, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.26  tff(c_47, plain, (![A_25]: (r1_tarski(A_25, '#skF_2') | ~r1_tarski(A_25, '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_38])).
% 2.10/1.26  tff(c_58, plain, (![B_30, A_31]: (v4_relat_1(B_30, A_31) | ~r1_tarski(k1_relat_1(B_30), A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.10/1.26  tff(c_97, plain, (![B_42]: (v4_relat_1(B_42, '#skF_2') | ~v1_relat_1(B_42) | ~r1_tarski(k1_relat_1(B_42), '#skF_1'))), inference(resolution, [status(thm)], [c_47, c_58])).
% 2.10/1.26  tff(c_102, plain, (![B_8]: (v4_relat_1(B_8, '#skF_2') | ~v4_relat_1(B_8, '#skF_1') | ~v1_relat_1(B_8))), inference(resolution, [status(thm)], [c_8, c_97])).
% 2.10/1.26  tff(c_128, plain, (![C_49, A_50, B_51]: (m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))) | ~r1_tarski(k2_relat_1(C_49), B_51) | ~r1_tarski(k1_relat_1(C_49), A_50) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.10/1.26  tff(c_22, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.10/1.26  tff(c_140, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_128, c_22])).
% 2.10/1.26  tff(c_148, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_140])).
% 2.10/1.26  tff(c_149, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_148])).
% 2.10/1.26  tff(c_152, plain, (~v4_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_8, c_149])).
% 2.10/1.26  tff(c_158, plain, (~v4_relat_1('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_152])).
% 2.10/1.26  tff(c_162, plain, (~v4_relat_1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_102, c_158])).
% 2.10/1.26  tff(c_166, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_86, c_162])).
% 2.10/1.26  tff(c_167, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_148])).
% 2.10/1.26  tff(c_194, plain, (~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_53, c_167])).
% 2.10/1.26  tff(c_201, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_81, c_194])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 36
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 1
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.26  
% 2.10/1.26  Simplification rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Subsume      : 3
% 2.10/1.26  #Demod        : 9
% 2.10/1.26  #Tautology    : 4
% 2.10/1.26  #SimpNegUnit  : 0
% 2.10/1.26  #BackRed      : 0
% 2.10/1.26  
% 2.10/1.26  #Partial instantiations: 0
% 2.10/1.26  #Strategies tried      : 1
% 2.10/1.26  
% 2.10/1.26  Timing (in seconds)
% 2.10/1.26  ----------------------
% 2.10/1.26  Preprocessing        : 0.29
% 2.10/1.26  Parsing              : 0.16
% 2.10/1.26  CNF conversion       : 0.02
% 2.10/1.26  Main loop            : 0.20
% 2.10/1.26  Inferencing          : 0.08
% 2.10/1.26  Reduction            : 0.05
% 2.10/1.26  Demodulation         : 0.04
% 2.10/1.26  BG Simplification    : 0.01
% 2.10/1.26  Subsumption          : 0.04
% 2.10/1.26  Abstraction          : 0.01
% 2.10/1.26  MUC search           : 0.00
% 2.10/1.26  Cooper               : 0.00
% 2.10/1.26  Total                : 0.52
% 2.10/1.26  Index Insertion      : 0.00
% 2.10/1.26  Index Deletion       : 0.00
% 2.10/1.26  Index Matching       : 0.00
% 2.10/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
