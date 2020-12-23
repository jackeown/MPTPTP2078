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
% DateTime   : Thu Dec  3 10:07:17 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 119 expanded)
%              Number of equality atoms :   12 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_73,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_77,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_73])).

tff(c_24,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_52,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_78,plain,(
    k1_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_52])).

tff(c_31,plain,(
    ! [C_19,A_20,B_21] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_35,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_31])).

tff(c_47,plain,(
    ! [C_24,A_25,B_26] :
      ( v4_relat_1(C_24,A_25)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_51,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_47])).

tff(c_26,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_95,plain,(
    ! [C_40,A_41,B_42,D_43] :
      ( r1_tarski(C_40,k1_relset_1(A_41,B_42,D_43))
      | ~ r1_tarski(k6_relat_1(C_40),D_43)
      | ~ m1_subset_1(D_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_103,plain,(
    ! [A_44,B_45] :
      ( r1_tarski('#skF_2',k1_relset_1(A_44,B_45,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(resolution,[status(thm)],[c_26,c_95])).

tff(c_106,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_103])).

tff(c_108,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_106])).

tff(c_53,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k1_relat_1(B_27),A_28)
      | ~ v4_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [B_27,A_28] :
      ( k1_relat_1(B_27) = A_28
      | ~ r1_tarski(A_28,k1_relat_1(B_27))
      | ~ v4_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_53,c_2])).

tff(c_111,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ v4_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_108,c_56])).

tff(c_116,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_51,c_111])).

tff(c_118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_116])).

tff(c_119,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_239,plain,(
    ! [C_71,A_72,B_73,D_74] :
      ( r1_tarski(C_71,k2_relset_1(A_72,B_73,D_74))
      | ~ r1_tarski(k6_relat_1(C_71),D_74)
      | ~ m1_subset_1(D_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_247,plain,(
    ! [A_75,B_76] :
      ( r1_tarski('#skF_2',k2_relset_1(A_75,B_76,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(resolution,[status(thm)],[c_26,c_239])).

tff(c_250,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_28,c_247])).

tff(c_254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_250])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.23  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.02/1.23  
% 2.02/1.23  %Foreground sorts:
% 2.02/1.23  
% 2.02/1.23  
% 2.02/1.23  %Background operators:
% 2.02/1.23  
% 2.02/1.23  
% 2.02/1.23  %Foreground operators:
% 2.02/1.23  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.23  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.23  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.23  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.02/1.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.02/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.02/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.02/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.02/1.23  
% 2.11/1.24  tff(f_68, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relset_1)).
% 2.11/1.24  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.11/1.24  tff(f_41, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.11/1.24  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.11/1.24  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_relset_1)).
% 2.11/1.24  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 2.11/1.24  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.11/1.24  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.24  tff(c_73, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.24  tff(c_77, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_73])).
% 2.11/1.24  tff(c_24, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.24  tff(c_52, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.11/1.24  tff(c_78, plain, (k1_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_77, c_52])).
% 2.11/1.24  tff(c_31, plain, (![C_19, A_20, B_21]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.11/1.24  tff(c_35, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_31])).
% 2.11/1.24  tff(c_47, plain, (![C_24, A_25, B_26]: (v4_relat_1(C_24, A_25) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.11/1.24  tff(c_51, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_47])).
% 2.11/1.24  tff(c_26, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.24  tff(c_95, plain, (![C_40, A_41, B_42, D_43]: (r1_tarski(C_40, k1_relset_1(A_41, B_42, D_43)) | ~r1_tarski(k6_relat_1(C_40), D_43) | ~m1_subset_1(D_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.24  tff(c_103, plain, (![A_44, B_45]: (r1_tarski('#skF_2', k1_relset_1(A_44, B_45, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(resolution, [status(thm)], [c_26, c_95])).
% 2.11/1.24  tff(c_106, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_103])).
% 2.11/1.24  tff(c_108, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_106])).
% 2.11/1.24  tff(c_53, plain, (![B_27, A_28]: (r1_tarski(k1_relat_1(B_27), A_28) | ~v4_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.24  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.24  tff(c_56, plain, (![B_27, A_28]: (k1_relat_1(B_27)=A_28 | ~r1_tarski(A_28, k1_relat_1(B_27)) | ~v4_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_53, c_2])).
% 2.11/1.24  tff(c_111, plain, (k1_relat_1('#skF_3')='#skF_2' | ~v4_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_108, c_56])).
% 2.11/1.24  tff(c_116, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_51, c_111])).
% 2.11/1.24  tff(c_118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_116])).
% 2.11/1.24  tff(c_119, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_24])).
% 2.11/1.24  tff(c_239, plain, (![C_71, A_72, B_73, D_74]: (r1_tarski(C_71, k2_relset_1(A_72, B_73, D_74)) | ~r1_tarski(k6_relat_1(C_71), D_74) | ~m1_subset_1(D_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.24  tff(c_247, plain, (![A_75, B_76]: (r1_tarski('#skF_2', k2_relset_1(A_75, B_76, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(resolution, [status(thm)], [c_26, c_239])).
% 2.11/1.24  tff(c_250, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_28, c_247])).
% 2.11/1.24  tff(c_254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_250])).
% 2.11/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  Inference rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Ref     : 0
% 2.11/1.24  #Sup     : 45
% 2.11/1.24  #Fact    : 0
% 2.11/1.24  #Define  : 0
% 2.11/1.24  #Split   : 2
% 2.11/1.24  #Chain   : 0
% 2.11/1.24  #Close   : 0
% 2.11/1.24  
% 2.11/1.24  Ordering : KBO
% 2.11/1.24  
% 2.11/1.24  Simplification rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Subsume      : 1
% 2.11/1.24  #Demod        : 24
% 2.11/1.24  #Tautology    : 19
% 2.11/1.24  #SimpNegUnit  : 2
% 2.11/1.24  #BackRed      : 1
% 2.11/1.24  
% 2.11/1.24  #Partial instantiations: 0
% 2.11/1.24  #Strategies tried      : 1
% 2.11/1.24  
% 2.11/1.24  Timing (in seconds)
% 2.11/1.24  ----------------------
% 2.11/1.24  Preprocessing        : 0.29
% 2.11/1.24  Parsing              : 0.16
% 2.11/1.24  CNF conversion       : 0.02
% 2.11/1.24  Main loop            : 0.18
% 2.11/1.24  Inferencing          : 0.07
% 2.11/1.24  Reduction            : 0.05
% 2.11/1.24  Demodulation         : 0.04
% 2.11/1.24  BG Simplification    : 0.01
% 2.11/1.24  Subsumption          : 0.03
% 2.11/1.24  Abstraction          : 0.01
% 2.11/1.24  MUC search           : 0.00
% 2.11/1.24  Cooper               : 0.00
% 2.11/1.24  Total                : 0.50
% 2.11/1.24  Index Insertion      : 0.00
% 2.11/1.24  Index Deletion       : 0.00
% 2.11/1.24  Index Matching       : 0.00
% 2.11/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
