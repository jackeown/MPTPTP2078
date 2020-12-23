%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:19 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 121 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   82 ( 215 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( B = k1_relset_1(B,A,C)
            & r1_tarski(B,k2_relset_1(B,A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relset_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(c_26,plain,
    ( ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3'))
    | k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_56,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_35,plain,(
    ! [B_27,A_28] :
      ( v1_relat_1(B_27)
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_28))
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_38,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_35])).

tff(c_41,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_38])).

tff(c_57,plain,(
    ! [C_31,A_32,B_33] :
      ( v4_relat_1(C_31,A_32)
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_61,plain,(
    v4_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_57])).

tff(c_67,plain,(
    ! [B_37,A_38] :
      ( k7_relat_1(B_37,A_38) = B_37
      | ~ v4_relat_1(B_37,A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_70,plain,
    ( k7_relat_1('#skF_3','#skF_2') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_61,c_67])).

tff(c_73,plain,(
    k7_relat_1('#skF_3','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_70])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_14])).

tff(c_81,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_77])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_85,plain,
    ( k1_relat_1('#skF_3') = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_81,c_2])).

tff(c_86,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_87,plain,(
    ! [A_39,B_40,C_41] :
      ( k1_relset_1(A_39,B_40,C_41) = k1_relat_1(C_41)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_91,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_87])).

tff(c_28,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_104,plain,(
    ! [C_44,A_45,B_46,D_47] :
      ( r1_tarski(C_44,k1_relset_1(A_45,B_46,D_47))
      | ~ r1_tarski(k6_relat_1(C_44),D_47)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_112,plain,(
    ! [A_48,B_49] :
      ( r1_tarski('#skF_2',k1_relset_1(A_48,B_49,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(resolution,[status(thm)],[c_28,c_104])).

tff(c_115,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_112])).

tff(c_117,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_115])).

tff(c_119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_117])).

tff(c_120,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_129,plain,(
    ! [A_50,B_51,C_52] :
      ( k1_relset_1(A_50,B_51,C_52) = k1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_132,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_129])).

tff(c_134,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_132])).

tff(c_136,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_134])).

tff(c_137,plain,(
    ~ r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_205,plain,(
    ! [C_69,A_70,B_71,D_72] :
      ( r1_tarski(C_69,k2_relset_1(A_70,B_71,D_72))
      | ~ r1_tarski(k6_relat_1(C_69),D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_213,plain,(
    ! [A_73,B_74] :
      ( r1_tarski('#skF_2',k2_relset_1(A_73,B_74,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(resolution,[status(thm)],[c_28,c_205])).

tff(c_216,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_2','#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_30,c_213])).

tff(c_220,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_216])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.25  
% 2.25/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.25  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.25/1.25  
% 2.25/1.25  %Foreground sorts:
% 2.25/1.25  
% 2.25/1.25  
% 2.25/1.25  %Background operators:
% 2.25/1.25  
% 2.25/1.25  
% 2.25/1.25  %Foreground operators:
% 2.25/1.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.25/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.25  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.25/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.25/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.25/1.25  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.25/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.25/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.25/1.25  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.25  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.25/1.25  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.25/1.25  
% 2.25/1.27  tff(f_77, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(k6_relat_1(B), C) => ((B = k1_relset_1(B, A, C)) & r1_tarski(B, k2_relset_1(B, A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_relset_1)).
% 2.25/1.27  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.25/1.27  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.25/1.27  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.25/1.27  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.25/1.27  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.25/1.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.25/1.27  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.25/1.27  tff(f_68, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.25/1.27  tff(c_26, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3')) | k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.27  tff(c_56, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.25/1.27  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.25/1.27  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.27  tff(c_35, plain, (![B_27, A_28]: (v1_relat_1(B_27) | ~m1_subset_1(B_27, k1_zfmisc_1(A_28)) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.25/1.27  tff(c_38, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_35])).
% 2.25/1.27  tff(c_41, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_38])).
% 2.25/1.27  tff(c_57, plain, (![C_31, A_32, B_33]: (v4_relat_1(C_31, A_32) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.25/1.27  tff(c_61, plain, (v4_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_57])).
% 2.25/1.27  tff(c_67, plain, (![B_37, A_38]: (k7_relat_1(B_37, A_38)=B_37 | ~v4_relat_1(B_37, A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.25/1.27  tff(c_70, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_61, c_67])).
% 2.25/1.27  tff(c_73, plain, (k7_relat_1('#skF_3', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_41, c_70])).
% 2.25/1.27  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.25/1.27  tff(c_77, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_73, c_14])).
% 2.25/1.27  tff(c_81, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_41, c_77])).
% 2.25/1.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.25/1.27  tff(c_85, plain, (k1_relat_1('#skF_3')='#skF_2' | ~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_81, c_2])).
% 2.25/1.27  tff(c_86, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_85])).
% 2.25/1.27  tff(c_87, plain, (![A_39, B_40, C_41]: (k1_relset_1(A_39, B_40, C_41)=k1_relat_1(C_41) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.25/1.27  tff(c_91, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_87])).
% 2.25/1.27  tff(c_28, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.27  tff(c_104, plain, (![C_44, A_45, B_46, D_47]: (r1_tarski(C_44, k1_relset_1(A_45, B_46, D_47)) | ~r1_tarski(k6_relat_1(C_44), D_47) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.25/1.27  tff(c_112, plain, (![A_48, B_49]: (r1_tarski('#skF_2', k1_relset_1(A_48, B_49, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(resolution, [status(thm)], [c_28, c_104])).
% 2.25/1.27  tff(c_115, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_112])).
% 2.25/1.27  tff(c_117, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_115])).
% 2.25/1.27  tff(c_119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_117])).
% 2.25/1.27  tff(c_120, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_85])).
% 2.25/1.27  tff(c_129, plain, (![A_50, B_51, C_52]: (k1_relset_1(A_50, B_51, C_52)=k1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.25/1.27  tff(c_132, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_129])).
% 2.25/1.27  tff(c_134, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_132])).
% 2.25/1.27  tff(c_136, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_134])).
% 2.25/1.27  tff(c_137, plain, (~r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_26])).
% 2.25/1.27  tff(c_205, plain, (![C_69, A_70, B_71, D_72]: (r1_tarski(C_69, k2_relset_1(A_70, B_71, D_72)) | ~r1_tarski(k6_relat_1(C_69), D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.25/1.27  tff(c_213, plain, (![A_73, B_74]: (r1_tarski('#skF_2', k2_relset_1(A_73, B_74, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(resolution, [status(thm)], [c_28, c_205])).
% 2.25/1.27  tff(c_216, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_2', '#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_213])).
% 2.25/1.27  tff(c_220, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137, c_216])).
% 2.25/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.27  
% 2.25/1.27  Inference rules
% 2.25/1.27  ----------------------
% 2.25/1.27  #Ref     : 0
% 2.25/1.27  #Sup     : 38
% 2.25/1.27  #Fact    : 0
% 2.25/1.27  #Define  : 0
% 2.25/1.27  #Split   : 4
% 2.25/1.27  #Chain   : 0
% 2.25/1.27  #Close   : 0
% 2.25/1.27  
% 2.25/1.27  Ordering : KBO
% 2.25/1.27  
% 2.25/1.27  Simplification rules
% 2.25/1.27  ----------------------
% 2.25/1.27  #Subsume      : 1
% 2.25/1.27  #Demod        : 31
% 2.25/1.27  #Tautology    : 20
% 2.25/1.27  #SimpNegUnit  : 4
% 2.25/1.27  #BackRed      : 5
% 2.25/1.27  
% 2.25/1.27  #Partial instantiations: 0
% 2.25/1.27  #Strategies tried      : 1
% 2.25/1.27  
% 2.25/1.27  Timing (in seconds)
% 2.25/1.27  ----------------------
% 2.25/1.27  Preprocessing        : 0.30
% 2.25/1.27  Parsing              : 0.15
% 2.25/1.27  CNF conversion       : 0.02
% 2.25/1.27  Main loop            : 0.18
% 2.25/1.27  Inferencing          : 0.06
% 2.25/1.27  Reduction            : 0.06
% 2.25/1.27  Demodulation         : 0.04
% 2.25/1.27  BG Simplification    : 0.01
% 2.25/1.27  Subsumption          : 0.03
% 2.25/1.27  Abstraction          : 0.01
% 2.25/1.27  MUC search           : 0.00
% 2.25/1.27  Cooper               : 0.00
% 2.25/1.27  Total                : 0.51
% 2.25/1.27  Index Insertion      : 0.00
% 2.25/1.27  Index Deletion       : 0.00
% 2.25/1.27  Index Matching       : 0.00
% 2.25/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
