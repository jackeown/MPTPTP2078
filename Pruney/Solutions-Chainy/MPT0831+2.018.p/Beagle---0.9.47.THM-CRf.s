%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:34 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 110 expanded)
%              Number of leaves         :   27 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 182 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_25,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_29,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_25])).

tff(c_37,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_41,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_37])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_44,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_41,c_4])).

tff(c_47,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_44])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_47,c_6])).

tff(c_55,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_51])).

tff(c_22,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_57,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_67,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_3')
      | ~ r1_tarski(A_42,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_22,c_57])).

tff(c_75,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_55,c_67])).

tff(c_127,plain,(
    ! [D_53,B_54,C_55,A_56] :
      ( m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(B_54,C_55)))
      | ~ r1_tarski(k1_relat_1(D_53),B_54)
      | ~ m1_subset_1(D_53,k1_zfmisc_1(k2_zfmisc_1(A_56,C_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_131,plain,(
    ! [B_57] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_57,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_57) ) ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_152,plain,(
    ! [B_58] :
      ( v4_relat_1('#skF_4',B_58)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_58) ) ),
    inference(resolution,[status(thm)],[c_131,c_12])).

tff(c_159,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_75,c_152])).

tff(c_164,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_159,c_4])).

tff(c_167,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_164])).

tff(c_77,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k5_relset_1(A_43,B_44,C_45,D_46) = k7_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_80,plain,(
    ! [D_46] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_46) = k7_relat_1('#skF_4',D_46) ),
    inference(resolution,[status(thm)],[c_24,c_77])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_96,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_20])).

tff(c_176,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_96])).

tff(c_130,plain,(
    ! [B_54] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_54,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_54) ) ),
    inference(resolution,[status(thm)],[c_24,c_127])).

tff(c_222,plain,(
    ! [A_67,B_68,C_69,D_70] :
      ( r2_relset_1(A_67,B_68,C_69,C_69)
      | ~ m1_subset_1(D_70,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68)))
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_229,plain,(
    ! [C_71] :
      ( r2_relset_1('#skF_2','#skF_1',C_71,C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_222])).

tff(c_232,plain,
    ( r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_130,c_229])).

tff(c_237,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_232])).

tff(c_239,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_176,c_237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:57:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  
% 2.15/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.26  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.15/1.26  
% 2.15/1.26  %Foreground sorts:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Background operators:
% 2.15/1.26  
% 2.15/1.26  
% 2.15/1.26  %Foreground operators:
% 2.15/1.26  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.26  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.15/1.26  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.15/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.26  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.15/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.15/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.26  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.15/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.15/1.26  
% 2.15/1.28  tff(f_74, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relset_1)).
% 2.15/1.28  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.15/1.28  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.15/1.28  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.15/1.28  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.15/1.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.15/1.28  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 2.15/1.28  tff(f_55, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.15/1.28  tff(f_61, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.15/1.28  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.28  tff(c_25, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.28  tff(c_29, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_25])).
% 2.15/1.28  tff(c_37, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.28  tff(c_41, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_37])).
% 2.15/1.28  tff(c_4, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.15/1.28  tff(c_44, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_41, c_4])).
% 2.15/1.28  tff(c_47, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29, c_44])).
% 2.15/1.28  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.28  tff(c_51, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_47, c_6])).
% 2.15/1.28  tff(c_55, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_29, c_51])).
% 2.15/1.28  tff(c_22, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.28  tff(c_57, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.28  tff(c_67, plain, (![A_42]: (r1_tarski(A_42, '#skF_3') | ~r1_tarski(A_42, '#skF_2'))), inference(resolution, [status(thm)], [c_22, c_57])).
% 2.15/1.28  tff(c_75, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_55, c_67])).
% 2.15/1.28  tff(c_127, plain, (![D_53, B_54, C_55, A_56]: (m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(B_54, C_55))) | ~r1_tarski(k1_relat_1(D_53), B_54) | ~m1_subset_1(D_53, k1_zfmisc_1(k2_zfmisc_1(A_56, C_55))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.15/1.28  tff(c_131, plain, (![B_57]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_57, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_57))), inference(resolution, [status(thm)], [c_24, c_127])).
% 2.15/1.28  tff(c_12, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.28  tff(c_152, plain, (![B_58]: (v4_relat_1('#skF_4', B_58) | ~r1_tarski(k1_relat_1('#skF_4'), B_58))), inference(resolution, [status(thm)], [c_131, c_12])).
% 2.15/1.28  tff(c_159, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_75, c_152])).
% 2.15/1.28  tff(c_164, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_159, c_4])).
% 2.15/1.28  tff(c_167, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_29, c_164])).
% 2.15/1.28  tff(c_77, plain, (![A_43, B_44, C_45, D_46]: (k5_relset_1(A_43, B_44, C_45, D_46)=k7_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.15/1.28  tff(c_80, plain, (![D_46]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_46)=k7_relat_1('#skF_4', D_46))), inference(resolution, [status(thm)], [c_24, c_77])).
% 2.15/1.28  tff(c_20, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.15/1.28  tff(c_96, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_20])).
% 2.15/1.28  tff(c_176, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_96])).
% 2.15/1.28  tff(c_130, plain, (![B_54]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_54, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_54))), inference(resolution, [status(thm)], [c_24, c_127])).
% 2.15/1.28  tff(c_222, plain, (![A_67, B_68, C_69, D_70]: (r2_relset_1(A_67, B_68, C_69, C_69) | ~m1_subset_1(D_70, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.15/1.28  tff(c_229, plain, (![C_71]: (r2_relset_1('#skF_2', '#skF_1', C_71, C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_24, c_222])).
% 2.15/1.28  tff(c_232, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_130, c_229])).
% 2.15/1.28  tff(c_237, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_232])).
% 2.15/1.28  tff(c_239, plain, $false, inference(negUnitSimplification, [status(thm)], [c_176, c_237])).
% 2.15/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  Inference rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Ref     : 0
% 2.15/1.28  #Sup     : 48
% 2.15/1.28  #Fact    : 0
% 2.15/1.28  #Define  : 0
% 2.15/1.28  #Split   : 0
% 2.15/1.28  #Chain   : 0
% 2.15/1.28  #Close   : 0
% 2.15/1.28  
% 2.15/1.28  Ordering : KBO
% 2.15/1.28  
% 2.15/1.28  Simplification rules
% 2.15/1.28  ----------------------
% 2.15/1.28  #Subsume      : 5
% 2.15/1.28  #Demod        : 17
% 2.15/1.28  #Tautology    : 14
% 2.15/1.28  #SimpNegUnit  : 1
% 2.15/1.28  #BackRed      : 2
% 2.15/1.28  
% 2.15/1.28  #Partial instantiations: 0
% 2.15/1.28  #Strategies tried      : 1
% 2.15/1.28  
% 2.15/1.28  Timing (in seconds)
% 2.15/1.28  ----------------------
% 2.15/1.28  Preprocessing        : 0.28
% 2.15/1.28  Parsing              : 0.15
% 2.15/1.28  CNF conversion       : 0.02
% 2.15/1.28  Main loop            : 0.18
% 2.15/1.28  Inferencing          : 0.08
% 2.15/1.28  Reduction            : 0.05
% 2.15/1.28  Demodulation         : 0.04
% 2.15/1.28  BG Simplification    : 0.01
% 2.15/1.28  Subsumption          : 0.03
% 2.15/1.28  Abstraction          : 0.01
% 2.15/1.28  MUC search           : 0.00
% 2.15/1.28  Cooper               : 0.00
% 2.15/1.28  Total                : 0.49
% 2.15/1.28  Index Insertion      : 0.00
% 2.15/1.28  Index Deletion       : 0.00
% 2.15/1.28  Index Matching       : 0.00
% 2.15/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
