%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:39 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 125 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 213 expanded)
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

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( r1_tarski(B,C)
         => r2_relset_1(B,A,k5_relset_1(B,A,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

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
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_6,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_29,plain,(
    ! [B_32,A_33] :
      ( v1_relat_1(B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_33))
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_32,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_35,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_32])).

tff(c_59,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_63,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_8,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_63,c_8])).

tff(c_69,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_66])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_42,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [A_42] :
      ( r1_tarski(A_42,'#skF_3')
      | ~ r1_tarski(A_42,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_42])).

tff(c_54,plain,(
    ! [B_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,'#skF_2')),'#skF_3')
      | ~ v1_relat_1(B_12) ) ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_77,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_54])).

tff(c_84,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_77])).

tff(c_133,plain,(
    ! [D_56,B_57,C_58,A_59] :
      ( m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(B_57,C_58)))
      | ~ r1_tarski(k1_relat_1(D_56),B_57)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_59,C_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_137,plain,(
    ! [B_60] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_60,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_60) ) ),
    inference(resolution,[status(thm)],[c_26,c_133])).

tff(c_14,plain,(
    ! [C_15,A_13,B_14] :
      ( v4_relat_1(C_15,A_13)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_159,plain,(
    ! [B_61] :
      ( v4_relat_1('#skF_4',B_61)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_61) ) ),
    inference(resolution,[status(thm)],[c_137,c_14])).

tff(c_168,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_84,c_159])).

tff(c_179,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_168,c_8])).

tff(c_182,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_179])).

tff(c_70,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k5_relset_1(A_47,B_48,C_49,D_50) = k7_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_73,plain,(
    ! [D_50] : k5_relset_1('#skF_2','#skF_1','#skF_4',D_50) = k7_relat_1('#skF_4',D_50) ),
    inference(resolution,[status(thm)],[c_26,c_70])).

tff(c_22,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k5_relset_1('#skF_2','#skF_1','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_99,plain,(
    ~ r2_relset_1('#skF_2','#skF_1',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_22])).

tff(c_183,plain,(
    ~ r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_99])).

tff(c_80,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_69,c_10])).

tff(c_86,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_80])).

tff(c_136,plain,(
    ! [B_57] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_57,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_57) ) ),
    inference(resolution,[status(thm)],[c_26,c_133])).

tff(c_218,plain,(
    ! [A_68,B_69,C_70,D_71] :
      ( r2_relset_1(A_68,B_69,C_70,C_70)
      | ~ m1_subset_1(D_71,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69)))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_225,plain,(
    ! [C_72] :
      ( r2_relset_1('#skF_2','#skF_1',C_72,C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ) ),
    inference(resolution,[status(thm)],[c_26,c_218])).

tff(c_228,plain,
    ( r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_136,c_225])).

tff(c_233,plain,(
    r2_relset_1('#skF_2','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_228])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_233])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:03:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  %$ r2_relset_1 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.24  
% 2.06/1.24  %Foreground sorts:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Background operators:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Foreground operators:
% 2.06/1.24  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.06/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.06/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.06/1.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.06/1.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.06/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.06/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.06/1.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.24  
% 2.06/1.25  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.06/1.25  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A))) => (r1_tarski(B, C) => r2_relset_1(B, A, k5_relset_1(B, A, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_relset_1)).
% 2.06/1.25  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.06/1.25  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.06/1.25  tff(f_46, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.06/1.25  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.06/1.25  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.06/1.25  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.06/1.25  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.06/1.25  tff(f_66, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.06/1.25  tff(c_6, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.25  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.25  tff(c_29, plain, (![B_32, A_33]: (v1_relat_1(B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_33)) | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.25  tff(c_32, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.06/1.25  tff(c_35, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_32])).
% 2.06/1.25  tff(c_59, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.25  tff(c_63, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_59])).
% 2.06/1.25  tff(c_8, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.25  tff(c_66, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_63, c_8])).
% 2.06/1.25  tff(c_69, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_66])).
% 2.06/1.25  tff(c_10, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.25  tff(c_24, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.25  tff(c_42, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.25  tff(c_49, plain, (![A_42]: (r1_tarski(A_42, '#skF_3') | ~r1_tarski(A_42, '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_42])).
% 2.06/1.25  tff(c_54, plain, (![B_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, '#skF_2')), '#skF_3') | ~v1_relat_1(B_12))), inference(resolution, [status(thm)], [c_10, c_49])).
% 2.06/1.25  tff(c_77, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_69, c_54])).
% 2.06/1.25  tff(c_84, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_77])).
% 2.06/1.25  tff(c_133, plain, (![D_56, B_57, C_58, A_59]: (m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(B_57, C_58))) | ~r1_tarski(k1_relat_1(D_56), B_57) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_59, C_58))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.06/1.25  tff(c_137, plain, (![B_60]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_60, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_60))), inference(resolution, [status(thm)], [c_26, c_133])).
% 2.06/1.25  tff(c_14, plain, (![C_15, A_13, B_14]: (v4_relat_1(C_15, A_13) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.25  tff(c_159, plain, (![B_61]: (v4_relat_1('#skF_4', B_61) | ~r1_tarski(k1_relat_1('#skF_4'), B_61))), inference(resolution, [status(thm)], [c_137, c_14])).
% 2.06/1.25  tff(c_168, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_84, c_159])).
% 2.06/1.25  tff(c_179, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_168, c_8])).
% 2.06/1.25  tff(c_182, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_179])).
% 2.06/1.25  tff(c_70, plain, (![A_47, B_48, C_49, D_50]: (k5_relset_1(A_47, B_48, C_49, D_50)=k7_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.06/1.25  tff(c_73, plain, (![D_50]: (k5_relset_1('#skF_2', '#skF_1', '#skF_4', D_50)=k7_relat_1('#skF_4', D_50))), inference(resolution, [status(thm)], [c_26, c_70])).
% 2.06/1.25  tff(c_22, plain, (~r2_relset_1('#skF_2', '#skF_1', k5_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.06/1.25  tff(c_99, plain, (~r2_relset_1('#skF_2', '#skF_1', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_73, c_22])).
% 2.06/1.25  tff(c_183, plain, (~r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_99])).
% 2.06/1.25  tff(c_80, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_69, c_10])).
% 2.06/1.25  tff(c_86, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_80])).
% 2.06/1.25  tff(c_136, plain, (![B_57]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_57, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_57))), inference(resolution, [status(thm)], [c_26, c_133])).
% 2.06/1.25  tff(c_218, plain, (![A_68, B_69, C_70, D_71]: (r2_relset_1(A_68, B_69, C_70, C_70) | ~m1_subset_1(D_71, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.25  tff(c_225, plain, (![C_72]: (r2_relset_1('#skF_2', '#skF_1', C_72, C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))))), inference(resolution, [status(thm)], [c_26, c_218])).
% 2.06/1.25  tff(c_228, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_136, c_225])).
% 2.06/1.25  tff(c_233, plain, (r2_relset_1('#skF_2', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_228])).
% 2.06/1.25  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_233])).
% 2.06/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  Inference rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Ref     : 0
% 2.06/1.25  #Sup     : 46
% 2.06/1.25  #Fact    : 0
% 2.06/1.25  #Define  : 0
% 2.06/1.25  #Split   : 0
% 2.06/1.25  #Chain   : 0
% 2.06/1.25  #Close   : 0
% 2.06/1.25  
% 2.06/1.25  Ordering : KBO
% 2.06/1.25  
% 2.06/1.25  Simplification rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Subsume      : 4
% 2.06/1.25  #Demod        : 18
% 2.06/1.25  #Tautology    : 14
% 2.06/1.25  #SimpNegUnit  : 1
% 2.06/1.25  #BackRed      : 2
% 2.06/1.25  
% 2.06/1.25  #Partial instantiations: 0
% 2.06/1.25  #Strategies tried      : 1
% 2.06/1.25  
% 2.06/1.25  Timing (in seconds)
% 2.06/1.25  ----------------------
% 2.06/1.26  Preprocessing        : 0.29
% 2.06/1.26  Parsing              : 0.16
% 2.06/1.26  CNF conversion       : 0.02
% 2.06/1.26  Main loop            : 0.18
% 2.06/1.26  Inferencing          : 0.07
% 2.06/1.26  Reduction            : 0.05
% 2.06/1.26  Demodulation         : 0.04
% 2.06/1.26  BG Simplification    : 0.01
% 2.06/1.26  Subsumption          : 0.03
% 2.06/1.26  Abstraction          : 0.01
% 2.06/1.26  MUC search           : 0.00
% 2.06/1.26  Cooper               : 0.00
% 2.06/1.26  Total                : 0.50
% 2.06/1.26  Index Insertion      : 0.00
% 2.06/1.26  Index Deletion       : 0.00
% 2.06/1.26  Index Matching       : 0.00
% 2.06/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
