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
% DateTime   : Thu Dec  3 10:13:46 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 115 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :   87 ( 219 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
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

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_29,plain,(
    ! [C_26,A_27,B_28] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_33,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_29])).

tff(c_41,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_24,c_41])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( k7_relat_1(B_5,A_4) = B_5
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_45,c_4])).

tff(c_51,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_48])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_7,A_6)),A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_55,plain,
    ( r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_6])).

tff(c_59,plain,(
    r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_55])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_61,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(B_41,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_39] :
      ( r1_tarski(A_39,'#skF_3')
      | ~ r1_tarski(A_39,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_61])).

tff(c_132,plain,(
    ! [D_54,B_55,C_56,A_57] :
      ( m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(B_55,C_56)))
      | ~ r1_tarski(k1_relat_1(D_54),B_55)
      | ~ m1_subset_1(D_54,k1_zfmisc_1(k2_zfmisc_1(A_57,C_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_136,plain,(
    ! [B_58] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_58,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_58) ) ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( v4_relat_1(C_13,A_11)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_154,plain,(
    ! [B_59] :
      ( v4_relat_1('#skF_4',B_59)
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_59) ) ),
    inference(resolution,[status(thm)],[c_136,c_12])).

tff(c_158,plain,
    ( v4_relat_1('#skF_4','#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_154])).

tff(c_164,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_158])).

tff(c_169,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_164,c_4])).

tff(c_172,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_169])).

tff(c_28,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_227,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( k2_partfun1(A_64,B_65,C_66,D_67) = k7_relat_1(C_66,D_67)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65)))
      | ~ v1_funct_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_231,plain,(
    ! [D_67] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_67) = k7_relat_1('#skF_4',D_67)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_227])).

tff(c_237,plain,(
    ! [D_67] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_67) = k7_relat_1('#skF_4',D_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_231])).

tff(c_20,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_238,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_237,c_20])).

tff(c_239,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_238])).

tff(c_135,plain,(
    ! [B_55] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_55,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_55) ) ),
    inference(resolution,[status(thm)],[c_24,c_132])).

tff(c_333,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( r2_relset_1(A_78,B_79,C_80,C_80)
      | ~ m1_subset_1(D_81,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79)))
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_340,plain,(
    ! [C_82] :
      ( r2_relset_1('#skF_1','#skF_2',C_82,C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(resolution,[status(thm)],[c_24,c_333])).

tff(c_343,plain,
    ( r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_135,c_340])).

tff(c_348,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_343])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_239,c_348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:15:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.40  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.47/1.40  
% 2.47/1.40  %Foreground sorts:
% 2.47/1.40  
% 2.47/1.40  
% 2.47/1.40  %Background operators:
% 2.47/1.40  
% 2.47/1.40  
% 2.47/1.40  %Foreground operators:
% 2.47/1.40  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.40  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 2.47/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.47/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.40  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.47/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.40  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.47/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.40  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 2.47/1.40  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.47/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.40  
% 2.47/1.41  tff(f_80, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_funct_2)).
% 2.47/1.41  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.47/1.41  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.47/1.41  tff(f_37, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 2.47/1.41  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.47/1.41  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.47/1.41  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 2.47/1.41  tff(f_69, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 2.47/1.41  tff(f_57, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 2.47/1.41  tff(c_24, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.41  tff(c_29, plain, (![C_26, A_27, B_28]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.41  tff(c_33, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_29])).
% 2.47/1.41  tff(c_41, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.41  tff(c_45, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_24, c_41])).
% 2.47/1.41  tff(c_4, plain, (![B_5, A_4]: (k7_relat_1(B_5, A_4)=B_5 | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.41  tff(c_48, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_45, c_4])).
% 2.47/1.41  tff(c_51, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_48])).
% 2.47/1.41  tff(c_6, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(k7_relat_1(B_7, A_6)), A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.47/1.41  tff(c_55, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_51, c_6])).
% 2.47/1.41  tff(c_59, plain, (r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_55])).
% 2.47/1.41  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.41  tff(c_61, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(B_41, C_40) | ~r1_tarski(A_39, B_41))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.41  tff(c_70, plain, (![A_39]: (r1_tarski(A_39, '#skF_3') | ~r1_tarski(A_39, '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_61])).
% 2.47/1.41  tff(c_132, plain, (![D_54, B_55, C_56, A_57]: (m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(B_55, C_56))) | ~r1_tarski(k1_relat_1(D_54), B_55) | ~m1_subset_1(D_54, k1_zfmisc_1(k2_zfmisc_1(A_57, C_56))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.47/1.41  tff(c_136, plain, (![B_58]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_58, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_58))), inference(resolution, [status(thm)], [c_24, c_132])).
% 2.47/1.41  tff(c_12, plain, (![C_13, A_11, B_12]: (v4_relat_1(C_13, A_11) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.41  tff(c_154, plain, (![B_59]: (v4_relat_1('#skF_4', B_59) | ~r1_tarski(k1_relat_1('#skF_4'), B_59))), inference(resolution, [status(thm)], [c_136, c_12])).
% 2.47/1.41  tff(c_158, plain, (v4_relat_1('#skF_4', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_70, c_154])).
% 2.47/1.41  tff(c_164, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_158])).
% 2.47/1.41  tff(c_169, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_164, c_4])).
% 2.47/1.41  tff(c_172, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_169])).
% 2.47/1.41  tff(c_28, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.41  tff(c_227, plain, (![A_64, B_65, C_66, D_67]: (k2_partfun1(A_64, B_65, C_66, D_67)=k7_relat_1(C_66, D_67) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))) | ~v1_funct_1(C_66))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.47/1.41  tff(c_231, plain, (![D_67]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_67)=k7_relat_1('#skF_4', D_67) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_227])).
% 2.47/1.41  tff(c_237, plain, (![D_67]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_67)=k7_relat_1('#skF_4', D_67))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_231])).
% 2.47/1.41  tff(c_20, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.47/1.41  tff(c_238, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_237, c_20])).
% 2.47/1.41  tff(c_239, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_238])).
% 2.47/1.41  tff(c_135, plain, (![B_55]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_55, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_55))), inference(resolution, [status(thm)], [c_24, c_132])).
% 2.47/1.41  tff(c_333, plain, (![A_78, B_79, C_80, D_81]: (r2_relset_1(A_78, B_79, C_80, C_80) | ~m1_subset_1(D_81, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.41  tff(c_340, plain, (![C_82]: (r2_relset_1('#skF_1', '#skF_2', C_82, C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(resolution, [status(thm)], [c_24, c_333])).
% 2.47/1.41  tff(c_343, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_135, c_340])).
% 2.47/1.41  tff(c_348, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_59, c_343])).
% 2.47/1.41  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_239, c_348])).
% 2.47/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.41  
% 2.47/1.41  Inference rules
% 2.47/1.41  ----------------------
% 2.47/1.41  #Ref     : 0
% 2.47/1.41  #Sup     : 70
% 2.47/1.41  #Fact    : 0
% 2.47/1.41  #Define  : 0
% 2.47/1.41  #Split   : 1
% 2.47/1.41  #Chain   : 0
% 2.47/1.41  #Close   : 0
% 2.47/1.41  
% 2.47/1.41  Ordering : KBO
% 2.47/1.41  
% 2.47/1.41  Simplification rules
% 2.47/1.41  ----------------------
% 2.47/1.41  #Subsume      : 12
% 2.47/1.41  #Demod        : 28
% 2.47/1.41  #Tautology    : 17
% 2.47/1.41  #SimpNegUnit  : 1
% 2.47/1.41  #BackRed      : 1
% 2.47/1.41  
% 2.47/1.41  #Partial instantiations: 0
% 2.47/1.41  #Strategies tried      : 1
% 2.47/1.41  
% 2.47/1.41  Timing (in seconds)
% 2.47/1.41  ----------------------
% 2.47/1.42  Preprocessing        : 0.32
% 2.47/1.42  Parsing              : 0.17
% 2.47/1.42  CNF conversion       : 0.02
% 2.47/1.42  Main loop            : 0.31
% 2.47/1.42  Inferencing          : 0.12
% 2.47/1.42  Reduction            : 0.08
% 2.47/1.42  Demodulation         : 0.06
% 2.47/1.42  BG Simplification    : 0.01
% 2.47/1.42  Subsumption          : 0.07
% 2.47/1.42  Abstraction          : 0.02
% 2.47/1.42  MUC search           : 0.00
% 2.47/1.42  Cooper               : 0.00
% 2.47/1.42  Total                : 0.67
% 2.47/1.42  Index Insertion      : 0.00
% 2.47/1.42  Index Deletion       : 0.00
% 2.47/1.42  Index Matching       : 0.00
% 2.47/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
