%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:34 EST 2020

% Result     : Theorem 3.03s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 105 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 200 expanded)
%              Number of equality atoms :   34 (  86 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_37,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_37])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_112,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_115,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_112])).

tff(c_120,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_115])).

tff(c_55,plain,(
    ! [C_36,A_37,B_38] :
      ( v4_relat_1(C_36,A_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_62,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_64,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = B_39
      | ~ v4_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_70,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_64])).

tff(c_76,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_70])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k2_relat_1(k7_relat_1(B_2,A_1)) = k9_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_98,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_2])).

tff(c_102,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_98])).

tff(c_123,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_102])).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_45,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_37])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_118,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_112])).

tff(c_122,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_118])).

tff(c_141,plain,(
    ! [B_46,A_47] :
      ( k9_relat_1(B_46,k2_relat_1(A_47)) = k2_relat_1(k5_relat_1(A_47,B_46))
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_150,plain,(
    ! [B_46] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_46)) = k9_relat_1(B_46,'#skF_1')
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_141])).

tff(c_160,plain,(
    ! [B_46] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_46)) = k9_relat_1(B_46,'#skF_1')
      | ~ v1_relat_1(B_46) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_150])).

tff(c_233,plain,(
    ! [E_59,C_57,D_61,A_62,B_60,F_58] :
      ( k4_relset_1(A_62,B_60,C_57,D_61,E_59,F_58) = k5_relat_1(E_59,F_58)
      | ~ m1_subset_1(F_58,k1_zfmisc_1(k2_zfmisc_1(C_57,D_61)))
      | ~ m1_subset_1(E_59,k1_zfmisc_1(k2_zfmisc_1(A_62,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_240,plain,(
    ! [A_63,B_64,E_65] :
      ( k4_relset_1(A_63,B_64,'#skF_1','#skF_1',E_65,'#skF_2') = k5_relat_1(E_65,'#skF_2')
      | ~ m1_subset_1(E_65,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(resolution,[status(thm)],[c_28,c_233])).

tff(c_248,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_240])).

tff(c_258,plain,(
    ! [B_70,E_66,F_67,D_68,C_69,A_71] :
      ( m1_subset_1(k4_relset_1(A_71,B_70,C_69,D_68,E_66,F_67),k1_zfmisc_1(k2_zfmisc_1(A_71,D_68)))
      | ~ m1_subset_1(F_67,k1_zfmisc_1(k2_zfmisc_1(C_69,D_68)))
      | ~ m1_subset_1(E_66,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_278,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_258])).

tff(c_289,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_278])).

tff(c_16,plain,(
    ! [A_20,B_21,C_22] :
      ( k2_relset_1(A_20,B_21,C_22) = k2_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_311,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_289,c_16])).

tff(c_20,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_253,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_20])).

tff(c_593,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_311,c_253])).

tff(c_600,plain,
    ( k9_relat_1('#skF_2','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_593])).

tff(c_603,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_123,c_600])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:19:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.03/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.49  
% 3.03/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.03/1.49  %$ v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.03/1.49  
% 3.03/1.49  %Foreground sorts:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Background operators:
% 3.03/1.49  
% 3.03/1.49  
% 3.03/1.49  %Foreground operators:
% 3.03/1.49  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.03/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.03/1.49  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.03/1.49  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.03/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.03/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.03/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.03/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.03/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.03/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.03/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.03/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.03/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.03/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.03/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.03/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.03/1.49  
% 3.09/1.51  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_2)).
% 3.09/1.51  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.09/1.51  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.09/1.51  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.09/1.51  tff(f_42, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 3.09/1.51  tff(f_29, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.09/1.51  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.09/1.51  tff(f_68, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.09/1.51  tff(f_58, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.09/1.51  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.51  tff(c_37, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.09/1.51  tff(c_44, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_37])).
% 3.09/1.51  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.51  tff(c_112, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.09/1.51  tff(c_115, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_112])).
% 3.09/1.51  tff(c_120, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_115])).
% 3.09/1.51  tff(c_55, plain, (![C_36, A_37, B_38]: (v4_relat_1(C_36, A_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.09/1.51  tff(c_62, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_55])).
% 3.09/1.51  tff(c_64, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=B_39 | ~v4_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.09/1.51  tff(c_70, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_62, c_64])).
% 3.09/1.51  tff(c_76, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_70])).
% 3.09/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_relat_1(k7_relat_1(B_2, A_1))=k9_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.09/1.51  tff(c_98, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_76, c_2])).
% 3.09/1.51  tff(c_102, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_98])).
% 3.09/1.51  tff(c_123, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_120, c_102])).
% 3.09/1.51  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.51  tff(c_45, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_37])).
% 3.09/1.51  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.51  tff(c_118, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_112])).
% 3.09/1.51  tff(c_122, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_118])).
% 3.09/1.51  tff(c_141, plain, (![B_46, A_47]: (k9_relat_1(B_46, k2_relat_1(A_47))=k2_relat_1(k5_relat_1(A_47, B_46)) | ~v1_relat_1(B_46) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.09/1.51  tff(c_150, plain, (![B_46]: (k2_relat_1(k5_relat_1('#skF_3', B_46))=k9_relat_1(B_46, '#skF_1') | ~v1_relat_1(B_46) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_122, c_141])).
% 3.09/1.51  tff(c_160, plain, (![B_46]: (k2_relat_1(k5_relat_1('#skF_3', B_46))=k9_relat_1(B_46, '#skF_1') | ~v1_relat_1(B_46))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_150])).
% 3.09/1.51  tff(c_233, plain, (![E_59, C_57, D_61, A_62, B_60, F_58]: (k4_relset_1(A_62, B_60, C_57, D_61, E_59, F_58)=k5_relat_1(E_59, F_58) | ~m1_subset_1(F_58, k1_zfmisc_1(k2_zfmisc_1(C_57, D_61))) | ~m1_subset_1(E_59, k1_zfmisc_1(k2_zfmisc_1(A_62, B_60))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.09/1.51  tff(c_240, plain, (![A_63, B_64, E_65]: (k4_relset_1(A_63, B_64, '#skF_1', '#skF_1', E_65, '#skF_2')=k5_relat_1(E_65, '#skF_2') | ~m1_subset_1(E_65, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(resolution, [status(thm)], [c_28, c_233])).
% 3.09/1.51  tff(c_248, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_240])).
% 3.09/1.51  tff(c_258, plain, (![B_70, E_66, F_67, D_68, C_69, A_71]: (m1_subset_1(k4_relset_1(A_71, B_70, C_69, D_68, E_66, F_67), k1_zfmisc_1(k2_zfmisc_1(A_71, D_68))) | ~m1_subset_1(F_67, k1_zfmisc_1(k2_zfmisc_1(C_69, D_68))) | ~m1_subset_1(E_66, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.09/1.51  tff(c_278, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_248, c_258])).
% 3.09/1.51  tff(c_289, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_278])).
% 3.09/1.51  tff(c_16, plain, (![A_20, B_21, C_22]: (k2_relset_1(A_20, B_21, C_22)=k2_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.09/1.51  tff(c_311, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_289, c_16])).
% 3.09/1.51  tff(c_20, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.09/1.51  tff(c_253, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_248, c_20])).
% 3.09/1.51  tff(c_593, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_311, c_253])).
% 3.09/1.51  tff(c_600, plain, (k9_relat_1('#skF_2', '#skF_1')!='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_160, c_593])).
% 3.09/1.51  tff(c_603, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_123, c_600])).
% 3.09/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.09/1.51  
% 3.09/1.51  Inference rules
% 3.09/1.51  ----------------------
% 3.09/1.51  #Ref     : 0
% 3.09/1.51  #Sup     : 161
% 3.09/1.51  #Fact    : 0
% 3.09/1.51  #Define  : 0
% 3.09/1.51  #Split   : 0
% 3.09/1.51  #Chain   : 0
% 3.09/1.51  #Close   : 0
% 3.09/1.51  
% 3.09/1.51  Ordering : KBO
% 3.09/1.51  
% 3.09/1.51  Simplification rules
% 3.09/1.51  ----------------------
% 3.09/1.51  #Subsume      : 2
% 3.09/1.51  #Demod        : 50
% 3.09/1.51  #Tautology    : 60
% 3.09/1.51  #SimpNegUnit  : 0
% 3.09/1.51  #BackRed      : 4
% 3.09/1.52  
% 3.09/1.52  #Partial instantiations: 0
% 3.09/1.52  #Strategies tried      : 1
% 3.09/1.52  
% 3.09/1.52  Timing (in seconds)
% 3.09/1.52  ----------------------
% 3.09/1.52  Preprocessing        : 0.32
% 3.09/1.52  Parsing              : 0.17
% 3.09/1.52  CNF conversion       : 0.02
% 3.09/1.52  Main loop            : 0.41
% 3.09/1.52  Inferencing          : 0.16
% 3.09/1.52  Reduction            : 0.12
% 3.09/1.52  Demodulation         : 0.09
% 3.09/1.52  BG Simplification    : 0.02
% 3.09/1.52  Subsumption          : 0.07
% 3.09/1.52  Abstraction          : 0.03
% 3.09/1.52  MUC search           : 0.00
% 3.09/1.52  Cooper               : 0.00
% 3.09/1.52  Total                : 0.78
% 3.09/1.52  Index Insertion      : 0.00
% 3.09/1.52  Index Deletion       : 0.00
% 3.09/1.52  Index Matching       : 0.00
% 3.09/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
