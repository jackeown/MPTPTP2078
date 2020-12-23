%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:36 EST 2020

% Result     : Theorem 2.37s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 118 expanded)
%              Number of leaves         :   29 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   97 ( 228 expanded)
%              Number of equality atoms :   30 (  82 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_87,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_138,plain,(
    ! [D_51,F_54,A_52,C_53,E_56,B_55] :
      ( k4_relset_1(A_52,B_55,C_53,D_51,E_56,F_54) = k5_relat_1(E_56,F_54)
      | ~ m1_subset_1(F_54,k1_zfmisc_1(k2_zfmisc_1(C_53,D_51)))
      | ~ m1_subset_1(E_56,k1_zfmisc_1(k2_zfmisc_1(A_52,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_177,plain,(
    ! [A_58,B_59,E_60] :
      ( k4_relset_1(A_58,B_59,'#skF_1','#skF_1',E_60,'#skF_2') = k5_relat_1(E_60,'#skF_2')
      | ~ m1_subset_1(E_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(resolution,[status(thm)],[c_30,c_138])).

tff(c_185,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_177])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_190,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_22])).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_49,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_43])).

tff(c_26,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_103,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_106,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_103])).

tff(c_111,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_106])).

tff(c_54,plain,(
    ! [C_38,A_39,B_40] :
      ( v4_relat_1(C_38,A_39)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_61,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_54])).

tff(c_72,plain,(
    ! [B_44,A_45] :
      ( k7_relat_1(B_44,A_45) = B_44
      | ~ v4_relat_1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_78,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_61,c_72])).

tff(c_84,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_78])).

tff(c_10,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_12,A_11)),A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,
    ( r1_tarski(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_10])).

tff(c_92,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_88])).

tff(c_46,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_28,c_40])).

tff(c_52,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_46])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_109,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_103])).

tff(c_113,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_109])).

tff(c_122,plain,(
    ! [B_49,A_50] :
      ( k2_relat_1(k5_relat_1(B_49,A_50)) = k2_relat_1(A_50)
      | ~ r1_tarski(k1_relat_1(A_50),k2_relat_1(B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_125,plain,(
    ! [A_50] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_50)) = k2_relat_1(A_50)
      | ~ r1_tarski(k1_relat_1(A_50),'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_122])).

tff(c_145,plain,(
    ! [A_57] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_57)) = k2_relat_1(A_57)
      | ~ r1_tarski(k1_relat_1(A_57),'#skF_1')
      | ~ v1_relat_1(A_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_125])).

tff(c_151,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_92,c_145])).

tff(c_161,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_111,c_151])).

tff(c_220,plain,(
    ! [B_63,D_66,A_65,C_67,F_62,E_64] :
      ( m1_subset_1(k4_relset_1(A_65,B_63,C_67,D_66,E_64,F_62),k1_zfmisc_1(k2_zfmisc_1(A_65,D_66)))
      | ~ m1_subset_1(F_62,k1_zfmisc_1(k2_zfmisc_1(C_67,D_66)))
      | ~ m1_subset_1(E_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_240,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_220])).

tff(c_253,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_30,c_240])).

tff(c_18,plain,(
    ! [A_22,B_23,C_24] :
      ( k2_relset_1(A_22,B_23,C_24) = k2_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_326,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_253,c_18])).

tff(c_340,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_326])).

tff(c_342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_190,c_340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:40:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.37/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.41  
% 2.37/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.41  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.37/1.41  
% 2.37/1.41  %Foreground sorts:
% 2.37/1.41  
% 2.37/1.41  
% 2.37/1.41  %Background operators:
% 2.37/1.41  
% 2.37/1.41  
% 2.37/1.41  %Foreground operators:
% 2.37/1.41  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.37/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.37/1.41  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.37/1.41  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.37/1.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.37/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.37/1.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.37/1.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.37/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.37/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.37/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.37/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.37/1.41  
% 2.65/1.43  tff(f_87, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_2)).
% 2.65/1.43  tff(f_75, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.65/1.43  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.65/1.43  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.65/1.43  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.65/1.43  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.65/1.43  tff(f_40, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.65/1.43  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.65/1.43  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.65/1.43  tff(f_65, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.65/1.43  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.43  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.43  tff(c_138, plain, (![D_51, F_54, A_52, C_53, E_56, B_55]: (k4_relset_1(A_52, B_55, C_53, D_51, E_56, F_54)=k5_relat_1(E_56, F_54) | ~m1_subset_1(F_54, k1_zfmisc_1(k2_zfmisc_1(C_53, D_51))) | ~m1_subset_1(E_56, k1_zfmisc_1(k2_zfmisc_1(A_52, B_55))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.43  tff(c_177, plain, (![A_58, B_59, E_60]: (k4_relset_1(A_58, B_59, '#skF_1', '#skF_1', E_60, '#skF_2')=k5_relat_1(E_60, '#skF_2') | ~m1_subset_1(E_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(resolution, [status(thm)], [c_30, c_138])).
% 2.65/1.43  tff(c_185, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_177])).
% 2.65/1.43  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.43  tff(c_190, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_22])).
% 2.65/1.43  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.65/1.43  tff(c_40, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.65/1.43  tff(c_43, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_30, c_40])).
% 2.65/1.43  tff(c_49, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_43])).
% 2.65/1.43  tff(c_26, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.43  tff(c_103, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.65/1.43  tff(c_106, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_103])).
% 2.65/1.43  tff(c_111, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_106])).
% 2.65/1.43  tff(c_54, plain, (![C_38, A_39, B_40]: (v4_relat_1(C_38, A_39) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.65/1.43  tff(c_61, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_54])).
% 2.65/1.43  tff(c_72, plain, (![B_44, A_45]: (k7_relat_1(B_44, A_45)=B_44 | ~v4_relat_1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.65/1.43  tff(c_78, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_61, c_72])).
% 2.65/1.43  tff(c_84, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_78])).
% 2.65/1.43  tff(c_10, plain, (![B_12, A_11]: (r1_tarski(k1_relat_1(k7_relat_1(B_12, A_11)), A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.65/1.43  tff(c_88, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_84, c_10])).
% 2.65/1.43  tff(c_92, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_49, c_88])).
% 2.65/1.43  tff(c_46, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_28, c_40])).
% 2.65/1.43  tff(c_52, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_46])).
% 2.65/1.43  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.65/1.43  tff(c_109, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_103])).
% 2.65/1.43  tff(c_113, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_109])).
% 2.65/1.43  tff(c_122, plain, (![B_49, A_50]: (k2_relat_1(k5_relat_1(B_49, A_50))=k2_relat_1(A_50) | ~r1_tarski(k1_relat_1(A_50), k2_relat_1(B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.65/1.43  tff(c_125, plain, (![A_50]: (k2_relat_1(k5_relat_1('#skF_3', A_50))=k2_relat_1(A_50) | ~r1_tarski(k1_relat_1(A_50), '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_113, c_122])).
% 2.65/1.43  tff(c_145, plain, (![A_57]: (k2_relat_1(k5_relat_1('#skF_3', A_57))=k2_relat_1(A_57) | ~r1_tarski(k1_relat_1(A_57), '#skF_1') | ~v1_relat_1(A_57))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_125])).
% 2.65/1.43  tff(c_151, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_92, c_145])).
% 2.65/1.43  tff(c_161, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_49, c_111, c_151])).
% 2.65/1.43  tff(c_220, plain, (![B_63, D_66, A_65, C_67, F_62, E_64]: (m1_subset_1(k4_relset_1(A_65, B_63, C_67, D_66, E_64, F_62), k1_zfmisc_1(k2_zfmisc_1(A_65, D_66))) | ~m1_subset_1(F_62, k1_zfmisc_1(k2_zfmisc_1(C_67, D_66))) | ~m1_subset_1(E_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_63))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.43  tff(c_240, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_185, c_220])).
% 2.65/1.43  tff(c_253, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_30, c_240])).
% 2.65/1.43  tff(c_18, plain, (![A_22, B_23, C_24]: (k2_relset_1(A_22, B_23, C_24)=k2_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.65/1.43  tff(c_326, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_253, c_18])).
% 2.65/1.43  tff(c_340, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_326])).
% 2.65/1.43  tff(c_342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_190, c_340])).
% 2.65/1.43  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.43  
% 2.65/1.43  Inference rules
% 2.65/1.43  ----------------------
% 2.65/1.43  #Ref     : 0
% 2.65/1.43  #Sup     : 81
% 2.65/1.43  #Fact    : 0
% 2.65/1.43  #Define  : 0
% 2.65/1.43  #Split   : 0
% 2.65/1.43  #Chain   : 0
% 2.65/1.43  #Close   : 0
% 2.65/1.43  
% 2.65/1.43  Ordering : KBO
% 2.65/1.43  
% 2.65/1.43  Simplification rules
% 2.65/1.43  ----------------------
% 2.65/1.43  #Subsume      : 0
% 2.65/1.43  #Demod        : 28
% 2.65/1.43  #Tautology    : 26
% 2.65/1.43  #SimpNegUnit  : 1
% 2.65/1.43  #BackRed      : 1
% 2.65/1.43  
% 2.65/1.43  #Partial instantiations: 0
% 2.65/1.43  #Strategies tried      : 1
% 2.65/1.43  
% 2.65/1.43  Timing (in seconds)
% 2.65/1.43  ----------------------
% 2.65/1.43  Preprocessing        : 0.39
% 2.65/1.43  Parsing              : 0.19
% 2.65/1.43  CNF conversion       : 0.03
% 2.65/1.43  Main loop            : 0.26
% 2.65/1.43  Inferencing          : 0.10
% 2.65/1.43  Reduction            : 0.08
% 2.65/1.43  Demodulation         : 0.06
% 2.65/1.43  BG Simplification    : 0.02
% 2.65/1.43  Subsumption          : 0.04
% 2.65/1.43  Abstraction          : 0.02
% 2.65/1.43  MUC search           : 0.00
% 2.65/1.43  Cooper               : 0.00
% 2.65/1.43  Total                : 0.69
% 2.65/1.43  Index Insertion      : 0.00
% 2.65/1.43  Index Deletion       : 0.00
% 2.65/1.43  Index Matching       : 0.00
% 2.65/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
