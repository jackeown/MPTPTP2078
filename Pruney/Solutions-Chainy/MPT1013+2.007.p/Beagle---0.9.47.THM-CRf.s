%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:35 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 114 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :   10
%              Number of atoms          :   95 ( 216 expanded)
%              Number of equality atoms :   36 (  91 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_55,plain,(
    ! [C_39,A_40,B_41] :
      ( v1_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_67,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_55])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_135,plain,(
    ! [A_57,B_58,C_59] :
      ( k2_relset_1(A_57,B_58,C_59) = k2_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_142,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_135])).

tff(c_148,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_142])).

tff(c_90,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_102,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_90])).

tff(c_193,plain,(
    ! [A_62,B_63,C_64] :
      ( m1_subset_1(k1_relset_1(A_62,B_63,C_64),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_62,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_214,plain,
    ( m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_193])).

tff(c_222,plain,(
    m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_214])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_245,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_222,c_2])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_248,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_245,c_10])).

tff(c_251,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_248])).

tff(c_6,plain,(
    ! [B_4,A_3] :
      ( k2_relat_1(k7_relat_1(B_4,A_3)) = k9_relat_1(B_4,A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_255,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_6])).

tff(c_259,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_148,c_255])).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_68,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_55])).

tff(c_26,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_145,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_150,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_145])).

tff(c_8,plain,(
    ! [B_7,A_5] :
      ( k9_relat_1(B_7,k2_relat_1(A_5)) = k2_relat_1(k5_relat_1(A_5,B_7))
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_163,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_7)) = k9_relat_1(B_7,'#skF_1')
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_8])).

tff(c_167,plain,(
    ! [B_7] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_7)) = k9_relat_1(B_7,'#skF_1')
      | ~ v1_relat_1(B_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_163])).

tff(c_280,plain,(
    ! [F_68,D_73,A_70,B_72,E_69,C_71] :
      ( k4_relset_1(A_70,B_72,C_71,D_73,E_69,F_68) = k5_relat_1(E_69,F_68)
      | ~ m1_subset_1(F_68,k1_zfmisc_1(k2_zfmisc_1(C_71,D_73)))
      | ~ m1_subset_1(E_69,k1_zfmisc_1(k2_zfmisc_1(A_70,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_344,plain,(
    ! [A_84,B_85,E_86] :
      ( k4_relset_1(A_84,B_85,'#skF_1','#skF_1',E_86,'#skF_2') = k5_relat_1(E_86,'#skF_2')
      | ~ m1_subset_1(E_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(resolution,[status(thm)],[c_32,c_280])).

tff(c_362,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_344])).

tff(c_399,plain,(
    ! [C_99,B_95,E_96,F_94,D_98,A_97] :
      ( m1_subset_1(k4_relset_1(A_97,B_95,C_99,D_98,E_96,F_94),k1_zfmisc_1(k2_zfmisc_1(A_97,D_98)))
      | ~ m1_subset_1(F_94,k1_zfmisc_1(k2_zfmisc_1(C_99,D_98)))
      | ~ m1_subset_1(E_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_425,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_399])).

tff(c_438,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32,c_425])).

tff(c_20,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_relset_1(A_25,B_26,C_27) = k2_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_463,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_438,c_20])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_367,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_24])).

tff(c_842,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_367])).

tff(c_849,plain,
    ( k9_relat_1('#skF_2','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_842])).

tff(c_852,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_259,c_849])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  
% 2.79/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.44  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.79/1.44  
% 2.79/1.44  %Foreground sorts:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Background operators:
% 2.79/1.44  
% 2.79/1.44  
% 2.79/1.44  %Foreground operators:
% 2.79/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.79/1.44  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.79/1.44  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.79/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.79/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.79/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.79/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.79/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.79/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.79/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.79/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.44  
% 3.12/1.46  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_funct_2)).
% 3.12/1.46  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.12/1.46  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.12/1.46  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.12/1.46  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 3.12/1.46  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.12/1.46  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.12/1.46  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 3.12/1.46  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.12/1.46  tff(f_74, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.12/1.46  tff(f_60, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.12/1.46  tff(c_32, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.12/1.46  tff(c_55, plain, (![C_39, A_40, B_41]: (v1_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.12/1.46  tff(c_67, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_55])).
% 3.12/1.46  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.12/1.46  tff(c_135, plain, (![A_57, B_58, C_59]: (k2_relset_1(A_57, B_58, C_59)=k2_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.12/1.46  tff(c_142, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_135])).
% 3.12/1.46  tff(c_148, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_142])).
% 3.12/1.46  tff(c_90, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.12/1.46  tff(c_102, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_90])).
% 3.12/1.46  tff(c_193, plain, (![A_62, B_63, C_64]: (m1_subset_1(k1_relset_1(A_62, B_63, C_64), k1_zfmisc_1(A_62)) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_62, B_63))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.12/1.46  tff(c_214, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_102, c_193])).
% 3.12/1.46  tff(c_222, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_214])).
% 3.12/1.46  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.12/1.46  tff(c_245, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_222, c_2])).
% 3.12/1.46  tff(c_10, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~r1_tarski(k1_relat_1(B_9), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.12/1.46  tff(c_248, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_245, c_10])).
% 3.12/1.46  tff(c_251, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_248])).
% 3.12/1.46  tff(c_6, plain, (![B_4, A_3]: (k2_relat_1(k7_relat_1(B_4, A_3))=k9_relat_1(B_4, A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.46  tff(c_255, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_251, c_6])).
% 3.12/1.46  tff(c_259, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_67, c_148, c_255])).
% 3.12/1.46  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.12/1.46  tff(c_68, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_55])).
% 3.12/1.46  tff(c_26, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.12/1.46  tff(c_145, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_30, c_135])).
% 3.12/1.46  tff(c_150, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_145])).
% 3.12/1.46  tff(c_8, plain, (![B_7, A_5]: (k9_relat_1(B_7, k2_relat_1(A_5))=k2_relat_1(k5_relat_1(A_5, B_7)) | ~v1_relat_1(B_7) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.12/1.46  tff(c_163, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_3', B_7))=k9_relat_1(B_7, '#skF_1') | ~v1_relat_1(B_7) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_150, c_8])).
% 3.12/1.46  tff(c_167, plain, (![B_7]: (k2_relat_1(k5_relat_1('#skF_3', B_7))=k9_relat_1(B_7, '#skF_1') | ~v1_relat_1(B_7))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_163])).
% 3.12/1.46  tff(c_280, plain, (![F_68, D_73, A_70, B_72, E_69, C_71]: (k4_relset_1(A_70, B_72, C_71, D_73, E_69, F_68)=k5_relat_1(E_69, F_68) | ~m1_subset_1(F_68, k1_zfmisc_1(k2_zfmisc_1(C_71, D_73))) | ~m1_subset_1(E_69, k1_zfmisc_1(k2_zfmisc_1(A_70, B_72))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.12/1.46  tff(c_344, plain, (![A_84, B_85, E_86]: (k4_relset_1(A_84, B_85, '#skF_1', '#skF_1', E_86, '#skF_2')=k5_relat_1(E_86, '#skF_2') | ~m1_subset_1(E_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(resolution, [status(thm)], [c_32, c_280])).
% 3.12/1.46  tff(c_362, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_344])).
% 3.12/1.46  tff(c_399, plain, (![C_99, B_95, E_96, F_94, D_98, A_97]: (m1_subset_1(k4_relset_1(A_97, B_95, C_99, D_98, E_96, F_94), k1_zfmisc_1(k2_zfmisc_1(A_97, D_98))) | ~m1_subset_1(F_94, k1_zfmisc_1(k2_zfmisc_1(C_99, D_98))) | ~m1_subset_1(E_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_95))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.12/1.46  tff(c_425, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_362, c_399])).
% 3.12/1.46  tff(c_438, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32, c_425])).
% 3.12/1.46  tff(c_20, plain, (![A_25, B_26, C_27]: (k2_relset_1(A_25, B_26, C_27)=k2_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.12/1.46  tff(c_463, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_438, c_20])).
% 3.12/1.46  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.12/1.46  tff(c_367, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_362, c_24])).
% 3.12/1.46  tff(c_842, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_463, c_367])).
% 3.12/1.46  tff(c_849, plain, (k9_relat_1('#skF_2', '#skF_1')!='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_167, c_842])).
% 3.12/1.46  tff(c_852, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_259, c_849])).
% 3.12/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.46  
% 3.12/1.46  Inference rules
% 3.12/1.46  ----------------------
% 3.12/1.46  #Ref     : 0
% 3.12/1.46  #Sup     : 208
% 3.12/1.46  #Fact    : 0
% 3.12/1.46  #Define  : 0
% 3.12/1.46  #Split   : 0
% 3.12/1.46  #Chain   : 0
% 3.12/1.46  #Close   : 0
% 3.12/1.46  
% 3.12/1.46  Ordering : KBO
% 3.12/1.46  
% 3.12/1.46  Simplification rules
% 3.12/1.46  ----------------------
% 3.12/1.46  #Subsume      : 3
% 3.12/1.46  #Demod        : 68
% 3.12/1.46  #Tautology    : 69
% 3.12/1.46  #SimpNegUnit  : 0
% 3.12/1.46  #BackRed      : 3
% 3.12/1.46  
% 3.12/1.46  #Partial instantiations: 0
% 3.12/1.46  #Strategies tried      : 1
% 3.12/1.46  
% 3.12/1.46  Timing (in seconds)
% 3.12/1.46  ----------------------
% 3.12/1.46  Preprocessing        : 0.31
% 3.12/1.46  Parsing              : 0.17
% 3.12/1.46  CNF conversion       : 0.02
% 3.12/1.46  Main loop            : 0.37
% 3.12/1.46  Inferencing          : 0.15
% 3.12/1.46  Reduction            : 0.11
% 3.12/1.46  Demodulation         : 0.08
% 3.12/1.46  BG Simplification    : 0.02
% 3.12/1.46  Subsumption          : 0.06
% 3.12/1.46  Abstraction          : 0.03
% 3.12/1.46  MUC search           : 0.00
% 3.12/1.46  Cooper               : 0.00
% 3.12/1.46  Total                : 0.72
% 3.12/1.46  Index Insertion      : 0.00
% 3.12/1.46  Index Deletion       : 0.00
% 3.12/1.46  Index Matching       : 0.00
% 3.12/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
