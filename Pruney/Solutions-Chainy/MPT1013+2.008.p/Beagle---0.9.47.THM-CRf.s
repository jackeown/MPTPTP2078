%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:35 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.87s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :    9
%              Number of atoms          :   84 ( 183 expanded)
%              Number of equality atoms :   29 (  78 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_290,plain,(
    ! [B_67,A_70,E_68,C_66,F_69,D_71] :
      ( k4_relset_1(A_70,B_67,C_66,D_71,E_68,F_69) = k5_relat_1(E_68,F_69)
      | ~ m1_subset_1(F_69,k1_zfmisc_1(k2_zfmisc_1(C_66,D_71)))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(A_70,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_365,plain,(
    ! [A_86,B_87,E_88] :
      ( k4_relset_1(A_86,B_87,'#skF_1','#skF_1',E_88,'#skF_2') = k5_relat_1(E_88,'#skF_2')
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(resolution,[status(thm)],[c_28,c_290])).

tff(c_383,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_365])).

tff(c_20,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_388,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_20])).

tff(c_51,plain,(
    ! [C_35,A_36,B_37] :
      ( v1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_36,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_63,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_51])).

tff(c_24,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_94,plain,(
    ! [A_44,B_45,C_46] :
      ( k2_relset_1(A_44,B_45,C_46) = k2_relat_1(C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_101,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_107,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_101])).

tff(c_76,plain,(
    ! [A_41,B_42,C_43] :
      ( k1_relset_1(A_41,B_42,C_43) = k1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_88,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_76])).

tff(c_122,plain,(
    ! [A_47,B_48,C_49] :
      ( m1_subset_1(k1_relset_1(A_47,B_48,C_49),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_143,plain,
    ( m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_122])).

tff(c_151,plain,(
    m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_143])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_159,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_151,c_2])).

tff(c_64,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_51])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_104,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_109,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_104])).

tff(c_171,plain,(
    ! [B_53,A_54] :
      ( k2_relat_1(k5_relat_1(B_53,A_54)) = k2_relat_1(A_54)
      | ~ r1_tarski(k1_relat_1(A_54),k2_relat_1(B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_174,plain,(
    ! [A_54] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_54)) = k2_relat_1(A_54)
      | ~ r1_tarski(k1_relat_1(A_54),'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_171])).

tff(c_236,plain,(
    ! [A_64] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_64)) = k2_relat_1(A_64)
      | ~ r1_tarski(k1_relat_1(A_64),'#skF_1')
      | ~ v1_relat_1(A_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_174])).

tff(c_239,plain,
    ( k2_relat_1(k5_relat_1('#skF_3','#skF_2')) = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_159,c_236])).

tff(c_245,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_107,c_239])).

tff(c_393,plain,(
    ! [D_92,E_91,C_94,B_89,F_93,A_90] :
      ( m1_subset_1(k4_relset_1(A_90,B_89,C_94,D_92,E_91,F_93),k1_zfmisc_1(k2_zfmisc_1(A_90,D_92)))
      | ~ m1_subset_1(F_93,k1_zfmisc_1(k2_zfmisc_1(C_94,D_92)))
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(A_90,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_422,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_393])).

tff(c_442,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_422])).

tff(c_16,plain,(
    ! [A_21,B_22,C_23] :
      ( k2_relset_1(A_21,B_22,C_23) = k2_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_524,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_442,c_16])).

tff(c_539,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_524])).

tff(c_541,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_388,c_539])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:42:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.51  
% 2.87/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.52  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.87/1.52  
% 2.87/1.52  %Foreground sorts:
% 2.87/1.52  
% 2.87/1.52  
% 2.87/1.52  %Background operators:
% 2.87/1.52  
% 2.87/1.52  
% 2.87/1.52  %Foreground operators:
% 2.87/1.52  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.52  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.87/1.52  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.87/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.87/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.52  
% 2.87/1.53  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_2)).
% 2.87/1.53  tff(f_66, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.87/1.53  tff(f_42, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.87/1.53  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.87/1.53  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.87/1.53  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.87/1.53  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.87/1.53  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 2.87/1.53  tff(f_52, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.87/1.53  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.53  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.53  tff(c_290, plain, (![B_67, A_70, E_68, C_66, F_69, D_71]: (k4_relset_1(A_70, B_67, C_66, D_71, E_68, F_69)=k5_relat_1(E_68, F_69) | ~m1_subset_1(F_69, k1_zfmisc_1(k2_zfmisc_1(C_66, D_71))) | ~m1_subset_1(E_68, k1_zfmisc_1(k2_zfmisc_1(A_70, B_67))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.87/1.53  tff(c_365, plain, (![A_86, B_87, E_88]: (k4_relset_1(A_86, B_87, '#skF_1', '#skF_1', E_88, '#skF_2')=k5_relat_1(E_88, '#skF_2') | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(resolution, [status(thm)], [c_28, c_290])).
% 2.87/1.53  tff(c_383, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_365])).
% 2.87/1.53  tff(c_20, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.53  tff(c_388, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_20])).
% 2.87/1.53  tff(c_51, plain, (![C_35, A_36, B_37]: (v1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_36, B_37))))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.87/1.53  tff(c_63, plain, (v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_51])).
% 2.87/1.53  tff(c_24, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.53  tff(c_94, plain, (![A_44, B_45, C_46]: (k2_relset_1(A_44, B_45, C_46)=k2_relat_1(C_46) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.53  tff(c_101, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_94])).
% 2.87/1.53  tff(c_107, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_101])).
% 2.87/1.53  tff(c_76, plain, (![A_41, B_42, C_43]: (k1_relset_1(A_41, B_42, C_43)=k1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.87/1.53  tff(c_88, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_76])).
% 2.87/1.53  tff(c_122, plain, (![A_47, B_48, C_49]: (m1_subset_1(k1_relset_1(A_47, B_48, C_49), k1_zfmisc_1(A_47)) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.87/1.53  tff(c_143, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_88, c_122])).
% 2.87/1.53  tff(c_151, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_143])).
% 2.87/1.53  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.87/1.53  tff(c_159, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_151, c_2])).
% 2.87/1.53  tff(c_64, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_51])).
% 2.87/1.53  tff(c_22, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.87/1.53  tff(c_104, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_94])).
% 2.87/1.53  tff(c_109, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_104])).
% 2.87/1.53  tff(c_171, plain, (![B_53, A_54]: (k2_relat_1(k5_relat_1(B_53, A_54))=k2_relat_1(A_54) | ~r1_tarski(k1_relat_1(A_54), k2_relat_1(B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.87/1.53  tff(c_174, plain, (![A_54]: (k2_relat_1(k5_relat_1('#skF_3', A_54))=k2_relat_1(A_54) | ~r1_tarski(k1_relat_1(A_54), '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_54))), inference(superposition, [status(thm), theory('equality')], [c_109, c_171])).
% 2.87/1.53  tff(c_236, plain, (![A_64]: (k2_relat_1(k5_relat_1('#skF_3', A_64))=k2_relat_1(A_64) | ~r1_tarski(k1_relat_1(A_64), '#skF_1') | ~v1_relat_1(A_64))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_174])).
% 2.87/1.53  tff(c_239, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_159, c_236])).
% 2.87/1.53  tff(c_245, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_63, c_107, c_239])).
% 2.87/1.53  tff(c_393, plain, (![D_92, E_91, C_94, B_89, F_93, A_90]: (m1_subset_1(k4_relset_1(A_90, B_89, C_94, D_92, E_91, F_93), k1_zfmisc_1(k2_zfmisc_1(A_90, D_92))) | ~m1_subset_1(F_93, k1_zfmisc_1(k2_zfmisc_1(C_94, D_92))) | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(A_90, B_89))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.87/1.53  tff(c_422, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_383, c_393])).
% 2.87/1.53  tff(c_442, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_422])).
% 2.87/1.53  tff(c_16, plain, (![A_21, B_22, C_23]: (k2_relset_1(A_21, B_22, C_23)=k2_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.87/1.53  tff(c_524, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_442, c_16])).
% 2.87/1.53  tff(c_539, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_245, c_524])).
% 2.87/1.53  tff(c_541, plain, $false, inference(negUnitSimplification, [status(thm)], [c_388, c_539])).
% 2.87/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.53  
% 2.87/1.53  Inference rules
% 2.87/1.53  ----------------------
% 2.87/1.53  #Ref     : 0
% 2.87/1.53  #Sup     : 129
% 2.87/1.53  #Fact    : 0
% 2.87/1.53  #Define  : 0
% 2.87/1.53  #Split   : 0
% 2.87/1.53  #Chain   : 0
% 2.87/1.53  #Close   : 0
% 2.87/1.53  
% 2.87/1.53  Ordering : KBO
% 2.87/1.53  
% 2.87/1.53  Simplification rules
% 2.87/1.53  ----------------------
% 2.87/1.53  #Subsume      : 1
% 2.87/1.53  #Demod        : 48
% 2.87/1.53  #Tautology    : 47
% 2.87/1.53  #SimpNegUnit  : 1
% 2.87/1.53  #BackRed      : 1
% 2.87/1.53  
% 2.87/1.53  #Partial instantiations: 0
% 2.87/1.53  #Strategies tried      : 1
% 2.87/1.53  
% 2.87/1.53  Timing (in seconds)
% 2.87/1.53  ----------------------
% 2.87/1.54  Preprocessing        : 0.41
% 2.87/1.54  Parsing              : 0.24
% 2.87/1.54  CNF conversion       : 0.02
% 2.87/1.54  Main loop            : 0.35
% 2.87/1.54  Inferencing          : 0.14
% 2.87/1.54  Reduction            : 0.10
% 2.87/1.54  Demodulation         : 0.07
% 2.87/1.54  BG Simplification    : 0.02
% 2.87/1.54  Subsumption          : 0.06
% 2.87/1.54  Abstraction          : 0.02
% 2.87/1.54  MUC search           : 0.00
% 2.87/1.54  Cooper               : 0.00
% 2.87/1.54  Total                : 0.80
% 2.87/1.54  Index Insertion      : 0.00
% 2.87/1.54  Index Deletion       : 0.00
% 2.87/1.54  Index Matching       : 0.00
% 2.87/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
