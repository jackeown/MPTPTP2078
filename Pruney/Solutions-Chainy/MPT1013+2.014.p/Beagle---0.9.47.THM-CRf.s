%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:36 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 126 expanded)
%              Number of leaves         :   31 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 240 expanded)
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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_58,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(B_43)
      | ~ m1_subset_1(B_43,k1_zfmisc_1(A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_64,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_34,c_58])).

tff(c_71,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_64])).

tff(c_30,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_98,plain,(
    ! [A_51,B_52,C_53] :
      ( k2_relset_1(A_51,B_52,C_53) = k2_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_105,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_98])).

tff(c_111,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_105])).

tff(c_122,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_134,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_122])).

tff(c_188,plain,(
    ! [A_65,B_66,C_67] :
      ( m1_subset_1(k1_relset_1(A_65,B_66,C_67),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_208,plain,
    ( m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_188])).

tff(c_216,plain,(
    m1_subset_1(k1_relat_1('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_208])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_251,plain,(
    r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_216,c_2])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ r1_tarski(k1_relat_1(B_14),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_254,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_251,c_14])).

tff(c_260,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_254])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k2_relat_1(k7_relat_1(B_9,A_8)) = k9_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_265,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_10])).

tff(c_269,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_111,c_265])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_67,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_32,c_58])).

tff(c_74,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_28,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_108,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_98])).

tff(c_113,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_108])).

tff(c_166,plain,(
    ! [B_63,A_64] :
      ( k9_relat_1(B_63,k2_relat_1(A_64)) = k2_relat_1(k5_relat_1(A_64,B_63))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_175,plain,(
    ! [B_63] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_63)) = k9_relat_1(B_63,'#skF_1')
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_166])).

tff(c_185,plain,(
    ! [B_63] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_63)) = k9_relat_1(B_63,'#skF_1')
      | ~ v1_relat_1(B_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_175])).

tff(c_280,plain,(
    ! [E_72,F_70,D_73,C_68,B_69,A_71] :
      ( k4_relset_1(A_71,B_69,C_68,D_73,E_72,F_70) = k5_relat_1(E_72,F_70)
      | ~ m1_subset_1(F_70,k1_zfmisc_1(k2_zfmisc_1(C_68,D_73)))
      | ~ m1_subset_1(E_72,k1_zfmisc_1(k2_zfmisc_1(A_71,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_421,plain,(
    ! [A_85,B_86,E_87] :
      ( k4_relset_1(A_85,B_86,'#skF_1','#skF_1',E_87,'#skF_2') = k5_relat_1(E_87,'#skF_2')
      | ~ m1_subset_1(E_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(resolution,[status(thm)],[c_34,c_280])).

tff(c_447,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_421])).

tff(c_18,plain,(
    ! [E_22,D_21,F_23,A_18,C_20,B_19] :
      ( m1_subset_1(k4_relset_1(A_18,B_19,C_20,D_21,E_22,F_23),k1_zfmisc_1(k2_zfmisc_1(A_18,D_21)))
      | ~ m1_subset_1(F_23,k1_zfmisc_1(k2_zfmisc_1(C_20,D_21)))
      | ~ m1_subset_1(E_22,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_580,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_18])).

tff(c_584,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34,c_580])).

tff(c_22,plain,(
    ! [A_27,B_28,C_29] :
      ( k2_relset_1(A_27,B_28,C_29) = k2_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_613,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_584,c_22])).

tff(c_26,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_576,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_26])).

tff(c_685,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_613,c_576])).

tff(c_692,plain,
    ( k9_relat_1('#skF_2','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_685])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_269,c_692])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:19:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.45  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k4_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.94/1.45  
% 2.94/1.45  %Foreground sorts:
% 2.94/1.45  
% 2.94/1.45  
% 2.94/1.45  %Background operators:
% 2.94/1.45  
% 2.94/1.45  
% 2.94/1.45  %Foreground operators:
% 2.94/1.45  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.94/1.45  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.94/1.45  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.94/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.94/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.94/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.94/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.94/1.45  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.94/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.94/1.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.94/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.45  
% 2.94/1.47  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.94/1.47  tff(f_91, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A))) => (((k2_relset_1(A, A, B) = A) & (k2_relset_1(A, A, C) = A)) => (k2_relset_1(A, A, k4_relset_1(A, A, A, A, C, B)) = A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_funct_2)).
% 2.94/1.47  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.94/1.47  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.94/1.47  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.94/1.47  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 2.94/1.47  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.94/1.47  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.94/1.47  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.94/1.47  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.94/1.47  tff(f_79, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 2.94/1.47  tff(f_65, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 2.94/1.47  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.94/1.47  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.94/1.47  tff(c_58, plain, (![B_43, A_44]: (v1_relat_1(B_43) | ~m1_subset_1(B_43, k1_zfmisc_1(A_44)) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.94/1.47  tff(c_64, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_58])).
% 2.94/1.47  tff(c_71, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_64])).
% 2.94/1.47  tff(c_30, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.94/1.47  tff(c_98, plain, (![A_51, B_52, C_53]: (k2_relset_1(A_51, B_52, C_53)=k2_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.94/1.47  tff(c_105, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_98])).
% 2.94/1.47  tff(c_111, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_105])).
% 2.94/1.47  tff(c_122, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.94/1.47  tff(c_134, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_122])).
% 2.94/1.47  tff(c_188, plain, (![A_65, B_66, C_67]: (m1_subset_1(k1_relset_1(A_65, B_66, C_67), k1_zfmisc_1(A_65)) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.94/1.47  tff(c_208, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_134, c_188])).
% 2.94/1.47  tff(c_216, plain, (m1_subset_1(k1_relat_1('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_208])).
% 2.94/1.47  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.94/1.47  tff(c_251, plain, (r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_216, c_2])).
% 2.94/1.47  tff(c_14, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~r1_tarski(k1_relat_1(B_14), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.94/1.47  tff(c_254, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_251, c_14])).
% 2.94/1.47  tff(c_260, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_254])).
% 2.94/1.47  tff(c_10, plain, (![B_9, A_8]: (k2_relat_1(k7_relat_1(B_9, A_8))=k9_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.94/1.47  tff(c_265, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_260, c_10])).
% 2.94/1.47  tff(c_269, plain, (k9_relat_1('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_111, c_265])).
% 2.94/1.47  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.94/1.47  tff(c_67, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_32, c_58])).
% 2.94/1.47  tff(c_74, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_67])).
% 2.94/1.47  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.94/1.47  tff(c_108, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_98])).
% 2.94/1.47  tff(c_113, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_108])).
% 2.94/1.47  tff(c_166, plain, (![B_63, A_64]: (k9_relat_1(B_63, k2_relat_1(A_64))=k2_relat_1(k5_relat_1(A_64, B_63)) | ~v1_relat_1(B_63) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.94/1.47  tff(c_175, plain, (![B_63]: (k2_relat_1(k5_relat_1('#skF_3', B_63))=k9_relat_1(B_63, '#skF_1') | ~v1_relat_1(B_63) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_113, c_166])).
% 2.94/1.47  tff(c_185, plain, (![B_63]: (k2_relat_1(k5_relat_1('#skF_3', B_63))=k9_relat_1(B_63, '#skF_1') | ~v1_relat_1(B_63))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_175])).
% 2.94/1.47  tff(c_280, plain, (![E_72, F_70, D_73, C_68, B_69, A_71]: (k4_relset_1(A_71, B_69, C_68, D_73, E_72, F_70)=k5_relat_1(E_72, F_70) | ~m1_subset_1(F_70, k1_zfmisc_1(k2_zfmisc_1(C_68, D_73))) | ~m1_subset_1(E_72, k1_zfmisc_1(k2_zfmisc_1(A_71, B_69))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.94/1.47  tff(c_421, plain, (![A_85, B_86, E_87]: (k4_relset_1(A_85, B_86, '#skF_1', '#skF_1', E_87, '#skF_2')=k5_relat_1(E_87, '#skF_2') | ~m1_subset_1(E_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(resolution, [status(thm)], [c_34, c_280])).
% 2.94/1.47  tff(c_447, plain, (k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_421])).
% 2.94/1.47  tff(c_18, plain, (![E_22, D_21, F_23, A_18, C_20, B_19]: (m1_subset_1(k4_relset_1(A_18, B_19, C_20, D_21, E_22, F_23), k1_zfmisc_1(k2_zfmisc_1(A_18, D_21))) | ~m1_subset_1(F_23, k1_zfmisc_1(k2_zfmisc_1(C_20, D_21))) | ~m1_subset_1(E_22, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.94/1.47  tff(c_580, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_447, c_18])).
% 2.94/1.47  tff(c_584, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34, c_580])).
% 2.94/1.47  tff(c_22, plain, (![A_27, B_28, C_29]: (k2_relset_1(A_27, B_28, C_29)=k2_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.94/1.47  tff(c_613, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))=k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_584, c_22])).
% 2.94/1.47  tff(c_26, plain, (k2_relset_1('#skF_1', '#skF_1', k4_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.94/1.47  tff(c_576, plain, (k2_relset_1('#skF_1', '#skF_1', k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_447, c_26])).
% 2.94/1.47  tff(c_685, plain, (k2_relat_1(k5_relat_1('#skF_3', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_613, c_576])).
% 2.94/1.47  tff(c_692, plain, (k9_relat_1('#skF_2', '#skF_1')!='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_185, c_685])).
% 2.94/1.47  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_71, c_269, c_692])).
% 2.94/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.94/1.47  
% 2.94/1.47  Inference rules
% 2.94/1.47  ----------------------
% 2.94/1.47  #Ref     : 0
% 2.94/1.47  #Sup     : 163
% 2.94/1.47  #Fact    : 0
% 2.94/1.47  #Define  : 0
% 2.94/1.47  #Split   : 1
% 2.94/1.47  #Chain   : 0
% 2.94/1.47  #Close   : 0
% 2.94/1.47  
% 2.94/1.47  Ordering : KBO
% 2.94/1.47  
% 2.94/1.47  Simplification rules
% 2.94/1.47  ----------------------
% 2.94/1.47  #Subsume      : 13
% 2.94/1.47  #Demod        : 55
% 2.94/1.47  #Tautology    : 51
% 2.94/1.47  #SimpNegUnit  : 0
% 2.94/1.47  #BackRed      : 2
% 2.94/1.47  
% 2.94/1.47  #Partial instantiations: 0
% 2.94/1.47  #Strategies tried      : 1
% 2.94/1.47  
% 2.94/1.47  Timing (in seconds)
% 2.94/1.47  ----------------------
% 2.94/1.47  Preprocessing        : 0.34
% 2.94/1.47  Parsing              : 0.19
% 2.94/1.47  CNF conversion       : 0.02
% 2.94/1.47  Main loop            : 0.33
% 2.94/1.47  Inferencing          : 0.13
% 2.94/1.47  Reduction            : 0.10
% 2.94/1.47  Demodulation         : 0.07
% 2.94/1.47  BG Simplification    : 0.02
% 2.94/1.47  Subsumption          : 0.06
% 2.94/1.47  Abstraction          : 0.02
% 2.94/1.47  MUC search           : 0.00
% 2.94/1.47  Cooper               : 0.00
% 2.94/1.47  Total                : 0.70
% 2.94/1.47  Index Insertion      : 0.00
% 2.94/1.47  Index Deletion       : 0.00
% 2.94/1.47  Index Matching       : 0.00
% 2.94/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
