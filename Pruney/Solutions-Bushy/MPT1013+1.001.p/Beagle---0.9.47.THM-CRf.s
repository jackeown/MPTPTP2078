%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT1013+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:15 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of leaves         :   26 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 162 expanded)
%              Number of equality atoms :   32 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > v1_relat_1 > k4_relset_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A)))
           => ( ( k2_relset_1(A,A,B) = A
                & k2_relset_1(A,A,C) = A )
             => k2_relset_1(A,A,k4_relset_1(A,A,A,A,C,B)) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_funct_2)).

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_44,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_34,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_35,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_35])).

tff(c_106,plain,(
    ! [A_40,B_41,C_42,D_43] :
      ( k7_relset_1(A_40,B_41,C_42,D_43) = k9_relat_1(C_42,D_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_130,plain,(
    ! [D_47] : k7_relset_1('#skF_1','#skF_1','#skF_2',D_47) = k9_relat_1('#skF_2',D_47) ),
    inference(resolution,[status(thm)],[c_26,c_106])).

tff(c_22,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_113,plain,(
    ! [A_44,B_45,C_46] :
      ( k7_relset_1(A_44,B_45,C_46,A_44) = k2_relset_1(A_44,B_45,C_46)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_115,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_2','#skF_1') = k2_relset_1('#skF_1','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_113])).

tff(c_119,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_115])).

tff(c_136,plain,(
    k9_relat_1('#skF_2','#skF_1') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_119])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_43,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_35])).

tff(c_20,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_33,B_34,C_35] :
      ( k2_relset_1(A_33,B_34,C_35) = k2_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_54,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_50])).

tff(c_63,plain,(
    ! [B_36,A_37] :
      ( k9_relat_1(B_36,k2_relat_1(A_37)) = k2_relat_1(k5_relat_1(A_37,B_36))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_72,plain,(
    ! [B_36] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_36)) = k9_relat_1(B_36,'#skF_1')
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_63])).

tff(c_79,plain,(
    ! [B_36] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_36)) = k9_relat_1(B_36,'#skF_1')
      | ~ v1_relat_1(B_36) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_43,c_72])).

tff(c_177,plain,(
    ! [E_55,F_52,A_56,C_57,D_53,B_54] :
      ( k4_relset_1(A_56,B_54,C_57,D_53,E_55,F_52) = k5_relat_1(E_55,F_52)
      | ~ m1_subset_1(F_52,k1_zfmisc_1(k2_zfmisc_1(C_57,D_53)))
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_209,plain,(
    ! [A_61,B_62,E_63] :
      ( k4_relset_1(A_61,B_62,'#skF_1','#skF_1',E_63,'#skF_2') = k5_relat_1(E_63,'#skF_2')
      | ~ m1_subset_1(E_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62))) ) ),
    inference(resolution,[status(thm)],[c_26,c_177])).

tff(c_217,plain,(
    k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_209])).

tff(c_227,plain,(
    ! [D_67,B_64,F_65,E_68,C_66,A_69] :
      ( m1_subset_1(k4_relset_1(A_69,B_64,C_66,D_67,E_68,F_65),k1_zfmisc_1(k2_zfmisc_1(A_69,D_67)))
      | ~ m1_subset_1(F_65,k1_zfmisc_1(k2_zfmisc_1(C_66,D_67)))
      | ~ m1_subset_1(E_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_250,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_227])).

tff(c_269,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_250])).

tff(c_6,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_302,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) = k2_relat_1(k5_relat_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_269,c_6])).

tff(c_18,plain,(
    k2_relset_1('#skF_1','#skF_1',k4_relset_1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_222,plain,(
    k2_relset_1('#skF_1','#skF_1',k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_18])).

tff(c_423,plain,(
    k2_relat_1(k5_relat_1('#skF_3','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_222])).

tff(c_430,plain,
    ( k9_relat_1('#skF_2','#skF_1') != '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_423])).

tff(c_433,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_136,c_430])).

%------------------------------------------------------------------------------
