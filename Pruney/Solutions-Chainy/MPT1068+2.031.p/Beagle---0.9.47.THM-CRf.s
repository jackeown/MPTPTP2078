%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:45 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 187 expanded)
%              Number of leaves         :   35 (  82 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 ( 674 expanded)
%              Number of equality atoms :   46 ( 159 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k8_funct_2,type,(
    k8_funct_2: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ! [E] :
                ( ( v1_funct_1(E)
                  & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(C,A))) )
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ( r1_tarski(k2_relset_1(B,C,D),k1_relset_1(C,A,E))
                     => ( B = k1_xboole_0
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k1_funct_1(E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_relat_1(E)
            & v1_funct_1(E) )
         => ( r2_hidden(C,A)
           => ( B = k1_xboole_0
              | k1_funct_1(k5_relat_1(D,E),C) = k1_funct_1(E,k1_funct_1(D,C)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_funct_2)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( r1_tarski(k2_relset_1(A,B,D),k1_relset_1(B,C,E))
           => ( B = k1_xboole_0
              | k8_funct_2(A,B,C,D,E) = k1_partfun1(A,B,B,C,D,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_2)).

tff(c_24,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_55,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_61,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_55])).

tff(c_67,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_61])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_40] :
      ( k1_xboole_0 = A_40
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_44,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_20])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_32,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_21,B_22,E_26,D_24,C_23] :
      ( k1_funct_1(k5_relat_1(D_24,E_26),C_23) = k1_funct_1(E_26,k1_funct_1(D_24,C_23))
      | k1_xboole_0 = B_22
      | ~ r2_hidden(C_23,A_21)
      | ~ v1_funct_1(E_26)
      | ~ v1_relat_1(E_26)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22)))
      | ~ v1_funct_2(D_24,A_21,B_22)
      | ~ v1_funct_1(D_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_115,plain,(
    ! [B_62,A_58,D_59,C_61,E_60] :
      ( k1_funct_1(k5_relat_1(D_59,E_60),C_61) = k1_funct_1(E_60,k1_funct_1(D_59,C_61))
      | B_62 = '#skF_1'
      | ~ r2_hidden(C_61,A_58)
      | ~ v1_funct_1(E_60)
      | ~ v1_relat_1(E_60)
      | ~ m1_subset_1(D_59,k1_zfmisc_1(k2_zfmisc_1(A_58,B_62)))
      | ~ v1_funct_2(D_59,A_58,B_62)
      | ~ v1_funct_1(D_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_16])).

tff(c_127,plain,(
    ! [B_63,E_66,A_65,D_67,B_64] :
      ( k1_funct_1(k5_relat_1(D_67,E_66),A_65) = k1_funct_1(E_66,k1_funct_1(D_67,A_65))
      | B_64 = '#skF_1'
      | ~ v1_funct_1(E_66)
      | ~ v1_relat_1(E_66)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_63,B_64)))
      | ~ v1_funct_2(D_67,B_63,B_64)
      | ~ v1_funct_1(D_67)
      | v1_xboole_0(B_63)
      | ~ m1_subset_1(A_65,B_63) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_129,plain,(
    ! [E_66,A_65] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_66),A_65) = k1_funct_1(E_66,k1_funct_1('#skF_5',A_65))
      | '#skF_1' = '#skF_4'
      | ~ v1_funct_1(E_66)
      | ~ v1_relat_1(E_66)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_65,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_127])).

tff(c_134,plain,(
    ! [E_66,A_65] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_66),A_65) = k1_funct_1(E_66,k1_funct_1('#skF_5',A_65))
      | '#skF_1' = '#skF_4'
      | ~ v1_funct_1(E_66)
      | ~ v1_relat_1(E_66)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_65,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_129])).

tff(c_140,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_134])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_43,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2])).

tff(c_143,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_140,c_43])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_143])).

tff(c_148,plain,(
    ! [E_66,A_65] :
      ( '#skF_1' = '#skF_4'
      | k1_funct_1(k5_relat_1('#skF_5',E_66),A_65) = k1_funct_1(E_66,k1_funct_1('#skF_5',A_65))
      | ~ v1_funct_1(E_66)
      | ~ v1_relat_1(E_66)
      | ~ m1_subset_1(A_65,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_134])).

tff(c_150,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_148])).

tff(c_165,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_4])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_165])).

tff(c_168,plain,(
    ! [E_66,A_65] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_66),A_65) = k1_funct_1(E_66,k1_funct_1('#skF_5',A_65))
      | ~ v1_funct_1(E_66)
      | ~ v1_relat_1(E_66)
      | ~ m1_subset_1(A_65,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_169,plain,(
    '#skF_1' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_148])).

tff(c_69,plain,(
    ! [C_46,E_50,F_49,A_51,D_47,B_48] :
      ( k1_partfun1(A_51,B_48,C_46,D_47,E_50,F_49) = k5_relat_1(E_50,F_49)
      | ~ m1_subset_1(F_49,k1_zfmisc_1(k2_zfmisc_1(C_46,D_47)))
      | ~ v1_funct_1(F_49)
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_48)))
      | ~ v1_funct_1(E_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_73,plain,(
    ! [A_51,B_48,E_50] :
      ( k1_partfun1(A_51,B_48,'#skF_4','#skF_2',E_50,'#skF_6') = k5_relat_1(E_50,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_48)))
      | ~ v1_funct_1(E_50) ) ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_101,plain,(
    ! [A_55,B_56,E_57] :
      ( k1_partfun1(A_55,B_56,'#skF_4','#skF_2',E_57,'#skF_6') = k5_relat_1(E_57,'#skF_6')
      | ~ m1_subset_1(E_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ v1_funct_1(E_57) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_73])).

tff(c_104,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_101])).

tff(c_110,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_104])).

tff(c_22,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_12,plain,(
    ! [C_11,B_10,E_14,D_12,A_9] :
      ( k1_partfun1(A_9,B_10,B_10,C_11,D_12,E_14) = k8_funct_2(A_9,B_10,C_11,D_12,E_14)
      | k1_xboole_0 = B_10
      | ~ r1_tarski(k2_relset_1(A_9,B_10,D_12),k1_relset_1(B_10,C_11,E_14))
      | ~ m1_subset_1(E_14,k1_zfmisc_1(k2_zfmisc_1(B_10,C_11)))
      | ~ v1_funct_1(E_14)
      | ~ m1_subset_1(D_12,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10)))
      | ~ v1_funct_2(D_12,A_9,B_10)
      | ~ v1_funct_1(D_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_180,plain,(
    ! [B_75,D_78,E_76,C_77,A_79] :
      ( k1_partfun1(A_79,B_75,B_75,C_77,D_78,E_76) = k8_funct_2(A_79,B_75,C_77,D_78,E_76)
      | B_75 = '#skF_1'
      | ~ r1_tarski(k2_relset_1(A_79,B_75,D_78),k1_relset_1(B_75,C_77,E_76))
      | ~ m1_subset_1(E_76,k1_zfmisc_1(k2_zfmisc_1(B_75,C_77)))
      | ~ v1_funct_1(E_76)
      | ~ m1_subset_1(D_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_75)))
      | ~ v1_funct_2(D_78,A_79,B_75)
      | ~ v1_funct_1(D_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_183,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | '#skF_1' = '#skF_4'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_180])).

tff(c_186,plain,
    ( k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_110,c_183])).

tff(c_187,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_186])).

tff(c_18,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_188,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_18])).

tff(c_195,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_188])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_67,c_28,c_195])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:14:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.31  
% 2.36/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.31  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.36/1.31  
% 2.36/1.31  %Foreground sorts:
% 2.36/1.31  
% 2.36/1.31  
% 2.36/1.31  %Background operators:
% 2.36/1.31  
% 2.36/1.31  
% 2.36/1.31  %Foreground operators:
% 2.36/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.36/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.36/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.36/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.31  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.36/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.36/1.31  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.36/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.36/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.36/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.36/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.36/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.36/1.31  
% 2.36/1.33  tff(f_115, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 2.36/1.33  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.36/1.33  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.36/1.33  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 2.36/1.33  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.36/1.33  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.36/1.33  tff(f_90, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_funct_2)).
% 2.36/1.33  tff(f_73, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.36/1.33  tff(f_63, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 2.36/1.33  tff(c_24, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.36/1.33  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_55, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.36/1.33  tff(c_61, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_55])).
% 2.36/1.33  tff(c_67, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_61])).
% 2.36/1.33  tff(c_28, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.33  tff(c_38, plain, (![A_40]: (k1_xboole_0=A_40 | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.33  tff(c_42, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_38])).
% 2.36/1.33  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_44, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_20])).
% 2.36/1.33  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_32, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.36/1.33  tff(c_16, plain, (![A_21, B_22, E_26, D_24, C_23]: (k1_funct_1(k5_relat_1(D_24, E_26), C_23)=k1_funct_1(E_26, k1_funct_1(D_24, C_23)) | k1_xboole_0=B_22 | ~r2_hidden(C_23, A_21) | ~v1_funct_1(E_26) | ~v1_relat_1(E_26) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))) | ~v1_funct_2(D_24, A_21, B_22) | ~v1_funct_1(D_24))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.36/1.33  tff(c_115, plain, (![B_62, A_58, D_59, C_61, E_60]: (k1_funct_1(k5_relat_1(D_59, E_60), C_61)=k1_funct_1(E_60, k1_funct_1(D_59, C_61)) | B_62='#skF_1' | ~r2_hidden(C_61, A_58) | ~v1_funct_1(E_60) | ~v1_relat_1(E_60) | ~m1_subset_1(D_59, k1_zfmisc_1(k2_zfmisc_1(A_58, B_62))) | ~v1_funct_2(D_59, A_58, B_62) | ~v1_funct_1(D_59))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_16])).
% 2.36/1.33  tff(c_127, plain, (![B_63, E_66, A_65, D_67, B_64]: (k1_funct_1(k5_relat_1(D_67, E_66), A_65)=k1_funct_1(E_66, k1_funct_1(D_67, A_65)) | B_64='#skF_1' | ~v1_funct_1(E_66) | ~v1_relat_1(E_66) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_63, B_64))) | ~v1_funct_2(D_67, B_63, B_64) | ~v1_funct_1(D_67) | v1_xboole_0(B_63) | ~m1_subset_1(A_65, B_63))), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.36/1.33  tff(c_129, plain, (![E_66, A_65]: (k1_funct_1(k5_relat_1('#skF_5', E_66), A_65)=k1_funct_1(E_66, k1_funct_1('#skF_5', A_65)) | '#skF_1'='#skF_4' | ~v1_funct_1(E_66) | ~v1_relat_1(E_66) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_65, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_127])).
% 2.36/1.33  tff(c_134, plain, (![E_66, A_65]: (k1_funct_1(k5_relat_1('#skF_5', E_66), A_65)=k1_funct_1(E_66, k1_funct_1('#skF_5', A_65)) | '#skF_1'='#skF_4' | ~v1_funct_1(E_66) | ~v1_relat_1(E_66) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_65, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_129])).
% 2.36/1.33  tff(c_140, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_134])).
% 2.36/1.33  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.33  tff(c_43, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2])).
% 2.36/1.33  tff(c_143, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_140, c_43])).
% 2.36/1.33  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_143])).
% 2.36/1.33  tff(c_148, plain, (![E_66, A_65]: ('#skF_1'='#skF_4' | k1_funct_1(k5_relat_1('#skF_5', E_66), A_65)=k1_funct_1(E_66, k1_funct_1('#skF_5', A_65)) | ~v1_funct_1(E_66) | ~v1_relat_1(E_66) | ~m1_subset_1(A_65, '#skF_3'))), inference(splitRight, [status(thm)], [c_134])).
% 2.36/1.33  tff(c_150, plain, ('#skF_1'='#skF_4'), inference(splitLeft, [status(thm)], [c_148])).
% 2.36/1.33  tff(c_165, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_150, c_4])).
% 2.36/1.33  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_165])).
% 2.36/1.33  tff(c_168, plain, (![E_66, A_65]: (k1_funct_1(k5_relat_1('#skF_5', E_66), A_65)=k1_funct_1(E_66, k1_funct_1('#skF_5', A_65)) | ~v1_funct_1(E_66) | ~v1_relat_1(E_66) | ~m1_subset_1(A_65, '#skF_3'))), inference(splitRight, [status(thm)], [c_148])).
% 2.36/1.33  tff(c_169, plain, ('#skF_1'!='#skF_4'), inference(splitRight, [status(thm)], [c_148])).
% 2.36/1.33  tff(c_69, plain, (![C_46, E_50, F_49, A_51, D_47, B_48]: (k1_partfun1(A_51, B_48, C_46, D_47, E_50, F_49)=k5_relat_1(E_50, F_49) | ~m1_subset_1(F_49, k1_zfmisc_1(k2_zfmisc_1(C_46, D_47))) | ~v1_funct_1(F_49) | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_48))) | ~v1_funct_1(E_50))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.33  tff(c_73, plain, (![A_51, B_48, E_50]: (k1_partfun1(A_51, B_48, '#skF_4', '#skF_2', E_50, '#skF_6')=k5_relat_1(E_50, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_48))) | ~v1_funct_1(E_50))), inference(resolution, [status(thm)], [c_26, c_69])).
% 2.36/1.33  tff(c_101, plain, (![A_55, B_56, E_57]: (k1_partfun1(A_55, B_56, '#skF_4', '#skF_2', E_57, '#skF_6')=k5_relat_1(E_57, '#skF_6') | ~m1_subset_1(E_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~v1_funct_1(E_57))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_73])).
% 2.36/1.33  tff(c_104, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_101])).
% 2.36/1.33  tff(c_110, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_104])).
% 2.36/1.33  tff(c_22, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_12, plain, (![C_11, B_10, E_14, D_12, A_9]: (k1_partfun1(A_9, B_10, B_10, C_11, D_12, E_14)=k8_funct_2(A_9, B_10, C_11, D_12, E_14) | k1_xboole_0=B_10 | ~r1_tarski(k2_relset_1(A_9, B_10, D_12), k1_relset_1(B_10, C_11, E_14)) | ~m1_subset_1(E_14, k1_zfmisc_1(k2_zfmisc_1(B_10, C_11))) | ~v1_funct_1(E_14) | ~m1_subset_1(D_12, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))) | ~v1_funct_2(D_12, A_9, B_10) | ~v1_funct_1(D_12))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.36/1.33  tff(c_180, plain, (![B_75, D_78, E_76, C_77, A_79]: (k1_partfun1(A_79, B_75, B_75, C_77, D_78, E_76)=k8_funct_2(A_79, B_75, C_77, D_78, E_76) | B_75='#skF_1' | ~r1_tarski(k2_relset_1(A_79, B_75, D_78), k1_relset_1(B_75, C_77, E_76)) | ~m1_subset_1(E_76, k1_zfmisc_1(k2_zfmisc_1(B_75, C_77))) | ~v1_funct_1(E_76) | ~m1_subset_1(D_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_75))) | ~v1_funct_2(D_78, A_79, B_75) | ~v1_funct_1(D_78))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_12])).
% 2.36/1.33  tff(c_183, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | '#skF_1'='#skF_4' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_180])).
% 2.36/1.33  tff(c_186, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | '#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_110, c_183])).
% 2.36/1.33  tff(c_187, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_169, c_186])).
% 2.36/1.33  tff(c_18, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 2.36/1.33  tff(c_188, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_18])).
% 2.36/1.33  tff(c_195, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_168, c_188])).
% 2.36/1.33  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_67, c_28, c_195])).
% 2.36/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.33  
% 2.36/1.33  Inference rules
% 2.36/1.33  ----------------------
% 2.36/1.33  #Ref     : 0
% 2.36/1.33  #Sup     : 31
% 2.36/1.33  #Fact    : 0
% 2.36/1.33  #Define  : 0
% 2.36/1.33  #Split   : 3
% 2.36/1.33  #Chain   : 0
% 2.36/1.33  #Close   : 0
% 2.36/1.33  
% 2.36/1.33  Ordering : KBO
% 2.36/1.33  
% 2.36/1.33  Simplification rules
% 2.36/1.33  ----------------------
% 2.36/1.33  #Subsume      : 0
% 2.36/1.33  #Demod        : 39
% 2.36/1.33  #Tautology    : 15
% 2.36/1.33  #SimpNegUnit  : 4
% 2.36/1.33  #BackRed      : 10
% 2.36/1.33  
% 2.36/1.33  #Partial instantiations: 0
% 2.36/1.33  #Strategies tried      : 1
% 2.36/1.33  
% 2.36/1.33  Timing (in seconds)
% 2.36/1.33  ----------------------
% 2.36/1.33  Preprocessing        : 0.33
% 2.36/1.33  Parsing              : 0.19
% 2.36/1.33  CNF conversion       : 0.03
% 2.36/1.33  Main loop            : 0.19
% 2.36/1.33  Inferencing          : 0.07
% 2.36/1.33  Reduction            : 0.06
% 2.36/1.33  Demodulation         : 0.05
% 2.36/1.33  BG Simplification    : 0.01
% 2.36/1.33  Subsumption          : 0.03
% 2.36/1.33  Abstraction          : 0.01
% 2.36/1.33  MUC search           : 0.00
% 2.36/1.33  Cooper               : 0.00
% 2.36/1.33  Total                : 0.56
% 2.36/1.33  Index Insertion      : 0.00
% 2.36/1.33  Index Deletion       : 0.00
% 2.36/1.33  Index Matching       : 0.00
% 2.36/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
