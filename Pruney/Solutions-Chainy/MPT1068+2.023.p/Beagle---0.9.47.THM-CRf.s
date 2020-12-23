%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:44 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 180 expanded)
%              Number of leaves         :   34 (  83 expanded)
%              Depth                    :   10
%              Number of atoms          :  148 ( 730 expanded)
%              Number of equality atoms :   40 ( 161 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

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

tff(f_113,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t185_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_61,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_2)).

tff(f_34,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_88,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_funct_2)).

tff(c_24,plain,(
    m1_subset_1('#skF_7','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_59,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_70,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_59])).

tff(c_28,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_32,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_73,plain,(
    ! [B_49,D_48,C_47,E_51,A_52,F_50] :
      ( k1_partfun1(A_52,B_49,C_47,D_48,E_51,F_50) = k5_relat_1(E_51,F_50)
      | ~ m1_subset_1(F_50,k1_zfmisc_1(k2_zfmisc_1(C_47,D_48)))
      | ~ v1_funct_1(F_50)
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_49)))
      | ~ v1_funct_1(E_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_75,plain,(
    ! [A_52,B_49,E_51] :
      ( k1_partfun1(A_52,B_49,'#skF_4','#skF_2',E_51,'#skF_6') = k5_relat_1(E_51,'#skF_6')
      | ~ v1_funct_1('#skF_6')
      | ~ m1_subset_1(E_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_49)))
      | ~ v1_funct_1(E_51) ) ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_88,plain,(
    ! [A_53,B_54,E_55] :
      ( k1_partfun1(A_53,B_54,'#skF_4','#skF_2',E_55,'#skF_6') = k5_relat_1(E_55,'#skF_6')
      | ~ m1_subset_1(E_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_1(E_55) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_75])).

tff(c_98,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_88])).

tff(c_105,plain,(
    k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_98])).

tff(c_22,plain,(
    r1_tarski(k2_relset_1('#skF_3','#skF_4','#skF_5'),k1_relset_1('#skF_4','#skF_2','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_171,plain,(
    ! [E_70,D_72,B_69,C_71,A_73] :
      ( k1_partfun1(A_73,B_69,B_69,C_71,D_72,E_70) = k8_funct_2(A_73,B_69,C_71,D_72,E_70)
      | k1_xboole_0 = B_69
      | ~ r1_tarski(k2_relset_1(A_73,B_69,D_72),k1_relset_1(B_69,C_71,E_70))
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(B_69,C_71)))
      | ~ v1_funct_1(E_70)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_73,B_69)))
      | ~ v1_funct_2(D_72,A_73,B_69)
      | ~ v1_funct_1(D_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_174,plain,
    ( k1_partfun1('#skF_3','#skF_4','#skF_4','#skF_2','#skF_5','#skF_6') = k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_171])).

tff(c_177,plain,
    ( k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_105,c_174])).

tff(c_178,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_4,plain,(
    ! [A_2] : v1_xboole_0('#skF_1'(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    ! [A_39] :
      ( k1_xboole_0 = A_39
      | ~ v1_xboole_0(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_2] : '#skF_1'(A_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4,c_38])).

tff(c_43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4])).

tff(c_185,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_178,c_43])).

tff(c_190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_185])).

tff(c_192,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_115,plain,(
    ! [A_56,E_58,B_60,D_57,C_59] :
      ( k1_funct_1(k5_relat_1(D_57,E_58),C_59) = k1_funct_1(E_58,k1_funct_1(D_57,C_59))
      | k1_xboole_0 = B_60
      | ~ r2_hidden(C_59,A_56)
      | ~ v1_funct_1(E_58)
      | ~ v1_relat_1(E_58)
      | ~ m1_subset_1(D_57,k1_zfmisc_1(k2_zfmisc_1(A_56,B_60)))
      | ~ v1_funct_2(D_57,A_56,B_60)
      | ~ v1_funct_1(D_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_145,plain,(
    ! [B_66,D_67,B_65,A_68,E_64] :
      ( k1_funct_1(k5_relat_1(D_67,E_64),A_68) = k1_funct_1(E_64,k1_funct_1(D_67,A_68))
      | k1_xboole_0 = B_65
      | ~ v1_funct_1(E_64)
      | ~ v1_relat_1(E_64)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_66,B_65)))
      | ~ v1_funct_2(D_67,B_66,B_65)
      | ~ v1_funct_1(D_67)
      | v1_xboole_0(B_66)
      | ~ m1_subset_1(A_68,B_66) ) ),
    inference(resolution,[status(thm)],[c_8,c_115])).

tff(c_152,plain,(
    ! [E_64,A_68] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_64),A_68) = k1_funct_1(E_64,k1_funct_1('#skF_5',A_68))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_64)
      | ~ v1_relat_1(E_64)
      | ~ v1_funct_2('#skF_5','#skF_3','#skF_4')
      | ~ v1_funct_1('#skF_5')
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_68,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_30,c_145])).

tff(c_160,plain,(
    ! [E_64,A_68] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_64),A_68) = k1_funct_1(E_64,k1_funct_1('#skF_5',A_68))
      | k1_xboole_0 = '#skF_4'
      | ~ v1_funct_1(E_64)
      | ~ v1_relat_1(E_64)
      | v1_xboole_0('#skF_3')
      | ~ m1_subset_1(A_68,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_152])).

tff(c_161,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_160])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_164,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_161,c_2])).

tff(c_168,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_164])).

tff(c_169,plain,(
    ! [E_64,A_68] :
      ( k1_xboole_0 = '#skF_4'
      | k1_funct_1(k5_relat_1('#skF_5',E_64),A_68) = k1_funct_1(E_64,k1_funct_1('#skF_5',A_68))
      | ~ v1_funct_1(E_64)
      | ~ v1_relat_1(E_64)
      | ~ m1_subset_1(A_68,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_160])).

tff(c_200,plain,(
    ! [E_74,A_75] :
      ( k1_funct_1(k5_relat_1('#skF_5',E_74),A_75) = k1_funct_1(E_74,k1_funct_1('#skF_5',A_75))
      | ~ v1_funct_1(E_74)
      | ~ v1_relat_1(E_74)
      | ~ m1_subset_1(A_75,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_192,c_169])).

tff(c_191,plain,(
    k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6') = k5_relat_1('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_18,plain,(
    k1_funct_1(k8_funct_2('#skF_3','#skF_4','#skF_2','#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_194,plain,(
    k1_funct_1(k5_relat_1('#skF_5','#skF_6'),'#skF_7') != k1_funct_1('#skF_6',k1_funct_1('#skF_5','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_18])).

tff(c_206,plain,
    ( ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | ~ m1_subset_1('#skF_7','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_194])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_70,c_28,c_206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:47:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.37  
% 2.45/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.38  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 2.45/1.38  
% 2.45/1.38  %Foreground sorts:
% 2.45/1.38  
% 2.45/1.38  
% 2.45/1.38  %Background operators:
% 2.45/1.38  
% 2.45/1.38  
% 2.45/1.38  %Foreground operators:
% 2.45/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.45/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.45/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.45/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.45/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.38  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.45/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.45/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.45/1.38  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.45/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.45/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.45/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.38  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.45/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.45/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.45/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.45/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.38  
% 2.45/1.39  tff(f_113, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.45/1.39  tff(f_44, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.45/1.39  tff(f_71, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.45/1.39  tff(f_61, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.45/1.39  tff(f_34, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & v1_xboole_0(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc2_subset_1)).
% 2.45/1.39  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.45/1.39  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.45/1.39  tff(f_88, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.45/1.39  tff(c_24, plain, (m1_subset_1('#skF_7', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_59, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.45/1.39  tff(c_70, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_26, c_59])).
% 2.45/1.39  tff(c_28, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_36, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_32, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_73, plain, (![B_49, D_48, C_47, E_51, A_52, F_50]: (k1_partfun1(A_52, B_49, C_47, D_48, E_51, F_50)=k5_relat_1(E_51, F_50) | ~m1_subset_1(F_50, k1_zfmisc_1(k2_zfmisc_1(C_47, D_48))) | ~v1_funct_1(F_50) | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_49))) | ~v1_funct_1(E_51))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.45/1.39  tff(c_75, plain, (![A_52, B_49, E_51]: (k1_partfun1(A_52, B_49, '#skF_4', '#skF_2', E_51, '#skF_6')=k5_relat_1(E_51, '#skF_6') | ~v1_funct_1('#skF_6') | ~m1_subset_1(E_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_49))) | ~v1_funct_1(E_51))), inference(resolution, [status(thm)], [c_26, c_73])).
% 2.45/1.39  tff(c_88, plain, (![A_53, B_54, E_55]: (k1_partfun1(A_53, B_54, '#skF_4', '#skF_2', E_55, '#skF_6')=k5_relat_1(E_55, '#skF_6') | ~m1_subset_1(E_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_1(E_55))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_75])).
% 2.45/1.39  tff(c_98, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_88])).
% 2.45/1.39  tff(c_105, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_98])).
% 2.45/1.39  tff(c_22, plain, (r1_tarski(k2_relset_1('#skF_3', '#skF_4', '#skF_5'), k1_relset_1('#skF_4', '#skF_2', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_171, plain, (![E_70, D_72, B_69, C_71, A_73]: (k1_partfun1(A_73, B_69, B_69, C_71, D_72, E_70)=k8_funct_2(A_73, B_69, C_71, D_72, E_70) | k1_xboole_0=B_69 | ~r1_tarski(k2_relset_1(A_73, B_69, D_72), k1_relset_1(B_69, C_71, E_70)) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(B_69, C_71))) | ~v1_funct_1(E_70) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_73, B_69))) | ~v1_funct_2(D_72, A_73, B_69) | ~v1_funct_1(D_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.45/1.39  tff(c_174, plain, (k1_partfun1('#skF_3', '#skF_4', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6') | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_22, c_171])).
% 2.45/1.39  tff(c_177, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_105, c_174])).
% 2.45/1.39  tff(c_178, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_177])).
% 2.45/1.39  tff(c_4, plain, (![A_2]: (v1_xboole_0('#skF_1'(A_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.45/1.39  tff(c_38, plain, (![A_39]: (k1_xboole_0=A_39 | ~v1_xboole_0(A_39))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.39  tff(c_42, plain, (![A_2]: ('#skF_1'(A_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_38])).
% 2.45/1.39  tff(c_43, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4])).
% 2.45/1.39  tff(c_185, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_178, c_43])).
% 2.45/1.39  tff(c_190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_185])).
% 2.45/1.39  tff(c_192, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_177])).
% 2.45/1.39  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_8, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.45/1.39  tff(c_115, plain, (![A_56, E_58, B_60, D_57, C_59]: (k1_funct_1(k5_relat_1(D_57, E_58), C_59)=k1_funct_1(E_58, k1_funct_1(D_57, C_59)) | k1_xboole_0=B_60 | ~r2_hidden(C_59, A_56) | ~v1_funct_1(E_58) | ~v1_relat_1(E_58) | ~m1_subset_1(D_57, k1_zfmisc_1(k2_zfmisc_1(A_56, B_60))) | ~v1_funct_2(D_57, A_56, B_60) | ~v1_funct_1(D_57))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.45/1.39  tff(c_145, plain, (![B_66, D_67, B_65, A_68, E_64]: (k1_funct_1(k5_relat_1(D_67, E_64), A_68)=k1_funct_1(E_64, k1_funct_1(D_67, A_68)) | k1_xboole_0=B_65 | ~v1_funct_1(E_64) | ~v1_relat_1(E_64) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_66, B_65))) | ~v1_funct_2(D_67, B_66, B_65) | ~v1_funct_1(D_67) | v1_xboole_0(B_66) | ~m1_subset_1(A_68, B_66))), inference(resolution, [status(thm)], [c_8, c_115])).
% 2.45/1.39  tff(c_152, plain, (![E_64, A_68]: (k1_funct_1(k5_relat_1('#skF_5', E_64), A_68)=k1_funct_1(E_64, k1_funct_1('#skF_5', A_68)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_64) | ~v1_relat_1(E_64) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3') | ~m1_subset_1(A_68, '#skF_3'))), inference(resolution, [status(thm)], [c_30, c_145])).
% 2.45/1.39  tff(c_160, plain, (![E_64, A_68]: (k1_funct_1(k5_relat_1('#skF_5', E_64), A_68)=k1_funct_1(E_64, k1_funct_1('#skF_5', A_68)) | k1_xboole_0='#skF_4' | ~v1_funct_1(E_64) | ~v1_relat_1(E_64) | v1_xboole_0('#skF_3') | ~m1_subset_1(A_68, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_152])).
% 2.45/1.39  tff(c_161, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_160])).
% 2.45/1.39  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.45/1.39  tff(c_164, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_161, c_2])).
% 2.45/1.39  tff(c_168, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_164])).
% 2.45/1.39  tff(c_169, plain, (![E_64, A_68]: (k1_xboole_0='#skF_4' | k1_funct_1(k5_relat_1('#skF_5', E_64), A_68)=k1_funct_1(E_64, k1_funct_1('#skF_5', A_68)) | ~v1_funct_1(E_64) | ~v1_relat_1(E_64) | ~m1_subset_1(A_68, '#skF_3'))), inference(splitRight, [status(thm)], [c_160])).
% 2.45/1.39  tff(c_200, plain, (![E_74, A_75]: (k1_funct_1(k5_relat_1('#skF_5', E_74), A_75)=k1_funct_1(E_74, k1_funct_1('#skF_5', A_75)) | ~v1_funct_1(E_74) | ~v1_relat_1(E_74) | ~m1_subset_1(A_75, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_192, c_169])).
% 2.45/1.39  tff(c_191, plain, (k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6')=k5_relat_1('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_177])).
% 2.45/1.39  tff(c_18, plain, (k1_funct_1(k8_funct_2('#skF_3', '#skF_4', '#skF_2', '#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_113])).
% 2.45/1.39  tff(c_194, plain, (k1_funct_1(k5_relat_1('#skF_5', '#skF_6'), '#skF_7')!=k1_funct_1('#skF_6', k1_funct_1('#skF_5', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_18])).
% 2.45/1.39  tff(c_206, plain, (~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | ~m1_subset_1('#skF_7', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_200, c_194])).
% 2.45/1.39  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_70, c_28, c_206])).
% 2.45/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.45/1.39  
% 2.45/1.39  Inference rules
% 2.45/1.39  ----------------------
% 2.45/1.39  #Ref     : 0
% 2.45/1.39  #Sup     : 35
% 2.45/1.39  #Fact    : 0
% 2.45/1.39  #Define  : 0
% 2.45/1.39  #Split   : 4
% 2.45/1.39  #Chain   : 0
% 2.45/1.39  #Close   : 0
% 2.45/1.39  
% 2.45/1.39  Ordering : KBO
% 2.45/1.39  
% 2.45/1.39  Simplification rules
% 2.45/1.39  ----------------------
% 2.45/1.39  #Subsume      : 3
% 2.45/1.39  #Demod        : 31
% 2.45/1.39  #Tautology    : 14
% 2.45/1.39  #SimpNegUnit  : 4
% 2.45/1.39  #BackRed      : 12
% 2.45/1.39  
% 2.45/1.39  #Partial instantiations: 0
% 2.45/1.39  #Strategies tried      : 1
% 2.45/1.39  
% 2.45/1.39  Timing (in seconds)
% 2.45/1.39  ----------------------
% 2.45/1.40  Preprocessing        : 0.36
% 2.45/1.40  Parsing              : 0.19
% 2.45/1.40  CNF conversion       : 0.03
% 2.45/1.40  Main loop            : 0.20
% 2.45/1.40  Inferencing          : 0.07
% 2.45/1.40  Reduction            : 0.06
% 2.45/1.40  Demodulation         : 0.04
% 2.45/1.40  BG Simplification    : 0.02
% 2.45/1.40  Subsumption          : 0.04
% 2.45/1.40  Abstraction          : 0.01
% 2.45/1.40  MUC search           : 0.00
% 2.45/1.40  Cooper               : 0.00
% 2.45/1.40  Total                : 0.59
% 2.45/1.40  Index Insertion      : 0.00
% 2.45/1.40  Index Deletion       : 0.00
% 2.45/1.40  Index Matching       : 0.00
% 2.45/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
