%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:45 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 147 expanded)
%              Number of leaves         :   34 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  153 ( 588 expanded)
%              Number of equality atoms :   39 ( 127 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_118,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_93,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(f_76,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_66,axiom,(
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

tff(c_24,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_49,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_26,c_49])).

tff(c_61,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_55])).

tff(c_28,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_115,plain,(
    ! [D_63,E_61,A_60,C_62,B_64] :
      ( k1_funct_1(k5_relat_1(D_63,E_61),C_62) = k1_funct_1(E_61,k1_funct_1(D_63,C_62))
      | k1_xboole_0 = B_64
      | ~ r2_hidden(C_62,A_60)
      | ~ v1_funct_1(E_61)
      | ~ v1_relat_1(E_61)
      | ~ m1_subset_1(D_63,k1_zfmisc_1(k2_zfmisc_1(A_60,B_64)))
      | ~ v1_funct_2(D_63,A_60,B_64)
      | ~ v1_funct_1(D_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_119,plain,(
    ! [B_66,D_67,E_65,B_69,A_68] :
      ( k1_funct_1(k5_relat_1(D_67,E_65),A_68) = k1_funct_1(E_65,k1_funct_1(D_67,A_68))
      | k1_xboole_0 = B_66
      | ~ v1_funct_1(E_65)
      | ~ v1_relat_1(E_65)
      | ~ m1_subset_1(D_67,k1_zfmisc_1(k2_zfmisc_1(B_69,B_66)))
      | ~ v1_funct_2(D_67,B_69,B_66)
      | ~ v1_funct_1(D_67)
      | v1_xboole_0(B_69)
      | ~ m1_subset_1(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_121,plain,(
    ! [E_65,A_68] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_65),A_68) = k1_funct_1(E_65,k1_funct_1('#skF_4',A_68))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_65)
      | ~ v1_relat_1(E_65)
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_68,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_119])).

tff(c_126,plain,(
    ! [E_65,A_68] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_65),A_68) = k1_funct_1(E_65,k1_funct_1('#skF_4',A_68))
      | k1_xboole_0 = '#skF_3'
      | ~ v1_funct_1(E_65)
      | ~ v1_relat_1(E_65)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_68,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_121])).

tff(c_131,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_38,plain,(
    ! [B_41,A_42] :
      ( ~ v1_xboole_0(B_41)
      | B_41 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_41,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_38])).

tff(c_134,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_131,c_41])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_134])).

tff(c_141,plain,(
    ! [E_65,A_68] :
      ( k1_xboole_0 = '#skF_3'
      | k1_funct_1(k5_relat_1('#skF_4',E_65),A_68) = k1_funct_1(E_65,k1_funct_1('#skF_4',A_68))
      | ~ v1_funct_1(E_65)
      | ~ v1_relat_1(E_65)
      | ~ m1_subset_1(A_68,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_144,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_141])).

tff(c_148,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_2])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_148])).

tff(c_167,plain,(
    ! [E_75,A_76] :
      ( k1_funct_1(k5_relat_1('#skF_4',E_75),A_76) = k1_funct_1(E_75,k1_funct_1('#skF_4',A_76))
      | ~ v1_funct_1(E_75)
      | ~ v1_relat_1(E_75)
      | ~ m1_subset_1(A_76,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_153,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_141])).

tff(c_62,plain,(
    ! [B_49,E_50,D_52,F_48,C_53,A_51] :
      ( k1_partfun1(A_51,B_49,C_53,D_52,E_50,F_48) = k5_relat_1(E_50,F_48)
      | ~ m1_subset_1(F_48,k1_zfmisc_1(k2_zfmisc_1(C_53,D_52)))
      | ~ v1_funct_1(F_48)
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_49)))
      | ~ v1_funct_1(E_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_66,plain,(
    ! [A_51,B_49,E_50] :
      ( k1_partfun1(A_51,B_49,'#skF_3','#skF_1',E_50,'#skF_5') = k5_relat_1(E_50,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_49)))
      | ~ v1_funct_1(E_50) ) ),
    inference(resolution,[status(thm)],[c_26,c_62])).

tff(c_94,plain,(
    ! [A_57,B_58,E_59] :
      ( k1_partfun1(A_57,B_58,'#skF_3','#skF_1',E_59,'#skF_5') = k5_relat_1(E_59,'#skF_5')
      | ~ m1_subset_1(E_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58)))
      | ~ v1_funct_1(E_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_66])).

tff(c_97,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_94])).

tff(c_103,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_97])).

tff(c_22,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_154,plain,(
    ! [B_70,D_73,C_74,A_72,E_71] :
      ( k1_partfun1(A_72,B_70,B_70,C_74,D_73,E_71) = k8_funct_2(A_72,B_70,C_74,D_73,E_71)
      | k1_xboole_0 = B_70
      | ~ r1_tarski(k2_relset_1(A_72,B_70,D_73),k1_relset_1(B_70,C_74,E_71))
      | ~ m1_subset_1(E_71,k1_zfmisc_1(k2_zfmisc_1(B_70,C_74)))
      | ~ v1_funct_1(E_71)
      | ~ m1_subset_1(D_73,k1_zfmisc_1(k2_zfmisc_1(A_72,B_70)))
      | ~ v1_funct_2(D_73,A_72,B_70)
      | ~ v1_funct_1(D_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_157,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_154])).

tff(c_160,plain,
    ( k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_30,c_28,c_26,c_103,c_157])).

tff(c_161,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_160])).

tff(c_18,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_162,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_18])).

tff(c_173,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_162])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_61,c_28,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.24  
% 2.17/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.25  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.25  
% 2.17/1.25  %Foreground sorts:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Background operators:
% 2.17/1.25  
% 2.17/1.25  
% 2.17/1.25  %Foreground operators:
% 2.17/1.25  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.17/1.25  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.25  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.25  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.17/1.25  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.17/1.25  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.25  tff('#skF_6', type, '#skF_6': $i).
% 2.17/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.25  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.25  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.25  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.25  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.25  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.25  
% 2.17/1.26  tff(f_118, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t185_funct_2)).
% 2.17/1.26  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.26  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.26  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.17/1.26  tff(f_93, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_relat_1(E) & v1_funct_1(E)) => (r2_hidden(C, A) => ((B = k1_xboole_0) | (k1_funct_1(k5_relat_1(D, E), C) = k1_funct_1(E, k1_funct_1(D, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_funct_2)).
% 2.17/1.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.17/1.26  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.17/1.26  tff(f_76, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.17/1.26  tff(f_66, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_2)).
% 2.17/1.26  tff(c_24, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.26  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_49, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.26  tff(c_55, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_26, c_49])).
% 2.17/1.26  tff(c_61, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_55])).
% 2.17/1.26  tff(c_28, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_36, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.26  tff(c_115, plain, (![D_63, E_61, A_60, C_62, B_64]: (k1_funct_1(k5_relat_1(D_63, E_61), C_62)=k1_funct_1(E_61, k1_funct_1(D_63, C_62)) | k1_xboole_0=B_64 | ~r2_hidden(C_62, A_60) | ~v1_funct_1(E_61) | ~v1_relat_1(E_61) | ~m1_subset_1(D_63, k1_zfmisc_1(k2_zfmisc_1(A_60, B_64))) | ~v1_funct_2(D_63, A_60, B_64) | ~v1_funct_1(D_63))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.17/1.26  tff(c_119, plain, (![B_66, D_67, E_65, B_69, A_68]: (k1_funct_1(k5_relat_1(D_67, E_65), A_68)=k1_funct_1(E_65, k1_funct_1(D_67, A_68)) | k1_xboole_0=B_66 | ~v1_funct_1(E_65) | ~v1_relat_1(E_65) | ~m1_subset_1(D_67, k1_zfmisc_1(k2_zfmisc_1(B_69, B_66))) | ~v1_funct_2(D_67, B_69, B_66) | ~v1_funct_1(D_67) | v1_xboole_0(B_69) | ~m1_subset_1(A_68, B_69))), inference(resolution, [status(thm)], [c_6, c_115])).
% 2.17/1.26  tff(c_121, plain, (![E_65, A_68]: (k1_funct_1(k5_relat_1('#skF_4', E_65), A_68)=k1_funct_1(E_65, k1_funct_1('#skF_4', A_68)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_65) | ~v1_relat_1(E_65) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_68, '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_119])).
% 2.17/1.26  tff(c_126, plain, (![E_65, A_68]: (k1_funct_1(k5_relat_1('#skF_4', E_65), A_68)=k1_funct_1(E_65, k1_funct_1('#skF_4', A_68)) | k1_xboole_0='#skF_3' | ~v1_funct_1(E_65) | ~v1_relat_1(E_65) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_68, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_121])).
% 2.17/1.26  tff(c_131, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_126])).
% 2.17/1.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.17/1.26  tff(c_38, plain, (![B_41, A_42]: (~v1_xboole_0(B_41) | B_41=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.26  tff(c_41, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_2, c_38])).
% 2.17/1.26  tff(c_134, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_131, c_41])).
% 2.17/1.26  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_134])).
% 2.17/1.26  tff(c_141, plain, (![E_65, A_68]: (k1_xboole_0='#skF_3' | k1_funct_1(k5_relat_1('#skF_4', E_65), A_68)=k1_funct_1(E_65, k1_funct_1('#skF_4', A_68)) | ~v1_funct_1(E_65) | ~v1_relat_1(E_65) | ~m1_subset_1(A_68, '#skF_2'))), inference(splitRight, [status(thm)], [c_126])).
% 2.17/1.26  tff(c_144, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_141])).
% 2.17/1.26  tff(c_148, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_144, c_2])).
% 2.17/1.26  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_148])).
% 2.17/1.26  tff(c_167, plain, (![E_75, A_76]: (k1_funct_1(k5_relat_1('#skF_4', E_75), A_76)=k1_funct_1(E_75, k1_funct_1('#skF_4', A_76)) | ~v1_funct_1(E_75) | ~v1_relat_1(E_75) | ~m1_subset_1(A_76, '#skF_2'))), inference(splitRight, [status(thm)], [c_141])).
% 2.17/1.26  tff(c_153, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_141])).
% 2.17/1.26  tff(c_62, plain, (![B_49, E_50, D_52, F_48, C_53, A_51]: (k1_partfun1(A_51, B_49, C_53, D_52, E_50, F_48)=k5_relat_1(E_50, F_48) | ~m1_subset_1(F_48, k1_zfmisc_1(k2_zfmisc_1(C_53, D_52))) | ~v1_funct_1(F_48) | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_49))) | ~v1_funct_1(E_50))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.26  tff(c_66, plain, (![A_51, B_49, E_50]: (k1_partfun1(A_51, B_49, '#skF_3', '#skF_1', E_50, '#skF_5')=k5_relat_1(E_50, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_49))) | ~v1_funct_1(E_50))), inference(resolution, [status(thm)], [c_26, c_62])).
% 2.17/1.26  tff(c_94, plain, (![A_57, B_58, E_59]: (k1_partfun1(A_57, B_58, '#skF_3', '#skF_1', E_59, '#skF_5')=k5_relat_1(E_59, '#skF_5') | ~m1_subset_1(E_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))) | ~v1_funct_1(E_59))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_66])).
% 2.17/1.26  tff(c_97, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_94])).
% 2.17/1.26  tff(c_103, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_97])).
% 2.17/1.26  tff(c_22, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_154, plain, (![B_70, D_73, C_74, A_72, E_71]: (k1_partfun1(A_72, B_70, B_70, C_74, D_73, E_71)=k8_funct_2(A_72, B_70, C_74, D_73, E_71) | k1_xboole_0=B_70 | ~r1_tarski(k2_relset_1(A_72, B_70, D_73), k1_relset_1(B_70, C_74, E_71)) | ~m1_subset_1(E_71, k1_zfmisc_1(k2_zfmisc_1(B_70, C_74))) | ~v1_funct_1(E_71) | ~m1_subset_1(D_73, k1_zfmisc_1(k2_zfmisc_1(A_72, B_70))) | ~v1_funct_2(D_73, A_72, B_70) | ~v1_funct_1(D_73))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.26  tff(c_157, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | k1_xboole_0='#skF_3' | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_154])).
% 2.17/1.26  tff(c_160, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_30, c_28, c_26, c_103, c_157])).
% 2.17/1.26  tff(c_161, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_153, c_160])).
% 2.17/1.26  tff(c_18, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.17/1.26  tff(c_162, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_18])).
% 2.17/1.26  tff(c_173, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_167, c_162])).
% 2.17/1.26  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_61, c_28, c_173])).
% 2.17/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  Inference rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Ref     : 0
% 2.17/1.26  #Sup     : 29
% 2.17/1.26  #Fact    : 0
% 2.17/1.26  #Define  : 0
% 2.17/1.26  #Split   : 3
% 2.17/1.26  #Chain   : 0
% 2.17/1.26  #Close   : 0
% 2.17/1.26  
% 2.17/1.26  Ordering : KBO
% 2.17/1.26  
% 2.17/1.26  Simplification rules
% 2.17/1.26  ----------------------
% 2.17/1.26  #Subsume      : 0
% 2.17/1.26  #Demod        : 26
% 2.17/1.26  #Tautology    : 12
% 2.17/1.26  #SimpNegUnit  : 4
% 2.17/1.26  #BackRed      : 6
% 2.17/1.26  
% 2.17/1.26  #Partial instantiations: 0
% 2.17/1.26  #Strategies tried      : 1
% 2.17/1.26  
% 2.17/1.26  Timing (in seconds)
% 2.17/1.26  ----------------------
% 2.17/1.27  Preprocessing        : 0.31
% 2.17/1.27  Parsing              : 0.17
% 2.17/1.27  CNF conversion       : 0.02
% 2.17/1.27  Main loop            : 0.19
% 2.17/1.27  Inferencing          : 0.07
% 2.17/1.27  Reduction            : 0.06
% 2.17/1.27  Demodulation         : 0.04
% 2.17/1.27  BG Simplification    : 0.01
% 2.17/1.27  Subsumption          : 0.03
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.54
% 2.17/1.27  Index Insertion      : 0.00
% 2.17/1.27  Index Deletion       : 0.00
% 2.17/1.27  Index Matching       : 0.00
% 2.17/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
