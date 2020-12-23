%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:42 EST 2020

% Result     : Theorem 2.83s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 127 expanded)
%              Number of leaves         :   34 (  60 expanded)
%              Depth                    :   10
%              Number of atoms          :  129 ( 393 expanded)
%              Number of equality atoms :   48 ( 145 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,B,D) = B
                & k2_relset_1(B,C,E) = C )
             => ( C = k1_xboole_0
                | k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_607,plain,(
    ! [A_122,B_121,F_123,D_120,E_125,C_124] :
      ( k1_partfun1(A_122,B_121,C_124,D_120,E_125,F_123) = k5_relat_1(E_125,F_123)
      | ~ m1_subset_1(F_123,k1_zfmisc_1(k2_zfmisc_1(C_124,D_120)))
      | ~ v1_funct_1(F_123)
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_1(E_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_612,plain,(
    ! [A_122,B_121,E_125] :
      ( k1_partfun1(A_122,B_121,'#skF_2','#skF_3',E_125,'#skF_5') = k5_relat_1(E_125,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_125,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121)))
      | ~ v1_funct_1(E_125) ) ),
    inference(resolution,[status(thm)],[c_44,c_607])).

tff(c_645,plain,(
    ! [A_131,B_132,E_133] :
      ( k1_partfun1(A_131,B_132,'#skF_2','#skF_3',E_133,'#skF_5') = k5_relat_1(E_133,'#skF_5')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_131,B_132)))
      | ~ v1_funct_1(E_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_612])).

tff(c_655,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_645])).

tff(c_666,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_655])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_674,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_666,c_36])).

tff(c_93,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_109,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_93])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_55,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_74,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,B_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_55,c_74])).

tff(c_40,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_189,plain,(
    ! [A_58,B_59,C_60] :
      ( k2_relset_1(A_58,B_59,C_60) = k2_relat_1(C_60)
      | ~ m1_subset_1(C_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_196,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_189])).

tff(c_206,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_196])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_46,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_130,plain,(
    ! [A_48,B_49,C_50] :
      ( k1_relset_1(A_48,B_49,C_50) = k1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_130])).

tff(c_318,plain,(
    ! [B_83,A_84,C_85] :
      ( k1_xboole_0 = B_83
      | k1_relset_1(A_84,B_83,C_85) = A_84
      | ~ v1_funct_2(C_85,A_84,B_83)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_325,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_318])).

tff(c_336,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_146,c_325])).

tff(c_337,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_336])).

tff(c_110,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_93])).

tff(c_42,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_199,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_189])).

tff(c_208,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_199])).

tff(c_255,plain,(
    ! [B_68,A_69] :
      ( k2_relat_1(k5_relat_1(B_68,A_69)) = k2_relat_1(A_69)
      | ~ r1_tarski(k1_relat_1(A_69),k2_relat_1(B_68))
      | ~ v1_relat_1(B_68)
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_258,plain,(
    ! [A_69] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_69)) = k2_relat_1(A_69)
      | ~ r1_tarski(k1_relat_1(A_69),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_255])).

tff(c_263,plain,(
    ! [A_69] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_69)) = k2_relat_1(A_69)
      | ~ r1_tarski(k1_relat_1(A_69),'#skF_2')
      | ~ v1_relat_1(A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_258])).

tff(c_350,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_263])).

tff(c_359,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_86,c_206,c_350])).

tff(c_697,plain,(
    ! [C_137,E_140,A_141,F_142,B_138,D_139] :
      ( m1_subset_1(k1_partfun1(A_141,B_138,C_137,D_139,E_140,F_142),k1_zfmisc_1(k2_zfmisc_1(A_141,D_139)))
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_137,D_139)))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_141,B_138)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_743,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_697])).

tff(c_762,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_50,c_48,c_44,c_743])).

tff(c_16,plain,(
    ! [A_14,B_15,C_16] :
      ( k2_relset_1(A_14,B_15,C_16) = k2_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_786,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_762,c_16])).

tff(c_818,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_786])).

tff(c_820,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_674,c_818])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:43:06 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.83/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.46  
% 2.83/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.46  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_subset_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.83/1.46  
% 2.83/1.46  %Foreground sorts:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Background operators:
% 2.83/1.46  
% 2.83/1.46  
% 2.83/1.46  %Foreground operators:
% 2.83/1.46  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.83/1.46  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.83/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.83/1.46  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.83/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.83/1.46  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.83/1.46  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.83/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.83/1.46  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.83/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.83/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.83/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.83/1.46  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.83/1.46  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.83/1.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.83/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.83/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.83/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.83/1.46  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.83/1.46  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.83/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.83/1.46  
% 3.16/1.48  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.16/1.48  tff(f_94, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.16/1.48  tff(f_46, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.16/1.48  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.16/1.48  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.16/1.48  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.16/1.48  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.48  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.48  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.16/1.48  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.16/1.48  tff(f_84, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.16/1.48  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_607, plain, (![A_122, B_121, F_123, D_120, E_125, C_124]: (k1_partfun1(A_122, B_121, C_124, D_120, E_125, F_123)=k5_relat_1(E_125, F_123) | ~m1_subset_1(F_123, k1_zfmisc_1(k2_zfmisc_1(C_124, D_120))) | ~v1_funct_1(F_123) | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_1(E_125))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.16/1.48  tff(c_612, plain, (![A_122, B_121, E_125]: (k1_partfun1(A_122, B_121, '#skF_2', '#skF_3', E_125, '#skF_5')=k5_relat_1(E_125, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_125, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))) | ~v1_funct_1(E_125))), inference(resolution, [status(thm)], [c_44, c_607])).
% 3.16/1.48  tff(c_645, plain, (![A_131, B_132, E_133]: (k1_partfun1(A_131, B_132, '#skF_2', '#skF_3', E_133, '#skF_5')=k5_relat_1(E_133, '#skF_5') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_131, B_132))) | ~v1_funct_1(E_133))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_612])).
% 3.16/1.48  tff(c_655, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_645])).
% 3.16/1.48  tff(c_666, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_655])).
% 3.16/1.48  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_674, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_666, c_36])).
% 3.16/1.48  tff(c_93, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.16/1.48  tff(c_109, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_93])).
% 3.16/1.48  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.16/1.48  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.16/1.48  tff(c_55, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.16/1.48  tff(c_74, plain, (![A_35, B_36]: (r1_tarski(A_35, B_36) | ~m1_subset_1(A_35, k1_zfmisc_1(B_36)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.16/1.48  tff(c_86, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_55, c_74])).
% 3.16/1.48  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_189, plain, (![A_58, B_59, C_60]: (k2_relset_1(A_58, B_59, C_60)=k2_relat_1(C_60) | ~m1_subset_1(C_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.48  tff(c_196, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_189])).
% 3.16/1.48  tff(c_206, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_196])).
% 3.16/1.48  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_46, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_130, plain, (![A_48, B_49, C_50]: (k1_relset_1(A_48, B_49, C_50)=k1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.16/1.48  tff(c_146, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_44, c_130])).
% 3.16/1.48  tff(c_318, plain, (![B_83, A_84, C_85]: (k1_xboole_0=B_83 | k1_relset_1(A_84, B_83, C_85)=A_84 | ~v1_funct_2(C_85, A_84, B_83) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.16/1.48  tff(c_325, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_318])).
% 3.16/1.48  tff(c_336, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_146, c_325])).
% 3.16/1.48  tff(c_337, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_38, c_336])).
% 3.16/1.48  tff(c_110, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_93])).
% 3.16/1.48  tff(c_42, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.16/1.48  tff(c_199, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_189])).
% 3.16/1.48  tff(c_208, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_199])).
% 3.16/1.48  tff(c_255, plain, (![B_68, A_69]: (k2_relat_1(k5_relat_1(B_68, A_69))=k2_relat_1(A_69) | ~r1_tarski(k1_relat_1(A_69), k2_relat_1(B_68)) | ~v1_relat_1(B_68) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.16/1.48  tff(c_258, plain, (![A_69]: (k2_relat_1(k5_relat_1('#skF_4', A_69))=k2_relat_1(A_69) | ~r1_tarski(k1_relat_1(A_69), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_69))), inference(superposition, [status(thm), theory('equality')], [c_208, c_255])).
% 3.16/1.48  tff(c_263, plain, (![A_69]: (k2_relat_1(k5_relat_1('#skF_4', A_69))=k2_relat_1(A_69) | ~r1_tarski(k1_relat_1(A_69), '#skF_2') | ~v1_relat_1(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_258])).
% 3.16/1.48  tff(c_350, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_337, c_263])).
% 3.16/1.48  tff(c_359, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_86, c_206, c_350])).
% 3.16/1.48  tff(c_697, plain, (![C_137, E_140, A_141, F_142, B_138, D_139]: (m1_subset_1(k1_partfun1(A_141, B_138, C_137, D_139, E_140, F_142), k1_zfmisc_1(k2_zfmisc_1(A_141, D_139))) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_137, D_139))) | ~v1_funct_1(F_142) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_141, B_138))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.16/1.48  tff(c_743, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_666, c_697])).
% 3.16/1.48  tff(c_762, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_50, c_48, c_44, c_743])).
% 3.16/1.48  tff(c_16, plain, (![A_14, B_15, C_16]: (k2_relset_1(A_14, B_15, C_16)=k2_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.16/1.48  tff(c_786, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_762, c_16])).
% 3.16/1.48  tff(c_818, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_359, c_786])).
% 3.16/1.48  tff(c_820, plain, $false, inference(negUnitSimplification, [status(thm)], [c_674, c_818])).
% 3.16/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.48  
% 3.16/1.48  Inference rules
% 3.16/1.48  ----------------------
% 3.16/1.48  #Ref     : 0
% 3.16/1.48  #Sup     : 158
% 3.16/1.48  #Fact    : 0
% 3.16/1.48  #Define  : 0
% 3.16/1.48  #Split   : 4
% 3.16/1.48  #Chain   : 0
% 3.16/1.48  #Close   : 0
% 3.16/1.48  
% 3.16/1.48  Ordering : KBO
% 3.16/1.48  
% 3.16/1.48  Simplification rules
% 3.16/1.48  ----------------------
% 3.16/1.48  #Subsume      : 12
% 3.16/1.48  #Demod        : 100
% 3.16/1.48  #Tautology    : 61
% 3.16/1.48  #SimpNegUnit  : 7
% 3.16/1.48  #BackRed      : 5
% 3.16/1.48  
% 3.16/1.48  #Partial instantiations: 0
% 3.16/1.48  #Strategies tried      : 1
% 3.16/1.48  
% 3.16/1.48  Timing (in seconds)
% 3.16/1.48  ----------------------
% 3.16/1.48  Preprocessing        : 0.33
% 3.16/1.48  Parsing              : 0.17
% 3.16/1.48  CNF conversion       : 0.02
% 3.16/1.48  Main loop            : 0.36
% 3.16/1.48  Inferencing          : 0.14
% 3.16/1.48  Reduction            : 0.11
% 3.16/1.48  Demodulation         : 0.08
% 3.16/1.48  BG Simplification    : 0.02
% 3.16/1.48  Subsumption          : 0.06
% 3.16/1.48  Abstraction          : 0.02
% 3.16/1.48  MUC search           : 0.00
% 3.16/1.48  Cooper               : 0.00
% 3.16/1.48  Total                : 0.72
% 3.16/1.48  Index Insertion      : 0.00
% 3.16/1.48  Index Deletion       : 0.00
% 3.16/1.48  Index Matching       : 0.00
% 3.16/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
