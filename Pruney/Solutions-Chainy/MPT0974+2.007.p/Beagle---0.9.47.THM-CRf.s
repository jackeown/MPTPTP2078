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
% DateTime   : Thu Dec  3 10:11:42 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 146 expanded)
%              Number of leaves         :   36 (  68 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 456 expanded)
%              Number of equality atoms :   56 ( 174 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_124,negated_conjecture,(
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

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_80,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_92,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(c_58,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_328,plain,(
    ! [C_89,E_88,D_84,F_87,B_85,A_86] :
      ( k1_partfun1(A_86,B_85,C_89,D_84,E_88,F_87) = k5_relat_1(E_88,F_87)
      | ~ m1_subset_1(F_87,k1_zfmisc_1(k2_zfmisc_1(C_89,D_84)))
      | ~ v1_funct_1(F_87)
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85)))
      | ~ v1_funct_1(E_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_330,plain,(
    ! [A_86,B_85,E_88] :
      ( k1_partfun1(A_86,B_85,'#skF_2','#skF_3',E_88,'#skF_5') = k5_relat_1(E_88,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_85)))
      | ~ v1_funct_1(E_88) ) ),
    inference(resolution,[status(thm)],[c_48,c_328])).

tff(c_580,plain,(
    ! [A_104,B_105,E_106] :
      ( k1_partfun1(A_104,B_105,'#skF_2','#skF_3',E_106,'#skF_5') = k5_relat_1(E_106,'#skF_5')
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_1(E_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_330])).

tff(c_595,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_580])).

tff(c_608,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_595])).

tff(c_40,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_684,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_40])).

tff(c_85,plain,(
    ! [C_40,A_41,B_42] :
      ( v1_relat_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_94,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_97,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_94])).

tff(c_102,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_97])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_50,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_8,plain,(
    ! [A_3] :
      ( k10_relat_1(A_3,k2_relat_1(A_3)) = k1_relat_1(A_3)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_108,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_112,plain,(
    k10_relat_1('#skF_5','#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_108])).

tff(c_133,plain,(
    ! [A_49,B_50,C_51,D_52] :
      ( k8_relset_1(A_49,B_50,C_51,D_52) = k10_relat_1(C_51,D_52)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_138,plain,(
    ! [D_52] : k8_relset_1('#skF_2','#skF_3','#skF_5',D_52) = k10_relat_1('#skF_5',D_52) ),
    inference(resolution,[status(thm)],[c_48,c_133])).

tff(c_189,plain,(
    ! [A_64,B_65,C_66] :
      ( k8_relset_1(A_64,B_65,C_66,B_65) = k1_relset_1(A_64,B_65,C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_191,plain,(
    k8_relset_1('#skF_2','#skF_3','#skF_5','#skF_3') = k1_relset_1('#skF_2','#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_189])).

tff(c_195,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_138,c_191])).

tff(c_219,plain,(
    ! [B_72,A_73,C_74] :
      ( k1_xboole_0 = B_72
      | k1_relset_1(A_73,B_72,C_74) = A_73
      | ~ v1_funct_2(C_74,A_73,B_72)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_222,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_48,c_219])).

tff(c_228,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_195,c_222])).

tff(c_229,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_228])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_85])).

tff(c_46,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_100,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_94])).

tff(c_104,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_100])).

tff(c_175,plain,(
    ! [B_58,A_59] :
      ( k2_relat_1(k5_relat_1(B_58,A_59)) = k2_relat_1(A_59)
      | ~ r1_tarski(k1_relat_1(A_59),k2_relat_1(B_58))
      | ~ v1_relat_1(B_58)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_178,plain,(
    ! [A_59] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_59)) = k2_relat_1(A_59)
      | ~ r1_tarski(k1_relat_1(A_59),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_175])).

tff(c_183,plain,(
    ! [A_59] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_59)) = k2_relat_1(A_59)
      | ~ r1_tarski(k1_relat_1(A_59),'#skF_2')
      | ~ v1_relat_1(A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_178])).

tff(c_241,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_183])).

tff(c_250,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_6,c_102,c_241])).

tff(c_34,plain,(
    ! [A_23,B_24,F_28,D_26,C_25,E_27] :
      ( m1_subset_1(k1_partfun1(A_23,B_24,C_25,D_26,E_27,F_28),k1_zfmisc_1(k2_zfmisc_1(A_23,D_26)))
      | ~ m1_subset_1(F_28,k1_zfmisc_1(k2_zfmisc_1(C_25,D_26)))
      | ~ v1_funct_1(F_28)
      | ~ m1_subset_1(E_27,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24)))
      | ~ v1_funct_1(E_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_688,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_608,c_34])).

tff(c_692,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_54,c_52,c_48,c_688])).

tff(c_14,plain,(
    ! [A_10,B_11,C_12] :
      ( k2_relset_1(A_10,B_11,C_12) = k2_relat_1(C_12)
      | ~ m1_subset_1(C_12,k1_zfmisc_1(k2_zfmisc_1(A_10,B_11))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_755,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_692,c_14])).

tff(c_790,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_755])).

tff(c_792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_684,c_790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.48  
% 3.16/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.48  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.16/1.48  
% 3.16/1.48  %Foreground sorts:
% 3.16/1.48  
% 3.16/1.48  
% 3.16/1.48  %Background operators:
% 3.16/1.48  
% 3.16/1.48  
% 3.16/1.48  %Foreground operators:
% 3.16/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.16/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.48  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.16/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.16/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.16/1.48  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.16/1.48  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.16/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.16/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.16/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.16/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.16/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.16/1.48  
% 3.16/1.50  tff(f_124, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_funct_2)).
% 3.16/1.50  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.16/1.50  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.16/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.50  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.50  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.16/1.50  tff(f_56, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.16/1.50  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.16/1.50  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.16/1.50  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_relat_1)).
% 3.16/1.50  tff(f_92, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 3.16/1.50  tff(c_58, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_328, plain, (![C_89, E_88, D_84, F_87, B_85, A_86]: (k1_partfun1(A_86, B_85, C_89, D_84, E_88, F_87)=k5_relat_1(E_88, F_87) | ~m1_subset_1(F_87, k1_zfmisc_1(k2_zfmisc_1(C_89, D_84))) | ~v1_funct_1(F_87) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))) | ~v1_funct_1(E_88))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.16/1.50  tff(c_330, plain, (![A_86, B_85, E_88]: (k1_partfun1(A_86, B_85, '#skF_2', '#skF_3', E_88, '#skF_5')=k5_relat_1(E_88, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_85))) | ~v1_funct_1(E_88))), inference(resolution, [status(thm)], [c_48, c_328])).
% 3.16/1.50  tff(c_580, plain, (![A_104, B_105, E_106]: (k1_partfun1(A_104, B_105, '#skF_2', '#skF_3', E_106, '#skF_5')=k5_relat_1(E_106, '#skF_5') | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_1(E_106))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_330])).
% 3.16/1.50  tff(c_595, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_580])).
% 3.16/1.50  tff(c_608, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_595])).
% 3.16/1.50  tff(c_40, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_684, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_40])).
% 3.16/1.50  tff(c_85, plain, (![C_40, A_41, B_42]: (v1_relat_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.16/1.50  tff(c_92, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_85])).
% 3.16/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.50  tff(c_44, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_94, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.50  tff(c_97, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_48, c_94])).
% 3.16/1.50  tff(c_102, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_97])).
% 3.16/1.50  tff(c_42, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_50, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_8, plain, (![A_3]: (k10_relat_1(A_3, k2_relat_1(A_3))=k1_relat_1(A_3) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.50  tff(c_108, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 3.16/1.50  tff(c_112, plain, (k10_relat_1('#skF_5', '#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_108])).
% 3.16/1.50  tff(c_133, plain, (![A_49, B_50, C_51, D_52]: (k8_relset_1(A_49, B_50, C_51, D_52)=k10_relat_1(C_51, D_52) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.16/1.50  tff(c_138, plain, (![D_52]: (k8_relset_1('#skF_2', '#skF_3', '#skF_5', D_52)=k10_relat_1('#skF_5', D_52))), inference(resolution, [status(thm)], [c_48, c_133])).
% 3.16/1.50  tff(c_189, plain, (![A_64, B_65, C_66]: (k8_relset_1(A_64, B_65, C_66, B_65)=k1_relset_1(A_64, B_65, C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.16/1.50  tff(c_191, plain, (k8_relset_1('#skF_2', '#skF_3', '#skF_5', '#skF_3')=k1_relset_1('#skF_2', '#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_48, c_189])).
% 3.16/1.50  tff(c_195, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_138, c_191])).
% 3.16/1.50  tff(c_219, plain, (![B_72, A_73, C_74]: (k1_xboole_0=B_72 | k1_relset_1(A_73, B_72, C_74)=A_73 | ~v1_funct_2(C_74, A_73, B_72) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.16/1.50  tff(c_222, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_48, c_219])).
% 3.16/1.50  tff(c_228, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_195, c_222])).
% 3.16/1.50  tff(c_229, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_42, c_228])).
% 3.16/1.50  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_85])).
% 3.16/1.50  tff(c_46, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.16/1.50  tff(c_100, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_54, c_94])).
% 3.16/1.50  tff(c_104, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_100])).
% 3.16/1.50  tff(c_175, plain, (![B_58, A_59]: (k2_relat_1(k5_relat_1(B_58, A_59))=k2_relat_1(A_59) | ~r1_tarski(k1_relat_1(A_59), k2_relat_1(B_58)) | ~v1_relat_1(B_58) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.16/1.50  tff(c_178, plain, (![A_59]: (k2_relat_1(k5_relat_1('#skF_4', A_59))=k2_relat_1(A_59) | ~r1_tarski(k1_relat_1(A_59), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_104, c_175])).
% 3.16/1.50  tff(c_183, plain, (![A_59]: (k2_relat_1(k5_relat_1('#skF_4', A_59))=k2_relat_1(A_59) | ~r1_tarski(k1_relat_1(A_59), '#skF_2') | ~v1_relat_1(A_59))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_178])).
% 3.16/1.50  tff(c_241, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_229, c_183])).
% 3.16/1.50  tff(c_250, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_6, c_102, c_241])).
% 3.16/1.50  tff(c_34, plain, (![A_23, B_24, F_28, D_26, C_25, E_27]: (m1_subset_1(k1_partfun1(A_23, B_24, C_25, D_26, E_27, F_28), k1_zfmisc_1(k2_zfmisc_1(A_23, D_26))) | ~m1_subset_1(F_28, k1_zfmisc_1(k2_zfmisc_1(C_25, D_26))) | ~v1_funct_1(F_28) | ~m1_subset_1(E_27, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))) | ~v1_funct_1(E_27))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.16/1.50  tff(c_688, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_608, c_34])).
% 3.16/1.50  tff(c_692, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_54, c_52, c_48, c_688])).
% 3.16/1.50  tff(c_14, plain, (![A_10, B_11, C_12]: (k2_relset_1(A_10, B_11, C_12)=k2_relat_1(C_12) | ~m1_subset_1(C_12, k1_zfmisc_1(k2_zfmisc_1(A_10, B_11))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.16/1.50  tff(c_755, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_692, c_14])).
% 3.16/1.50  tff(c_790, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_755])).
% 3.16/1.50  tff(c_792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_684, c_790])).
% 3.16/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.50  
% 3.16/1.50  Inference rules
% 3.16/1.50  ----------------------
% 3.16/1.50  #Ref     : 0
% 3.16/1.50  #Sup     : 172
% 3.16/1.50  #Fact    : 0
% 3.16/1.50  #Define  : 0
% 3.16/1.50  #Split   : 6
% 3.16/1.50  #Chain   : 0
% 3.16/1.50  #Close   : 0
% 3.16/1.50  
% 3.16/1.50  Ordering : KBO
% 3.16/1.50  
% 3.16/1.50  Simplification rules
% 3.16/1.50  ----------------------
% 3.16/1.50  #Subsume      : 5
% 3.16/1.50  #Demod        : 109
% 3.16/1.50  #Tautology    : 53
% 3.16/1.50  #SimpNegUnit  : 7
% 3.16/1.50  #BackRed      : 9
% 3.16/1.50  
% 3.16/1.50  #Partial instantiations: 0
% 3.16/1.50  #Strategies tried      : 1
% 3.16/1.50  
% 3.16/1.50  Timing (in seconds)
% 3.16/1.50  ----------------------
% 3.16/1.50  Preprocessing        : 0.35
% 3.16/1.50  Parsing              : 0.18
% 3.16/1.50  CNF conversion       : 0.02
% 3.16/1.50  Main loop            : 0.38
% 3.16/1.50  Inferencing          : 0.13
% 3.16/1.50  Reduction            : 0.13
% 3.16/1.50  Demodulation         : 0.09
% 3.16/1.50  BG Simplification    : 0.02
% 3.16/1.50  Subsumption          : 0.07
% 3.16/1.50  Abstraction          : 0.02
% 3.16/1.50  MUC search           : 0.00
% 3.16/1.50  Cooper               : 0.00
% 3.16/1.50  Total                : 0.76
% 3.16/1.50  Index Insertion      : 0.00
% 3.16/1.50  Index Deletion       : 0.00
% 3.16/1.50  Index Matching       : 0.00
% 3.16/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
