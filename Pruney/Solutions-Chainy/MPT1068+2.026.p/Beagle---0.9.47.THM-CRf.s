%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:44 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 228 expanded)
%              Number of leaves         :   37 (  97 expanded)
%              Depth                    :   10
%              Number of atoms          :  185 ( 815 expanded)
%              Number of equality atoms :   51 ( 215 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_136,negated_conjecture,(
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

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_40,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ! [C] :
          ( ( v1_relat_1(C)
            & v1_funct_1(C) )
         => ( r2_hidden(A,k1_relat_1(B))
           => k1_funct_1(k5_relat_1(B,C),A) = k1_funct_1(C,k1_funct_1(B,A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_funct_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_111,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_83,axiom,(
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

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_63,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_40,c_63])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_69])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_77,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_relset_1(A_53,B_54,C_55) = k1_relat_1(C_55)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_84,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_77])).

tff(c_98,plain,(
    ! [B_62,A_63,C_64] :
      ( k1_xboole_0 = B_62
      | k1_relset_1(A_63,B_62,C_64) = A_63
      | ~ v1_funct_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_101,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_98])).

tff(c_107,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_84,c_101])).

tff(c_110,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_66,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_63])).

tff(c_72,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_66])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_135,plain,(
    ! [B_68,C_69,A_70] :
      ( k1_funct_1(k5_relat_1(B_68,C_69),A_70) = k1_funct_1(C_69,k1_funct_1(B_68,A_70))
      | ~ r2_hidden(A_70,k1_relat_1(B_68))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69)
      | ~ v1_funct_1(B_68)
      | ~ v1_relat_1(B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_153,plain,(
    ! [B_73,C_74,A_75] :
      ( k1_funct_1(k5_relat_1(B_73,C_74),A_75) = k1_funct_1(C_74,k1_funct_1(B_73,A_75))
      | ~ v1_funct_1(C_74)
      | ~ v1_relat_1(C_74)
      | ~ v1_funct_1(B_73)
      | ~ v1_relat_1(B_73)
      | v1_xboole_0(k1_relat_1(B_73))
      | ~ m1_subset_1(A_75,k1_relat_1(B_73)) ) ),
    inference(resolution,[status(thm)],[c_6,c_135])).

tff(c_155,plain,(
    ! [C_74,A_75] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_74),A_75) = k1_funct_1(C_74,k1_funct_1('#skF_4',A_75))
      | ~ v1_funct_1(C_74)
      | ~ v1_relat_1(C_74)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_75,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_153])).

tff(c_157,plain,(
    ! [C_74,A_75] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_74),A_75) = k1_funct_1(C_74,k1_funct_1('#skF_4',A_75))
      | ~ v1_funct_1(C_74)
      | ~ v1_relat_1(C_74)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_75,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_72,c_48,c_155])).

tff(c_158,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_52,plain,(
    ! [B_45,A_46] :
      ( ~ v1_xboole_0(B_45)
      | B_45 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_55,plain,(
    ! [A_46] :
      ( k1_xboole_0 = A_46
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_2,c_52])).

tff(c_161,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_158,c_55])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_161])).

tff(c_168,plain,(
    ! [C_74,A_75] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_74),A_75) = k1_funct_1(C_74,k1_funct_1('#skF_4',A_75))
      | ~ v1_funct_1(C_74)
      | ~ v1_relat_1(C_74)
      | ~ m1_subset_1(A_75,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_187,plain,(
    ! [E_83,D_78,B_79,F_81,A_80,C_82] :
      ( k1_partfun1(A_80,B_79,C_82,D_78,E_83,F_81) = k5_relat_1(E_83,F_81)
      | ~ m1_subset_1(F_81,k1_zfmisc_1(k2_zfmisc_1(C_82,D_78)))
      | ~ v1_funct_1(F_81)
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_1(E_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_191,plain,(
    ! [A_80,B_79,E_83] :
      ( k1_partfun1(A_80,B_79,'#skF_3','#skF_1',E_83,'#skF_5') = k5_relat_1(E_83,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_83,k1_zfmisc_1(k2_zfmisc_1(A_80,B_79)))
      | ~ v1_funct_1(E_83) ) ),
    inference(resolution,[status(thm)],[c_40,c_187])).

tff(c_231,plain,(
    ! [A_92,B_93,E_94] :
      ( k1_partfun1(A_92,B_93,'#skF_3','#skF_1',E_94,'#skF_5') = k5_relat_1(E_94,'#skF_5')
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93)))
      | ~ v1_funct_1(E_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_191])).

tff(c_234,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_231])).

tff(c_240,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_234])).

tff(c_85,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_36,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_90,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_36])).

tff(c_215,plain,(
    ! [A_88,E_91,B_89,C_87,D_90] :
      ( k1_partfun1(A_88,B_89,B_89,C_87,D_90,E_91) = k8_funct_2(A_88,B_89,C_87,D_90,E_91)
      | k1_xboole_0 = B_89
      | ~ r1_tarski(k2_relset_1(A_88,B_89,D_90),k1_relset_1(B_89,C_87,E_91))
      | ~ m1_subset_1(E_91,k1_zfmisc_1(k2_zfmisc_1(B_89,C_87)))
      | ~ v1_funct_1(E_91)
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ v1_funct_2(D_90,A_88,B_89)
      | ~ v1_funct_1(D_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_221,plain,(
    ! [A_88,D_90] :
      ( k1_partfun1(A_88,'#skF_3','#skF_3','#skF_1',D_90,'#skF_5') = k8_funct_2(A_88,'#skF_3','#skF_1',D_90,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_88,'#skF_3',D_90),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,'#skF_3')))
      | ~ v1_funct_2(D_90,A_88,'#skF_3')
      | ~ v1_funct_1(D_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_215])).

tff(c_226,plain,(
    ! [A_88,D_90] :
      ( k1_partfun1(A_88,'#skF_3','#skF_3','#skF_1',D_90,'#skF_5') = k8_funct_2(A_88,'#skF_3','#skF_1',D_90,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_88,'#skF_3',D_90),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_90,k1_zfmisc_1(k2_zfmisc_1(A_88,'#skF_3')))
      | ~ v1_funct_2(D_90,A_88,'#skF_3')
      | ~ v1_funct_1(D_90) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_221])).

tff(c_253,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_226])).

tff(c_262,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_2])).

tff(c_265,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_262])).

tff(c_268,plain,(
    ! [A_97,D_98] :
      ( k1_partfun1(A_97,'#skF_3','#skF_3','#skF_1',D_98,'#skF_5') = k8_funct_2(A_97,'#skF_3','#skF_1',D_98,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_97,'#skF_3',D_98),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_97,'#skF_3')))
      | ~ v1_funct_2(D_98,A_97,'#skF_3')
      | ~ v1_funct_1(D_98) ) ),
    inference(splitRight,[status(thm)],[c_226])).

tff(c_271,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_90,c_268])).

tff(c_274,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_240,c_271])).

tff(c_32,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_275,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_32])).

tff(c_282,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_275])).

tff(c_289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_75,c_42,c_282])).

tff(c_290,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_298,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_2])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_298])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:17:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  
% 2.29/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.29/1.31  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.29/1.31  
% 2.29/1.31  %Foreground sorts:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Background operators:
% 2.29/1.31  
% 2.29/1.31  
% 2.29/1.31  %Foreground operators:
% 2.29/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.29/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.29/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.29/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.29/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.29/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.29/1.31  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.29/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.29/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.29/1.31  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 2.29/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.29/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.29/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.29/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.29/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.29/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.29/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.29/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.29/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.29/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.29/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.29/1.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.29/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.29/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.29/1.31  
% 2.69/1.33  tff(f_136, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 2.69/1.33  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.69/1.33  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.69/1.33  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.69/1.33  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.69/1.33  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.69/1.33  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 2.69/1.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.69/1.33  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.69/1.33  tff(f_111, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 2.69/1.33  tff(f_83, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 2.69/1.33  tff(c_50, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.33  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_63, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.69/1.33  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_40, c_63])).
% 2.69/1.33  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_69])).
% 2.69/1.33  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_77, plain, (![A_53, B_54, C_55]: (k1_relset_1(A_53, B_54, C_55)=k1_relat_1(C_55) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.69/1.33  tff(c_84, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_77])).
% 2.69/1.33  tff(c_98, plain, (![B_62, A_63, C_64]: (k1_xboole_0=B_62 | k1_relset_1(A_63, B_62, C_64)=A_63 | ~v1_funct_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.69/1.33  tff(c_101, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_98])).
% 2.69/1.33  tff(c_107, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_84, c_101])).
% 2.69/1.33  tff(c_110, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_107])).
% 2.69/1.33  tff(c_66, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_63])).
% 2.69/1.33  tff(c_72, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_66])).
% 2.69/1.33  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.69/1.33  tff(c_135, plain, (![B_68, C_69, A_70]: (k1_funct_1(k5_relat_1(B_68, C_69), A_70)=k1_funct_1(C_69, k1_funct_1(B_68, A_70)) | ~r2_hidden(A_70, k1_relat_1(B_68)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69) | ~v1_funct_1(B_68) | ~v1_relat_1(B_68))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.69/1.33  tff(c_153, plain, (![B_73, C_74, A_75]: (k1_funct_1(k5_relat_1(B_73, C_74), A_75)=k1_funct_1(C_74, k1_funct_1(B_73, A_75)) | ~v1_funct_1(C_74) | ~v1_relat_1(C_74) | ~v1_funct_1(B_73) | ~v1_relat_1(B_73) | v1_xboole_0(k1_relat_1(B_73)) | ~m1_subset_1(A_75, k1_relat_1(B_73)))), inference(resolution, [status(thm)], [c_6, c_135])).
% 2.69/1.33  tff(c_155, plain, (![C_74, A_75]: (k1_funct_1(k5_relat_1('#skF_4', C_74), A_75)=k1_funct_1(C_74, k1_funct_1('#skF_4', A_75)) | ~v1_funct_1(C_74) | ~v1_relat_1(C_74) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_75, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_153])).
% 2.69/1.33  tff(c_157, plain, (![C_74, A_75]: (k1_funct_1(k5_relat_1('#skF_4', C_74), A_75)=k1_funct_1(C_74, k1_funct_1('#skF_4', A_75)) | ~v1_funct_1(C_74) | ~v1_relat_1(C_74) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_75, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_72, c_48, c_155])).
% 2.69/1.33  tff(c_158, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_157])).
% 2.69/1.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.69/1.33  tff(c_52, plain, (![B_45, A_46]: (~v1_xboole_0(B_45) | B_45=A_46 | ~v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.69/1.33  tff(c_55, plain, (![A_46]: (k1_xboole_0=A_46 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_2, c_52])).
% 2.69/1.33  tff(c_161, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_158, c_55])).
% 2.69/1.33  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_161])).
% 2.69/1.33  tff(c_168, plain, (![C_74, A_75]: (k1_funct_1(k5_relat_1('#skF_4', C_74), A_75)=k1_funct_1(C_74, k1_funct_1('#skF_4', A_75)) | ~v1_funct_1(C_74) | ~v1_relat_1(C_74) | ~m1_subset_1(A_75, '#skF_2'))), inference(splitRight, [status(thm)], [c_157])).
% 2.69/1.33  tff(c_187, plain, (![E_83, D_78, B_79, F_81, A_80, C_82]: (k1_partfun1(A_80, B_79, C_82, D_78, E_83, F_81)=k5_relat_1(E_83, F_81) | ~m1_subset_1(F_81, k1_zfmisc_1(k2_zfmisc_1(C_82, D_78))) | ~v1_funct_1(F_81) | ~m1_subset_1(E_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_1(E_83))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.69/1.33  tff(c_191, plain, (![A_80, B_79, E_83]: (k1_partfun1(A_80, B_79, '#skF_3', '#skF_1', E_83, '#skF_5')=k5_relat_1(E_83, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_83, k1_zfmisc_1(k2_zfmisc_1(A_80, B_79))) | ~v1_funct_1(E_83))), inference(resolution, [status(thm)], [c_40, c_187])).
% 2.69/1.33  tff(c_231, plain, (![A_92, B_93, E_94]: (k1_partfun1(A_92, B_93, '#skF_3', '#skF_1', E_94, '#skF_5')=k5_relat_1(E_94, '#skF_5') | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))) | ~v1_funct_1(E_94))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_191])).
% 2.69/1.33  tff(c_234, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_231])).
% 2.69/1.33  tff(c_240, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_234])).
% 2.69/1.33  tff(c_85, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_77])).
% 2.69/1.33  tff(c_36, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_90, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_36])).
% 2.69/1.33  tff(c_215, plain, (![A_88, E_91, B_89, C_87, D_90]: (k1_partfun1(A_88, B_89, B_89, C_87, D_90, E_91)=k8_funct_2(A_88, B_89, C_87, D_90, E_91) | k1_xboole_0=B_89 | ~r1_tarski(k2_relset_1(A_88, B_89, D_90), k1_relset_1(B_89, C_87, E_91)) | ~m1_subset_1(E_91, k1_zfmisc_1(k2_zfmisc_1(B_89, C_87))) | ~v1_funct_1(E_91) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~v1_funct_2(D_90, A_88, B_89) | ~v1_funct_1(D_90))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.69/1.33  tff(c_221, plain, (![A_88, D_90]: (k1_partfun1(A_88, '#skF_3', '#skF_3', '#skF_1', D_90, '#skF_5')=k8_funct_2(A_88, '#skF_3', '#skF_1', D_90, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_88, '#skF_3', D_90), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, '#skF_3'))) | ~v1_funct_2(D_90, A_88, '#skF_3') | ~v1_funct_1(D_90))), inference(superposition, [status(thm), theory('equality')], [c_85, c_215])).
% 2.69/1.33  tff(c_226, plain, (![A_88, D_90]: (k1_partfun1(A_88, '#skF_3', '#skF_3', '#skF_1', D_90, '#skF_5')=k8_funct_2(A_88, '#skF_3', '#skF_1', D_90, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_88, '#skF_3', D_90), k1_relat_1('#skF_5')) | ~m1_subset_1(D_90, k1_zfmisc_1(k2_zfmisc_1(A_88, '#skF_3'))) | ~v1_funct_2(D_90, A_88, '#skF_3') | ~v1_funct_1(D_90))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_221])).
% 2.69/1.33  tff(c_253, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_226])).
% 2.69/1.33  tff(c_262, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_253, c_2])).
% 2.69/1.33  tff(c_265, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_262])).
% 2.69/1.33  tff(c_268, plain, (![A_97, D_98]: (k1_partfun1(A_97, '#skF_3', '#skF_3', '#skF_1', D_98, '#skF_5')=k8_funct_2(A_97, '#skF_3', '#skF_1', D_98, '#skF_5') | ~r1_tarski(k2_relset_1(A_97, '#skF_3', D_98), k1_relat_1('#skF_5')) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_97, '#skF_3'))) | ~v1_funct_2(D_98, A_97, '#skF_3') | ~v1_funct_1(D_98))), inference(splitRight, [status(thm)], [c_226])).
% 2.69/1.33  tff(c_271, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_90, c_268])).
% 2.69/1.33  tff(c_274, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_240, c_271])).
% 2.69/1.33  tff(c_32, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_136])).
% 2.69/1.33  tff(c_275, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_32])).
% 2.69/1.33  tff(c_282, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_168, c_275])).
% 2.69/1.33  tff(c_289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_75, c_42, c_282])).
% 2.69/1.33  tff(c_290, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_107])).
% 2.69/1.33  tff(c_298, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_290, c_2])).
% 2.69/1.33  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_298])).
% 2.69/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.33  
% 2.69/1.33  Inference rules
% 2.69/1.33  ----------------------
% 2.69/1.33  #Ref     : 0
% 2.69/1.33  #Sup     : 50
% 2.69/1.33  #Fact    : 0
% 2.69/1.33  #Define  : 0
% 2.69/1.33  #Split   : 5
% 2.69/1.33  #Chain   : 0
% 2.69/1.33  #Close   : 0
% 2.69/1.33  
% 2.69/1.33  Ordering : KBO
% 2.69/1.33  
% 2.69/1.33  Simplification rules
% 2.69/1.33  ----------------------
% 2.69/1.33  #Subsume      : 0
% 2.69/1.33  #Demod        : 77
% 2.69/1.33  #Tautology    : 26
% 2.69/1.33  #SimpNegUnit  : 5
% 2.69/1.33  #BackRed      : 21
% 2.69/1.33  
% 2.69/1.33  #Partial instantiations: 0
% 2.69/1.33  #Strategies tried      : 1
% 2.69/1.33  
% 2.69/1.33  Timing (in seconds)
% 2.69/1.33  ----------------------
% 2.69/1.33  Preprocessing        : 0.34
% 2.69/1.33  Parsing              : 0.17
% 2.69/1.33  CNF conversion       : 0.03
% 2.69/1.33  Main loop            : 0.24
% 2.69/1.33  Inferencing          : 0.08
% 2.69/1.33  Reduction            : 0.08
% 2.69/1.33  Demodulation         : 0.06
% 2.69/1.33  BG Simplification    : 0.02
% 2.69/1.33  Subsumption          : 0.04
% 2.69/1.33  Abstraction          : 0.01
% 2.69/1.33  MUC search           : 0.00
% 2.69/1.33  Cooper               : 0.00
% 2.69/1.33  Total                : 0.62
% 2.69/1.33  Index Insertion      : 0.00
% 2.69/1.33  Index Deletion       : 0.00
% 2.69/1.33  Index Matching       : 0.00
% 2.69/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
