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
% DateTime   : Thu Dec  3 10:17:43 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 219 expanded)
%              Number of leaves         :   36 (  94 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 ( 797 expanded)
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

tff(f_131,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_96,axiom,(
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

tff(f_53,axiom,(
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

tff(f_106,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_78,axiom,(
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

tff(c_48,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_36,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_59,plain,(
    ! [C_44,A_45,B_46] :
      ( v1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_67,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_59])).

tff(c_40,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_44,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_42,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_69,plain,(
    ! [A_49,B_50,C_51] :
      ( k1_relset_1(A_49,B_50,C_51) = k1_relat_1(C_51)
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_69])).

tff(c_103,plain,(
    ! [B_62,A_63,C_64] :
      ( k1_xboole_0 = B_62
      | k1_relset_1(A_63,B_62,C_64) = A_63
      | ~ v1_funct_2(C_64,A_63,B_62)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_63,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_106,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_103])).

tff(c_112,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_76,c_106])).

tff(c_116,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_112])).

tff(c_66,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_59])).

tff(c_46,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_127,plain,(
    ! [B_65,C_66,A_67] :
      ( k1_funct_1(k5_relat_1(B_65,C_66),A_67) = k1_funct_1(C_66,k1_funct_1(B_65,A_67))
      | ~ r2_hidden(A_67,k1_relat_1(B_65))
      | ~ v1_funct_1(C_66)
      | ~ v1_relat_1(C_66)
      | ~ v1_funct_1(B_65)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_198,plain,(
    ! [B_82,C_83,A_84] :
      ( k1_funct_1(k5_relat_1(B_82,C_83),A_84) = k1_funct_1(C_83,k1_funct_1(B_82,A_84))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1(B_82)
      | ~ v1_relat_1(B_82)
      | v1_xboole_0(k1_relat_1(B_82))
      | ~ m1_subset_1(A_84,k1_relat_1(B_82)) ) ),
    inference(resolution,[status(thm)],[c_6,c_127])).

tff(c_200,plain,(
    ! [C_83,A_84] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_83),A_84) = k1_funct_1(C_83,k1_funct_1('#skF_4',A_84))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | v1_xboole_0(k1_relat_1('#skF_4'))
      | ~ m1_subset_1(A_84,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_198])).

tff(c_202,plain,(
    ! [C_83,A_84] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_83),A_84) = k1_funct_1(C_83,k1_funct_1('#skF_4',A_84))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_84,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_66,c_46,c_200])).

tff(c_203,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_202])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_49,plain,(
    ! [B_41,A_42] :
      ( ~ v1_xboole_0(B_41)
      | B_41 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_52,plain,(
    ! [A_42] :
      ( k1_xboole_0 = A_42
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_2,c_49])).

tff(c_218,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_203,c_52])).

tff(c_224,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_218])).

tff(c_225,plain,(
    ! [C_83,A_84] :
      ( k1_funct_1(k5_relat_1('#skF_4',C_83),A_84) = k1_funct_1(C_83,k1_funct_1('#skF_4',A_84))
      | ~ v1_funct_1(C_83)
      | ~ v1_relat_1(C_83)
      | ~ m1_subset_1(A_84,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_202])).

tff(c_136,plain,(
    ! [D_73,F_71,C_68,A_72,E_70,B_69] :
      ( k1_partfun1(A_72,B_69,C_68,D_73,E_70,F_71) = k5_relat_1(E_70,F_71)
      | ~ m1_subset_1(F_71,k1_zfmisc_1(k2_zfmisc_1(C_68,D_73)))
      | ~ v1_funct_1(F_71)
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_69)))
      | ~ v1_funct_1(E_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_140,plain,(
    ! [A_72,B_69,E_70] :
      ( k1_partfun1(A_72,B_69,'#skF_3','#skF_1',E_70,'#skF_5') = k5_relat_1(E_70,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_70,k1_zfmisc_1(k2_zfmisc_1(A_72,B_69)))
      | ~ v1_funct_1(E_70) ) ),
    inference(resolution,[status(thm)],[c_38,c_136])).

tff(c_156,plain,(
    ! [A_76,B_77,E_78] :
      ( k1_partfun1(A_76,B_77,'#skF_3','#skF_1',E_78,'#skF_5') = k5_relat_1(E_78,'#skF_5')
      | ~ m1_subset_1(E_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77)))
      | ~ v1_funct_1(E_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_140])).

tff(c_159,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_156])).

tff(c_165,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_159])).

tff(c_77,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_69])).

tff(c_34,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_82,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_34])).

tff(c_244,plain,(
    ! [A_96,C_92,E_95,B_94,D_93] :
      ( k1_partfun1(A_96,B_94,B_94,C_92,D_93,E_95) = k8_funct_2(A_96,B_94,C_92,D_93,E_95)
      | k1_xboole_0 = B_94
      | ~ r1_tarski(k2_relset_1(A_96,B_94,D_93),k1_relset_1(B_94,C_92,E_95))
      | ~ m1_subset_1(E_95,k1_zfmisc_1(k2_zfmisc_1(B_94,C_92)))
      | ~ v1_funct_1(E_95)
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_96,B_94)))
      | ~ v1_funct_2(D_93,A_96,B_94)
      | ~ v1_funct_1(D_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_250,plain,(
    ! [A_96,D_93] :
      ( k1_partfun1(A_96,'#skF_3','#skF_3','#skF_1',D_93,'#skF_5') = k8_funct_2(A_96,'#skF_3','#skF_1',D_93,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_96,'#skF_3',D_93),k1_relat_1('#skF_5'))
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_96,'#skF_3')))
      | ~ v1_funct_2(D_93,A_96,'#skF_3')
      | ~ v1_funct_1(D_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_244])).

tff(c_255,plain,(
    ! [A_96,D_93] :
      ( k1_partfun1(A_96,'#skF_3','#skF_3','#skF_1',D_93,'#skF_5') = k8_funct_2(A_96,'#skF_3','#skF_1',D_93,'#skF_5')
      | k1_xboole_0 = '#skF_3'
      | ~ r1_tarski(k2_relset_1(A_96,'#skF_3',D_93),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_93,k1_zfmisc_1(k2_zfmisc_1(A_96,'#skF_3')))
      | ~ v1_funct_2(D_93,A_96,'#skF_3')
      | ~ v1_funct_1(D_93) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_250])).

tff(c_257,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_266,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_2])).

tff(c_269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_266])).

tff(c_272,plain,(
    ! [A_99,D_100] :
      ( k1_partfun1(A_99,'#skF_3','#skF_3','#skF_1',D_100,'#skF_5') = k8_funct_2(A_99,'#skF_3','#skF_1',D_100,'#skF_5')
      | ~ r1_tarski(k2_relset_1(A_99,'#skF_3',D_100),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(D_100,k1_zfmisc_1(k2_zfmisc_1(A_99,'#skF_3')))
      | ~ v1_funct_2(D_100,A_99,'#skF_3')
      | ~ v1_funct_1(D_100) ) ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_275,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_1','#skF_4','#skF_5') = k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_272])).

tff(c_278,plain,(
    k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_165,c_275])).

tff(c_30,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_279,plain,(
    k1_funct_1(k5_relat_1('#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_30])).

tff(c_286,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_279])).

tff(c_293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_67,c_40,c_286])).

tff(c_294,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_112])).

tff(c_303,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_294,c_2])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_303])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:22:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.90/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.77  
% 3.25/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.25/1.77  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_funct_2 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.25/1.77  
% 3.25/1.77  %Foreground sorts:
% 3.25/1.77  
% 3.25/1.77  
% 3.25/1.77  %Background operators:
% 3.25/1.77  
% 3.25/1.77  
% 3.25/1.77  %Foreground operators:
% 3.25/1.77  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.25/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.77  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.25/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.77  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.77  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.77  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.77  tff('#skF_6', type, '#skF_6': $i).
% 3.25/1.77  tff('#skF_2', type, '#skF_2': $i).
% 3.25/1.77  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.77  tff('#skF_1', type, '#skF_1': $i).
% 3.25/1.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.25/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.77  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.25/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.25/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.77  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.77  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.25/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.77  
% 3.35/1.80  tff(f_131, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 3.35/1.80  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.35/1.80  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.35/1.80  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.35/1.80  tff(f_40, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.35/1.80  tff(f_53, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(B)) => (k1_funct_1(k5_relat_1(B, C), A) = k1_funct_1(C, k1_funct_1(B, A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_funct_1)).
% 3.35/1.80  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.35/1.80  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 3.35/1.80  tff(f_106, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.35/1.80  tff(f_78, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (r1_tarski(k2_relset_1(A, B, D), k1_relset_1(B, C, E)) => ((B = k1_xboole_0) | (k8_funct_2(A, B, C, D, E) = k1_partfun1(A, B, B, C, D, E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_2)).
% 3.35/1.80  tff(c_48, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_36, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_59, plain, (![C_44, A_45, B_46]: (v1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.35/1.80  tff(c_67, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_59])).
% 3.35/1.80  tff(c_40, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_32, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_44, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_42, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_69, plain, (![A_49, B_50, C_51]: (k1_relset_1(A_49, B_50, C_51)=k1_relat_1(C_51) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.35/1.80  tff(c_76, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_69])).
% 3.35/1.80  tff(c_103, plain, (![B_62, A_63, C_64]: (k1_xboole_0=B_62 | k1_relset_1(A_63, B_62, C_64)=A_63 | ~v1_funct_2(C_64, A_63, B_62) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_63, B_62))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.35/1.80  tff(c_106, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_103])).
% 3.35/1.80  tff(c_112, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_76, c_106])).
% 3.35/1.80  tff(c_116, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_112])).
% 3.35/1.80  tff(c_66, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_59])).
% 3.35/1.80  tff(c_46, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.35/1.80  tff(c_127, plain, (![B_65, C_66, A_67]: (k1_funct_1(k5_relat_1(B_65, C_66), A_67)=k1_funct_1(C_66, k1_funct_1(B_65, A_67)) | ~r2_hidden(A_67, k1_relat_1(B_65)) | ~v1_funct_1(C_66) | ~v1_relat_1(C_66) | ~v1_funct_1(B_65) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.35/1.80  tff(c_198, plain, (![B_82, C_83, A_84]: (k1_funct_1(k5_relat_1(B_82, C_83), A_84)=k1_funct_1(C_83, k1_funct_1(B_82, A_84)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1(B_82) | ~v1_relat_1(B_82) | v1_xboole_0(k1_relat_1(B_82)) | ~m1_subset_1(A_84, k1_relat_1(B_82)))), inference(resolution, [status(thm)], [c_6, c_127])).
% 3.35/1.80  tff(c_200, plain, (![C_83, A_84]: (k1_funct_1(k5_relat_1('#skF_4', C_83), A_84)=k1_funct_1(C_83, k1_funct_1('#skF_4', A_84)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | v1_xboole_0(k1_relat_1('#skF_4')) | ~m1_subset_1(A_84, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_198])).
% 3.35/1.80  tff(c_202, plain, (![C_83, A_84]: (k1_funct_1(k5_relat_1('#skF_4', C_83), A_84)=k1_funct_1(C_83, k1_funct_1('#skF_4', A_84)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_84, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_66, c_46, c_200])).
% 3.35/1.80  tff(c_203, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_202])).
% 3.35/1.80  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.35/1.80  tff(c_49, plain, (![B_41, A_42]: (~v1_xboole_0(B_41) | B_41=A_42 | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.35/1.80  tff(c_52, plain, (![A_42]: (k1_xboole_0=A_42 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_2, c_49])).
% 3.35/1.80  tff(c_218, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_203, c_52])).
% 3.35/1.80  tff(c_224, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_218])).
% 3.35/1.80  tff(c_225, plain, (![C_83, A_84]: (k1_funct_1(k5_relat_1('#skF_4', C_83), A_84)=k1_funct_1(C_83, k1_funct_1('#skF_4', A_84)) | ~v1_funct_1(C_83) | ~v1_relat_1(C_83) | ~m1_subset_1(A_84, '#skF_2'))), inference(splitRight, [status(thm)], [c_202])).
% 3.35/1.80  tff(c_136, plain, (![D_73, F_71, C_68, A_72, E_70, B_69]: (k1_partfun1(A_72, B_69, C_68, D_73, E_70, F_71)=k5_relat_1(E_70, F_71) | ~m1_subset_1(F_71, k1_zfmisc_1(k2_zfmisc_1(C_68, D_73))) | ~v1_funct_1(F_71) | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_69))) | ~v1_funct_1(E_70))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.35/1.80  tff(c_140, plain, (![A_72, B_69, E_70]: (k1_partfun1(A_72, B_69, '#skF_3', '#skF_1', E_70, '#skF_5')=k5_relat_1(E_70, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_70, k1_zfmisc_1(k2_zfmisc_1(A_72, B_69))) | ~v1_funct_1(E_70))), inference(resolution, [status(thm)], [c_38, c_136])).
% 3.35/1.80  tff(c_156, plain, (![A_76, B_77, E_78]: (k1_partfun1(A_76, B_77, '#skF_3', '#skF_1', E_78, '#skF_5')=k5_relat_1(E_78, '#skF_5') | ~m1_subset_1(E_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))) | ~v1_funct_1(E_78))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_140])).
% 3.35/1.80  tff(c_159, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_42, c_156])).
% 3.35/1.80  tff(c_165, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_159])).
% 3.35/1.80  tff(c_77, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_69])).
% 3.35/1.80  tff(c_34, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_82, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_34])).
% 3.35/1.80  tff(c_244, plain, (![A_96, C_92, E_95, B_94, D_93]: (k1_partfun1(A_96, B_94, B_94, C_92, D_93, E_95)=k8_funct_2(A_96, B_94, C_92, D_93, E_95) | k1_xboole_0=B_94 | ~r1_tarski(k2_relset_1(A_96, B_94, D_93), k1_relset_1(B_94, C_92, E_95)) | ~m1_subset_1(E_95, k1_zfmisc_1(k2_zfmisc_1(B_94, C_92))) | ~v1_funct_1(E_95) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_96, B_94))) | ~v1_funct_2(D_93, A_96, B_94) | ~v1_funct_1(D_93))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.35/1.80  tff(c_250, plain, (![A_96, D_93]: (k1_partfun1(A_96, '#skF_3', '#skF_3', '#skF_1', D_93, '#skF_5')=k8_funct_2(A_96, '#skF_3', '#skF_1', D_93, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_96, '#skF_3', D_93), k1_relat_1('#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_96, '#skF_3'))) | ~v1_funct_2(D_93, A_96, '#skF_3') | ~v1_funct_1(D_93))), inference(superposition, [status(thm), theory('equality')], [c_77, c_244])).
% 3.35/1.80  tff(c_255, plain, (![A_96, D_93]: (k1_partfun1(A_96, '#skF_3', '#skF_3', '#skF_1', D_93, '#skF_5')=k8_funct_2(A_96, '#skF_3', '#skF_1', D_93, '#skF_5') | k1_xboole_0='#skF_3' | ~r1_tarski(k2_relset_1(A_96, '#skF_3', D_93), k1_relat_1('#skF_5')) | ~m1_subset_1(D_93, k1_zfmisc_1(k2_zfmisc_1(A_96, '#skF_3'))) | ~v1_funct_2(D_93, A_96, '#skF_3') | ~v1_funct_1(D_93))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_250])).
% 3.35/1.80  tff(c_257, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_255])).
% 3.35/1.80  tff(c_266, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_257, c_2])).
% 3.35/1.80  tff(c_269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_266])).
% 3.35/1.80  tff(c_272, plain, (![A_99, D_100]: (k1_partfun1(A_99, '#skF_3', '#skF_3', '#skF_1', D_100, '#skF_5')=k8_funct_2(A_99, '#skF_3', '#skF_1', D_100, '#skF_5') | ~r1_tarski(k2_relset_1(A_99, '#skF_3', D_100), k1_relat_1('#skF_5')) | ~m1_subset_1(D_100, k1_zfmisc_1(k2_zfmisc_1(A_99, '#skF_3'))) | ~v1_funct_2(D_100, A_99, '#skF_3') | ~v1_funct_1(D_100))), inference(splitRight, [status(thm)], [c_255])).
% 3.35/1.80  tff(c_275, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_272])).
% 3.35/1.80  tff(c_278, plain, (k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_165, c_275])).
% 3.35/1.80  tff(c_30, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 3.35/1.80  tff(c_279, plain, (k1_funct_1(k5_relat_1('#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_30])).
% 3.35/1.80  tff(c_286, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_225, c_279])).
% 3.35/1.80  tff(c_293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_67, c_40, c_286])).
% 3.35/1.80  tff(c_294, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_112])).
% 3.35/1.80  tff(c_303, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_294, c_2])).
% 3.35/1.80  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_303])).
% 3.35/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.80  
% 3.35/1.80  Inference rules
% 3.35/1.80  ----------------------
% 3.35/1.80  #Ref     : 0
% 3.35/1.80  #Sup     : 52
% 3.35/1.80  #Fact    : 0
% 3.35/1.80  #Define  : 0
% 3.35/1.80  #Split   : 5
% 3.35/1.80  #Chain   : 0
% 3.35/1.80  #Close   : 0
% 3.35/1.80  
% 3.35/1.80  Ordering : KBO
% 3.35/1.80  
% 3.35/1.80  Simplification rules
% 3.35/1.80  ----------------------
% 3.35/1.80  #Subsume      : 0
% 3.35/1.80  #Demod        : 80
% 3.35/1.80  #Tautology    : 26
% 3.35/1.80  #SimpNegUnit  : 6
% 3.35/1.80  #BackRed      : 22
% 3.35/1.80  
% 3.35/1.80  #Partial instantiations: 0
% 3.35/1.80  #Strategies tried      : 1
% 3.35/1.80  
% 3.35/1.80  Timing (in seconds)
% 3.35/1.80  ----------------------
% 3.35/1.81  Preprocessing        : 0.51
% 3.35/1.81  Parsing              : 0.26
% 3.35/1.81  CNF conversion       : 0.04
% 3.35/1.81  Main loop            : 0.39
% 3.35/1.81  Inferencing          : 0.13
% 3.35/1.81  Reduction            : 0.13
% 3.35/1.81  Demodulation         : 0.09
% 3.35/1.81  BG Simplification    : 0.03
% 3.35/1.81  Subsumption          : 0.07
% 3.35/1.81  Abstraction          : 0.02
% 3.35/1.81  MUC search           : 0.00
% 3.35/1.81  Cooper               : 0.00
% 3.35/1.81  Total                : 0.96
% 3.35/1.81  Index Insertion      : 0.00
% 3.35/1.81  Index Deletion       : 0.00
% 3.35/1.81  Index Matching       : 0.00
% 3.35/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
