%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:48 EST 2020

% Result     : Theorem 4.65s
% Output     : CNFRefutation 5.05s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 571 expanded)
%              Number of leaves         :   43 ( 215 expanded)
%              Depth                    :   17
%              Number of atoms          :  277 (2074 expanded)
%              Number of equality atoms :   68 ( 532 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_partfun1,type,(
    k7_partfun1: ( $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_166,negated_conjecture,(
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
                        | k1_funct_1(k8_funct_2(B,C,A,D,E),F) = k7_partfun1(A,E,k1_funct_1(D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t186_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C] :
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
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_82,axiom,(
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

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => k7_partfun1(A,B,C) = k1_funct_1(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_partfun1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_39,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_66,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_54,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_58,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_138,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_146,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_138])).

tff(c_118,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_125,plain,(
    k1_relset_1('#skF_3','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_118])).

tff(c_52,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relset_1('#skF_3','#skF_1','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_128,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_52])).

tff(c_151,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_128])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_1732,plain,(
    ! [E_320,B_322,F_321,C_319,D_318,A_323] :
      ( k1_funct_1(k8_funct_2(B_322,C_319,A_323,D_318,E_320),F_321) = k1_funct_1(E_320,k1_funct_1(D_318,F_321))
      | k1_xboole_0 = B_322
      | ~ r1_tarski(k2_relset_1(B_322,C_319,D_318),k1_relset_1(C_319,A_323,E_320))
      | ~ m1_subset_1(F_321,B_322)
      | ~ m1_subset_1(E_320,k1_zfmisc_1(k2_zfmisc_1(C_319,A_323)))
      | ~ v1_funct_1(E_320)
      | ~ m1_subset_1(D_318,k1_zfmisc_1(k2_zfmisc_1(B_322,C_319)))
      | ~ v1_funct_2(D_318,B_322,C_319)
      | ~ v1_funct_1(D_318)
      | v1_xboole_0(C_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1740,plain,(
    ! [A_323,E_320,F_321] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_323,'#skF_4',E_320),F_321) = k1_funct_1(E_320,k1_funct_1('#skF_4',F_321))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_323,E_320))
      | ~ m1_subset_1(F_321,'#skF_2')
      | ~ m1_subset_1(E_320,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_323)))
      | ~ v1_funct_1(E_320)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_1732])).

tff(c_1753,plain,(
    ! [A_323,E_320,F_321] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_323,'#skF_4',E_320),F_321) = k1_funct_1(E_320,k1_funct_1('#skF_4',F_321))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_323,E_320))
      | ~ m1_subset_1(F_321,'#skF_2')
      | ~ m1_subset_1(E_320,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_323)))
      | ~ v1_funct_1(E_320)
      | v1_xboole_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_1740])).

tff(c_1771,plain,(
    ! [A_324,E_325,F_326] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3',A_324,'#skF_4',E_325),F_326) = k1_funct_1(E_325,k1_funct_1('#skF_4',F_326))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relset_1('#skF_3',A_324,E_325))
      | ~ m1_subset_1(F_326,'#skF_2')
      | ~ m1_subset_1(E_325,k1_zfmisc_1(k2_zfmisc_1('#skF_3',A_324)))
      | ~ v1_funct_1(E_325) ) ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_50,c_1753])).

tff(c_1773,plain,(
    ! [F_326] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_326) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_326))
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1('#skF_5'))
      | ~ m1_subset_1(F_326,'#skF_2')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_1')))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_1771])).

tff(c_1775,plain,(
    ! [F_326] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),F_326) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_326))
      | ~ m1_subset_1(F_326,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_151,c_1773])).

tff(c_91,plain,(
    ! [C_67,B_68,A_69] :
      ( v5_relat_1(C_67,B_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    v5_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_91])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_81,plain,(
    ! [C_62,A_63,B_64] :
      ( v1_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_89,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_81])).

tff(c_126,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_118])).

tff(c_1517,plain,(
    ! [B_285,A_286,C_287] :
      ( k1_xboole_0 = B_285
      | k1_relset_1(A_286,B_285,C_287) = A_286
      | ~ v1_funct_2(C_287,A_286,B_285)
      | ~ m1_subset_1(C_287,k1_zfmisc_1(k2_zfmisc_1(A_286,B_285))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1526,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1517])).

tff(c_1532,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_126,c_1526])).

tff(c_1533,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1532])).

tff(c_42,plain,(
    ! [B_45,A_44] :
      ( v1_funct_2(B_45,k1_relat_1(B_45),A_44)
      | ~ r1_tarski(k2_relat_1(B_45),A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1541,plain,(
    ! [A_44] :
      ( v1_funct_2('#skF_4','#skF_2',A_44)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_44)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_42])).

tff(c_1569,plain,(
    ! [A_291] :
      ( v1_funct_2('#skF_4','#skF_2',A_291)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_64,c_1541])).

tff(c_1573,plain,(
    v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_151,c_1569])).

tff(c_88,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_81])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_1625,plain,(
    ! [A_294,B_295,C_296] :
      ( k7_partfun1(A_294,B_295,C_296) = k1_funct_1(B_295,C_296)
      | ~ r2_hidden(C_296,k1_relat_1(B_295))
      | ~ v1_funct_1(B_295)
      | ~ v5_relat_1(B_295,A_294)
      | ~ v1_relat_1(B_295) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1627,plain,(
    ! [A_294,C_296] :
      ( k7_partfun1(A_294,'#skF_4',C_296) = k1_funct_1('#skF_4',C_296)
      | ~ r2_hidden(C_296,'#skF_2')
      | ~ v1_funct_1('#skF_4')
      | ~ v5_relat_1('#skF_4',A_294)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_1625])).

tff(c_1689,plain,(
    ! [A_308,C_309] :
      ( k7_partfun1(A_308,'#skF_4',C_309) = k1_funct_1('#skF_4',C_309)
      | ~ r2_hidden(C_309,'#skF_2')
      | ~ v5_relat_1('#skF_4',A_308) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_64,c_1627])).

tff(c_1693,plain,(
    ! [A_308,A_2] :
      ( k7_partfun1(A_308,'#skF_4',A_2) = k1_funct_1('#skF_4',A_2)
      | ~ v5_relat_1('#skF_4',A_308)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_2,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_6,c_1689])).

tff(c_1761,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1693])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_1764,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1761,c_4])).

tff(c_1768,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1764])).

tff(c_1770,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1693])).

tff(c_40,plain,(
    ! [B_45,A_44] :
      ( m1_subset_1(B_45,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_45),A_44)))
      | ~ r1_tarski(k2_relat_1(B_45),A_44)
      | ~ v1_funct_1(B_45)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1538,plain,(
    ! [A_44] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_44)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_44)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1533,c_40])).

tff(c_1545,plain,(
    ! [A_44] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_44)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_64,c_1538])).

tff(c_1659,plain,(
    ! [D_300,C_301,B_302,A_303] :
      ( r2_hidden(k1_funct_1(D_300,C_301),B_302)
      | k1_xboole_0 = B_302
      | ~ r2_hidden(C_301,A_303)
      | ~ m1_subset_1(D_300,k1_zfmisc_1(k2_zfmisc_1(A_303,B_302)))
      | ~ v1_funct_2(D_300,A_303,B_302)
      | ~ v1_funct_1(D_300) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1859,plain,(
    ! [D_341,A_342,B_343,B_344] :
      ( r2_hidden(k1_funct_1(D_341,A_342),B_343)
      | k1_xboole_0 = B_343
      | ~ m1_subset_1(D_341,k1_zfmisc_1(k2_zfmisc_1(B_344,B_343)))
      | ~ v1_funct_2(D_341,B_344,B_343)
      | ~ v1_funct_1(D_341)
      | v1_xboole_0(B_344)
      | ~ m1_subset_1(A_342,B_344) ) ),
    inference(resolution,[status(thm)],[c_6,c_1659])).

tff(c_1861,plain,(
    ! [A_342,A_44] :
      ( r2_hidden(k1_funct_1('#skF_4',A_342),A_44)
      | k1_xboole_0 = A_44
      | ~ v1_funct_2('#skF_4','#skF_2',A_44)
      | ~ v1_funct_1('#skF_4')
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_342,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_44) ) ),
    inference(resolution,[status(thm)],[c_1545,c_1859])).

tff(c_1870,plain,(
    ! [A_342,A_44] :
      ( r2_hidden(k1_funct_1('#skF_4',A_342),A_44)
      | k1_xboole_0 = A_44
      | ~ v1_funct_2('#skF_4','#skF_2',A_44)
      | v1_xboole_0('#skF_2')
      | ~ m1_subset_1(A_342,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1861])).

tff(c_1911,plain,(
    ! [A_346,A_347] :
      ( r2_hidden(k1_funct_1('#skF_4',A_346),A_347)
      | k1_xboole_0 = A_347
      | ~ v1_funct_2('#skF_4','#skF_2',A_347)
      | ~ m1_subset_1(A_346,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_347) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1770,c_1870])).

tff(c_36,plain,(
    ! [A_23,B_24,C_26] :
      ( k7_partfun1(A_23,B_24,C_26) = k1_funct_1(B_24,C_26)
      | ~ r2_hidden(C_26,k1_relat_1(B_24))
      | ~ v1_funct_1(B_24)
      | ~ v5_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2034,plain,(
    ! [A_370,B_371,A_372] :
      ( k7_partfun1(A_370,B_371,k1_funct_1('#skF_4',A_372)) = k1_funct_1(B_371,k1_funct_1('#skF_4',A_372))
      | ~ v1_funct_1(B_371)
      | ~ v5_relat_1(B_371,A_370)
      | ~ v1_relat_1(B_371)
      | k1_relat_1(B_371) = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1(B_371))
      | ~ m1_subset_1(A_372,'#skF_2')
      | ~ r1_tarski(k2_relat_1('#skF_4'),k1_relat_1(B_371)) ) ),
    inference(resolution,[status(thm)],[c_1911,c_36])).

tff(c_2038,plain,(
    ! [A_370,A_372] :
      ( k7_partfun1(A_370,'#skF_5',k1_funct_1('#skF_4',A_372)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_372))
      | ~ v1_funct_1('#skF_5')
      | ~ v5_relat_1('#skF_5',A_370)
      | ~ v1_relat_1('#skF_5')
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ v1_funct_2('#skF_4','#skF_2',k1_relat_1('#skF_5'))
      | ~ m1_subset_1(A_372,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_151,c_2034])).

tff(c_2046,plain,(
    ! [A_370,A_372] :
      ( k7_partfun1(A_370,'#skF_5',k1_funct_1('#skF_4',A_372)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_372))
      | ~ v5_relat_1('#skF_5',A_370)
      | k1_relat_1('#skF_5') = k1_xboole_0
      | ~ m1_subset_1(A_372,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1573,c_88,c_58,c_2038])).

tff(c_2049,plain,(
    k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_2046])).

tff(c_1577,plain,(
    ! [A_292] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_292)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_292) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_64,c_1538])).

tff(c_18,plain,(
    ! [C_13,B_11,A_10] :
      ( v1_xboole_0(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(B_11,A_10)))
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1614,plain,(
    ! [A_292] :
      ( v1_xboole_0('#skF_4')
      | ~ v1_xboole_0(A_292)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_292) ) ),
    inference(resolution,[status(thm)],[c_1577,c_18])).

tff(c_1639,plain,(
    ! [A_297] :
      ( ~ v1_xboole_0(A_297)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_297) ) ),
    inference(splitLeft,[status(thm)],[c_1614])).

tff(c_1643,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_151,c_1639])).

tff(c_2056,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2049,c_1643])).

tff(c_2064,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2056])).

tff(c_2067,plain,(
    ! [A_373,A_374] :
      ( k7_partfun1(A_373,'#skF_5',k1_funct_1('#skF_4',A_374)) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',A_374))
      | ~ v5_relat_1('#skF_5',A_373)
      | ~ m1_subset_1(A_374,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_2046])).

tff(c_48,plain,(
    k7_partfun1('#skF_1','#skF_5',k1_funct_1('#skF_4','#skF_6')) != k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_2073,plain,
    ( k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6'))
    | ~ v5_relat_1('#skF_5','#skF_1')
    | ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2067,c_48])).

tff(c_2079,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_3','#skF_1','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_98,c_2073])).

tff(c_2083,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1775,c_2079])).

tff(c_2087,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_2083])).

tff(c_2088,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1614])).

tff(c_2092,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2088,c_4])).

tff(c_2111,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2092,c_50])).

tff(c_10,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2108,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2092,c_2092,c_10])).

tff(c_2119,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2108,c_1533])).

tff(c_2121,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2111,c_2119])).

tff(c_2122,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1532])).

tff(c_2136,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2122,c_2])).

tff(c_2139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_2136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:40:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.65/1.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.92  
% 4.65/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.65/1.92  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k7_partfun1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.65/1.92  
% 4.65/1.92  %Foreground sorts:
% 4.65/1.92  
% 4.65/1.92  
% 4.65/1.92  %Background operators:
% 4.65/1.92  
% 4.65/1.92  
% 4.65/1.92  %Foreground operators:
% 4.65/1.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.65/1.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.65/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.65/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.65/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.65/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.65/1.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.65/1.92  tff(k7_partfun1, type, k7_partfun1: ($i * $i * $i) > $i).
% 4.65/1.92  tff('#skF_5', type, '#skF_5': $i).
% 4.65/1.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.65/1.92  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 4.65/1.92  tff('#skF_6', type, '#skF_6': $i).
% 4.65/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.65/1.92  tff('#skF_3', type, '#skF_3': $i).
% 4.65/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.65/1.92  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.65/1.92  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.65/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.65/1.92  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.65/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.65/1.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.65/1.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.65/1.92  tff('#skF_4', type, '#skF_4': $i).
% 4.65/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.65/1.92  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.65/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.65/1.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.65/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.65/1.92  
% 5.05/1.94  tff(f_166, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k7_partfun1(A, E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t186_funct_2)).
% 5.05/1.94  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.05/1.94  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.05/1.94  tff(f_117, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 5.05/1.94  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.05/1.94  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.05/1.94  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.05/1.94  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.05/1.94  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.05/1.94  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.05/1.94  tff(f_93, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => (k7_partfun1(A, B, C) = k1_funct_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_partfun1)).
% 5.05/1.94  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.05/1.94  tff(f_141, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 5.05/1.94  tff(f_56, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 5.05/1.94  tff(f_39, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.05/1.94  tff(c_66, plain, (~v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_54, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_58, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_138, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.05/1.94  tff(c_146, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_138])).
% 5.05/1.94  tff(c_118, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.05/1.94  tff(c_125, plain, (k1_relset_1('#skF_3', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_118])).
% 5.05/1.94  tff(c_52, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relset_1('#skF_3', '#skF_1', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_128, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_52])).
% 5.05/1.94  tff(c_151, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_128])).
% 5.05/1.94  tff(c_50, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_1732, plain, (![E_320, B_322, F_321, C_319, D_318, A_323]: (k1_funct_1(k8_funct_2(B_322, C_319, A_323, D_318, E_320), F_321)=k1_funct_1(E_320, k1_funct_1(D_318, F_321)) | k1_xboole_0=B_322 | ~r1_tarski(k2_relset_1(B_322, C_319, D_318), k1_relset_1(C_319, A_323, E_320)) | ~m1_subset_1(F_321, B_322) | ~m1_subset_1(E_320, k1_zfmisc_1(k2_zfmisc_1(C_319, A_323))) | ~v1_funct_1(E_320) | ~m1_subset_1(D_318, k1_zfmisc_1(k2_zfmisc_1(B_322, C_319))) | ~v1_funct_2(D_318, B_322, C_319) | ~v1_funct_1(D_318) | v1_xboole_0(C_319))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.05/1.94  tff(c_1740, plain, (![A_323, E_320, F_321]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_323, '#skF_4', E_320), F_321)=k1_funct_1(E_320, k1_funct_1('#skF_4', F_321)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_323, E_320)) | ~m1_subset_1(F_321, '#skF_2') | ~m1_subset_1(E_320, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_323))) | ~v1_funct_1(E_320) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_146, c_1732])).
% 5.05/1.94  tff(c_1753, plain, (![A_323, E_320, F_321]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_323, '#skF_4', E_320), F_321)=k1_funct_1(E_320, k1_funct_1('#skF_4', F_321)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_323, E_320)) | ~m1_subset_1(F_321, '#skF_2') | ~m1_subset_1(E_320, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_323))) | ~v1_funct_1(E_320) | v1_xboole_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_1740])).
% 5.05/1.94  tff(c_1771, plain, (![A_324, E_325, F_326]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', A_324, '#skF_4', E_325), F_326)=k1_funct_1(E_325, k1_funct_1('#skF_4', F_326)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relset_1('#skF_3', A_324, E_325)) | ~m1_subset_1(F_326, '#skF_2') | ~m1_subset_1(E_325, k1_zfmisc_1(k2_zfmisc_1('#skF_3', A_324))) | ~v1_funct_1(E_325))), inference(negUnitSimplification, [status(thm)], [c_66, c_50, c_1753])).
% 5.05/1.94  tff(c_1773, plain, (![F_326]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_326)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_326)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1('#skF_5')) | ~m1_subset_1(F_326, '#skF_2') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_1'))) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_125, c_1771])).
% 5.05/1.94  tff(c_1775, plain, (![F_326]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), F_326)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_326)) | ~m1_subset_1(F_326, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_151, c_1773])).
% 5.05/1.94  tff(c_91, plain, (![C_67, B_68, A_69]: (v5_relat_1(C_67, B_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.05/1.94  tff(c_98, plain, (v5_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_91])).
% 5.05/1.94  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 5.05/1.94  tff(c_81, plain, (![C_62, A_63, B_64]: (v1_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.05/1.94  tff(c_89, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_81])).
% 5.05/1.94  tff(c_126, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_118])).
% 5.05/1.94  tff(c_1517, plain, (![B_285, A_286, C_287]: (k1_xboole_0=B_285 | k1_relset_1(A_286, B_285, C_287)=A_286 | ~v1_funct_2(C_287, A_286, B_285) | ~m1_subset_1(C_287, k1_zfmisc_1(k2_zfmisc_1(A_286, B_285))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.05/1.94  tff(c_1526, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_60, c_1517])).
% 5.05/1.94  tff(c_1532, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_126, c_1526])).
% 5.05/1.94  tff(c_1533, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_1532])).
% 5.05/1.94  tff(c_42, plain, (![B_45, A_44]: (v1_funct_2(B_45, k1_relat_1(B_45), A_44) | ~r1_tarski(k2_relat_1(B_45), A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.05/1.94  tff(c_1541, plain, (![A_44]: (v1_funct_2('#skF_4', '#skF_2', A_44) | ~r1_tarski(k2_relat_1('#skF_4'), A_44) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_42])).
% 5.05/1.94  tff(c_1569, plain, (![A_291]: (v1_funct_2('#skF_4', '#skF_2', A_291) | ~r1_tarski(k2_relat_1('#skF_4'), A_291))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_64, c_1541])).
% 5.05/1.94  tff(c_1573, plain, (v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_151, c_1569])).
% 5.05/1.94  tff(c_88, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_56, c_81])).
% 5.05/1.94  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.05/1.94  tff(c_1625, plain, (![A_294, B_295, C_296]: (k7_partfun1(A_294, B_295, C_296)=k1_funct_1(B_295, C_296) | ~r2_hidden(C_296, k1_relat_1(B_295)) | ~v1_funct_1(B_295) | ~v5_relat_1(B_295, A_294) | ~v1_relat_1(B_295))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.05/1.94  tff(c_1627, plain, (![A_294, C_296]: (k7_partfun1(A_294, '#skF_4', C_296)=k1_funct_1('#skF_4', C_296) | ~r2_hidden(C_296, '#skF_2') | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', A_294) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_1625])).
% 5.05/1.94  tff(c_1689, plain, (![A_308, C_309]: (k7_partfun1(A_308, '#skF_4', C_309)=k1_funct_1('#skF_4', C_309) | ~r2_hidden(C_309, '#skF_2') | ~v5_relat_1('#skF_4', A_308))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_64, c_1627])).
% 5.05/1.94  tff(c_1693, plain, (![A_308, A_2]: (k7_partfun1(A_308, '#skF_4', A_2)=k1_funct_1('#skF_4', A_2) | ~v5_relat_1('#skF_4', A_308) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_2, '#skF_2'))), inference(resolution, [status(thm)], [c_6, c_1689])).
% 5.05/1.94  tff(c_1761, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1693])).
% 5.05/1.94  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.05/1.94  tff(c_1764, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1761, c_4])).
% 5.05/1.94  tff(c_1768, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1764])).
% 5.05/1.94  tff(c_1770, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_1693])).
% 5.05/1.94  tff(c_40, plain, (![B_45, A_44]: (m1_subset_1(B_45, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_45), A_44))) | ~r1_tarski(k2_relat_1(B_45), A_44) | ~v1_funct_1(B_45) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.05/1.94  tff(c_1538, plain, (![A_44]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_44))) | ~r1_tarski(k2_relat_1('#skF_4'), A_44) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1533, c_40])).
% 5.05/1.94  tff(c_1545, plain, (![A_44]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_44))) | ~r1_tarski(k2_relat_1('#skF_4'), A_44))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_64, c_1538])).
% 5.05/1.94  tff(c_1659, plain, (![D_300, C_301, B_302, A_303]: (r2_hidden(k1_funct_1(D_300, C_301), B_302) | k1_xboole_0=B_302 | ~r2_hidden(C_301, A_303) | ~m1_subset_1(D_300, k1_zfmisc_1(k2_zfmisc_1(A_303, B_302))) | ~v1_funct_2(D_300, A_303, B_302) | ~v1_funct_1(D_300))), inference(cnfTransformation, [status(thm)], [f_141])).
% 5.05/1.94  tff(c_1859, plain, (![D_341, A_342, B_343, B_344]: (r2_hidden(k1_funct_1(D_341, A_342), B_343) | k1_xboole_0=B_343 | ~m1_subset_1(D_341, k1_zfmisc_1(k2_zfmisc_1(B_344, B_343))) | ~v1_funct_2(D_341, B_344, B_343) | ~v1_funct_1(D_341) | v1_xboole_0(B_344) | ~m1_subset_1(A_342, B_344))), inference(resolution, [status(thm)], [c_6, c_1659])).
% 5.05/1.94  tff(c_1861, plain, (![A_342, A_44]: (r2_hidden(k1_funct_1('#skF_4', A_342), A_44) | k1_xboole_0=A_44 | ~v1_funct_2('#skF_4', '#skF_2', A_44) | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2') | ~m1_subset_1(A_342, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), A_44))), inference(resolution, [status(thm)], [c_1545, c_1859])).
% 5.05/1.94  tff(c_1870, plain, (![A_342, A_44]: (r2_hidden(k1_funct_1('#skF_4', A_342), A_44) | k1_xboole_0=A_44 | ~v1_funct_2('#skF_4', '#skF_2', A_44) | v1_xboole_0('#skF_2') | ~m1_subset_1(A_342, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), A_44))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1861])).
% 5.05/1.94  tff(c_1911, plain, (![A_346, A_347]: (r2_hidden(k1_funct_1('#skF_4', A_346), A_347) | k1_xboole_0=A_347 | ~v1_funct_2('#skF_4', '#skF_2', A_347) | ~m1_subset_1(A_346, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), A_347))), inference(negUnitSimplification, [status(thm)], [c_1770, c_1870])).
% 5.05/1.94  tff(c_36, plain, (![A_23, B_24, C_26]: (k7_partfun1(A_23, B_24, C_26)=k1_funct_1(B_24, C_26) | ~r2_hidden(C_26, k1_relat_1(B_24)) | ~v1_funct_1(B_24) | ~v5_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_93])).
% 5.05/1.94  tff(c_2034, plain, (![A_370, B_371, A_372]: (k7_partfun1(A_370, B_371, k1_funct_1('#skF_4', A_372))=k1_funct_1(B_371, k1_funct_1('#skF_4', A_372)) | ~v1_funct_1(B_371) | ~v5_relat_1(B_371, A_370) | ~v1_relat_1(B_371) | k1_relat_1(B_371)=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1(B_371)) | ~m1_subset_1(A_372, '#skF_2') | ~r1_tarski(k2_relat_1('#skF_4'), k1_relat_1(B_371)))), inference(resolution, [status(thm)], [c_1911, c_36])).
% 5.05/1.94  tff(c_2038, plain, (![A_370, A_372]: (k7_partfun1(A_370, '#skF_5', k1_funct_1('#skF_4', A_372))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_372)) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', A_370) | ~v1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_funct_2('#skF_4', '#skF_2', k1_relat_1('#skF_5')) | ~m1_subset_1(A_372, '#skF_2'))), inference(resolution, [status(thm)], [c_151, c_2034])).
% 5.05/1.94  tff(c_2046, plain, (![A_370, A_372]: (k7_partfun1(A_370, '#skF_5', k1_funct_1('#skF_4', A_372))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_372)) | ~v5_relat_1('#skF_5', A_370) | k1_relat_1('#skF_5')=k1_xboole_0 | ~m1_subset_1(A_372, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1573, c_88, c_58, c_2038])).
% 5.05/1.94  tff(c_2049, plain, (k1_relat_1('#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_2046])).
% 5.05/1.94  tff(c_1577, plain, (![A_292]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_292))) | ~r1_tarski(k2_relat_1('#skF_4'), A_292))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_64, c_1538])).
% 5.05/1.94  tff(c_18, plain, (![C_13, B_11, A_10]: (v1_xboole_0(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(B_11, A_10))) | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.05/1.94  tff(c_1614, plain, (![A_292]: (v1_xboole_0('#skF_4') | ~v1_xboole_0(A_292) | ~r1_tarski(k2_relat_1('#skF_4'), A_292))), inference(resolution, [status(thm)], [c_1577, c_18])).
% 5.05/1.94  tff(c_1639, plain, (![A_297]: (~v1_xboole_0(A_297) | ~r1_tarski(k2_relat_1('#skF_4'), A_297))), inference(splitLeft, [status(thm)], [c_1614])).
% 5.05/1.94  tff(c_1643, plain, (~v1_xboole_0(k1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_151, c_1639])).
% 5.05/1.94  tff(c_2056, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2049, c_1643])).
% 5.05/1.94  tff(c_2064, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_2056])).
% 5.05/1.94  tff(c_2067, plain, (![A_373, A_374]: (k7_partfun1(A_373, '#skF_5', k1_funct_1('#skF_4', A_374))=k1_funct_1('#skF_5', k1_funct_1('#skF_4', A_374)) | ~v5_relat_1('#skF_5', A_373) | ~m1_subset_1(A_374, '#skF_2'))), inference(splitRight, [status(thm)], [c_2046])).
% 5.05/1.94  tff(c_48, plain, (k7_partfun1('#skF_1', '#skF_5', k1_funct_1('#skF_4', '#skF_6'))!=k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_166])).
% 5.05/1.94  tff(c_2073, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6')) | ~v5_relat_1('#skF_5', '#skF_1') | ~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2067, c_48])).
% 5.05/1.94  tff(c_2079, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_3', '#skF_1', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_98, c_2073])).
% 5.05/1.94  tff(c_2083, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1775, c_2079])).
% 5.05/1.94  tff(c_2087, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_2083])).
% 5.05/1.94  tff(c_2088, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1614])).
% 5.05/1.94  tff(c_2092, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2088, c_4])).
% 5.05/1.94  tff(c_2111, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2092, c_50])).
% 5.05/1.94  tff(c_10, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.05/1.94  tff(c_2108, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2092, c_2092, c_10])).
% 5.05/1.94  tff(c_2119, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2108, c_1533])).
% 5.05/1.94  tff(c_2121, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2111, c_2119])).
% 5.05/1.94  tff(c_2122, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1532])).
% 5.05/1.94  tff(c_2136, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2122, c_2])).
% 5.05/1.94  tff(c_2139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_2136])).
% 5.05/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.05/1.94  
% 5.05/1.94  Inference rules
% 5.05/1.94  ----------------------
% 5.05/1.94  #Ref     : 0
% 5.05/1.94  #Sup     : 390
% 5.05/1.94  #Fact    : 0
% 5.05/1.94  #Define  : 0
% 5.05/1.94  #Split   : 35
% 5.05/1.94  #Chain   : 0
% 5.05/1.94  #Close   : 0
% 5.05/1.94  
% 5.05/1.94  Ordering : KBO
% 5.05/1.94  
% 5.05/1.94  Simplification rules
% 5.05/1.94  ----------------------
% 5.05/1.94  #Subsume      : 107
% 5.05/1.94  #Demod        : 702
% 5.05/1.94  #Tautology    : 103
% 5.05/1.94  #SimpNegUnit  : 84
% 5.05/1.94  #BackRed      : 173
% 5.05/1.94  
% 5.05/1.94  #Partial instantiations: 0
% 5.05/1.94  #Strategies tried      : 1
% 5.05/1.94  
% 5.05/1.94  Timing (in seconds)
% 5.05/1.94  ----------------------
% 5.05/1.94  Preprocessing        : 0.37
% 5.05/1.94  Parsing              : 0.20
% 5.05/1.94  CNF conversion       : 0.03
% 5.05/1.94  Main loop            : 0.73
% 5.05/1.94  Inferencing          : 0.24
% 5.05/1.94  Reduction            : 0.26
% 5.05/1.94  Demodulation         : 0.18
% 5.05/1.94  BG Simplification    : 0.03
% 5.05/1.94  Subsumption          : 0.14
% 5.05/1.94  Abstraction          : 0.04
% 5.05/1.94  MUC search           : 0.00
% 5.05/1.94  Cooper               : 0.00
% 5.05/1.94  Total                : 1.14
% 5.05/1.94  Index Insertion      : 0.00
% 5.05/1.94  Index Deletion       : 0.00
% 5.05/1.94  Index Matching       : 0.00
% 5.05/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
