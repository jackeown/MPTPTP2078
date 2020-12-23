%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:43 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 3.16s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 143 expanded)
%              Number of leaves         :   37 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  147 ( 412 expanded)
%              Number of equality atoms :   50 ( 146 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_125,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_93,axiom,(
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

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_66,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_69,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_66])).

tff(c_75,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_80,plain,(
    ! [C_48,B_49,A_50] :
      ( v5_relat_1(C_48,B_49)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_50,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_88,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_80])).

tff(c_72,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_52,c_66])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_44,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_121,plain,(
    ! [A_60,B_61,C_62] :
      ( k2_relset_1(A_60,B_61,C_62) = k2_relat_1(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_127,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_121])).

tff(c_131,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_127])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k2_relat_1(B_5),A_4)
      | ~ v5_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_149,plain,(
    ! [A_4] :
      ( r1_tarski('#skF_2',A_4)
      | ~ v5_relat_1('#skF_4',A_4)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_6])).

tff(c_170,plain,(
    ! [A_65] :
      ( r1_tarski('#skF_2',A_65)
      | ~ v5_relat_1('#skF_4',A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_149])).

tff(c_174,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_88,c_170])).

tff(c_42,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_124,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_121])).

tff(c_129,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_124])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_103,plain,(
    ! [A_56,B_57,C_58] :
      ( k1_relset_1(A_56,B_57,C_58) = k1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_56,B_57))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_110,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_46,c_103])).

tff(c_208,plain,(
    ! [B_80,A_81,C_82] :
      ( k1_xboole_0 = B_80
      | k1_relset_1(A_81,B_80,C_82) = A_81
      | ~ v1_funct_2(C_82,A_81,B_80)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_81,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_211,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_208])).

tff(c_217,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_110,c_211])).

tff(c_218,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_217])).

tff(c_183,plain,(
    ! [B_73,A_74] :
      ( k2_relat_1(k5_relat_1(B_73,A_74)) = k2_relat_1(A_74)
      | ~ r1_tarski(k1_relat_1(A_74),k2_relat_1(B_73))
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_186,plain,(
    ! [A_74] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_74)) = k2_relat_1(A_74)
      | ~ r1_tarski(k1_relat_1(A_74),'#skF_2')
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(A_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_183])).

tff(c_191,plain,(
    ! [A_74] :
      ( k2_relat_1(k5_relat_1('#skF_4',A_74)) = k2_relat_1(A_74)
      | ~ r1_tarski(k1_relat_1(A_74),'#skF_2')
      | ~ v1_relat_1(A_74) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_186])).

tff(c_229,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_191])).

tff(c_238,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_174,c_129,c_229])).

tff(c_243,plain,(
    ! [A_85,E_88,F_86,B_84,D_83,C_87] :
      ( k4_relset_1(A_85,B_84,C_87,D_83,E_88,F_86) = k5_relat_1(E_88,F_86)
      | ~ m1_subset_1(F_86,k1_zfmisc_1(k2_zfmisc_1(C_87,D_83)))
      | ~ m1_subset_1(E_88,k1_zfmisc_1(k2_zfmisc_1(A_85,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_468,plain,(
    ! [A_104,B_105,E_106] :
      ( k4_relset_1(A_104,B_105,'#skF_2','#skF_3',E_106,'#skF_5') = k5_relat_1(E_106,'#skF_5')
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(resolution,[status(thm)],[c_46,c_243])).

tff(c_488,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_52,c_468])).

tff(c_16,plain,(
    ! [E_18,C_16,D_17,F_19,A_14,B_15] :
      ( m1_subset_1(k4_relset_1(A_14,B_15,C_16,D_17,E_18,F_19),k1_zfmisc_1(k2_zfmisc_1(A_14,D_17)))
      | ~ m1_subset_1(F_19,k1_zfmisc_1(k2_zfmisc_1(C_16,D_17)))
      | ~ m1_subset_1(E_18,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_578,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_16])).

tff(c_582,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_46,c_578])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25] :
      ( k2_relset_1(A_23,B_24,C_25) = k2_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_605,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_582,c_20])).

tff(c_630,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_605])).

tff(c_56,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_50,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_448,plain,(
    ! [A_98,B_103,C_100,E_101,F_99,D_102] :
      ( k1_partfun1(A_98,B_103,C_100,D_102,E_101,F_99) = k5_relat_1(E_101,F_99)
      | ~ m1_subset_1(F_99,k1_zfmisc_1(k2_zfmisc_1(C_100,D_102)))
      | ~ v1_funct_1(F_99)
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_98,B_103)))
      | ~ v1_funct_1(E_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_456,plain,(
    ! [A_98,B_103,E_101] :
      ( k1_partfun1(A_98,B_103,'#skF_2','#skF_3',E_101,'#skF_5') = k5_relat_1(E_101,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_98,B_103)))
      | ~ v1_funct_1(E_101) ) ),
    inference(resolution,[status(thm)],[c_46,c_448])).

tff(c_646,plain,(
    ! [A_110,B_111,E_112] :
      ( k1_partfun1(A_110,B_111,'#skF_2','#skF_3',E_112,'#skF_5') = k5_relat_1(E_112,'#skF_5')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ v1_funct_1(E_112) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_456])).

tff(c_667,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_646])).

tff(c_678,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_667])).

tff(c_38,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_687,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_678,c_38])).

tff(c_690,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_630,c_687])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.82/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.42  
% 2.82/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/1.43  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.82/1.43  
% 2.82/1.43  %Foreground sorts:
% 2.82/1.43  
% 2.82/1.43  
% 2.82/1.43  %Background operators:
% 2.82/1.43  
% 2.82/1.43  
% 2.82/1.43  %Foreground operators:
% 2.82/1.43  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.82/1.43  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.82/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.82/1.43  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.82/1.43  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.43  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.82/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.82/1.43  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.82/1.43  tff('#skF_5', type, '#skF_5': $i).
% 2.82/1.43  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.82/1.43  tff('#skF_2', type, '#skF_2': $i).
% 2.82/1.43  tff('#skF_3', type, '#skF_3': $i).
% 2.82/1.43  tff('#skF_1', type, '#skF_1': $i).
% 2.82/1.43  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.82/1.43  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.82/1.43  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.82/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.82/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.82/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.82/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.82/1.43  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.82/1.43  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.82/1.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.82/1.43  
% 3.16/1.44  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.16/1.44  tff(f_125, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, B, D) = B) & (k2_relset_1(B, C, E) = C)) => ((C = k1_xboole_0) | (k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_funct_2)).
% 3.16/1.44  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.16/1.44  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.16/1.44  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.16/1.44  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 3.16/1.44  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.16/1.44  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.16/1.44  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 3.16/1.44  tff(f_75, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 3.16/1.44  tff(f_61, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 3.16/1.44  tff(f_103, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 3.16/1.44  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.16/1.44  tff(c_46, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_66, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.16/1.44  tff(c_69, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_66])).
% 3.16/1.44  tff(c_75, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_69])).
% 3.16/1.44  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_80, plain, (![C_48, B_49, A_50]: (v5_relat_1(C_48, B_49) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_50, B_49))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.16/1.44  tff(c_88, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_80])).
% 3.16/1.44  tff(c_72, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_52, c_66])).
% 3.16/1.44  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_72])).
% 3.16/1.44  tff(c_44, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_121, plain, (![A_60, B_61, C_62]: (k2_relset_1(A_60, B_61, C_62)=k2_relat_1(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.44  tff(c_127, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_121])).
% 3.16/1.44  tff(c_131, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_127])).
% 3.16/1.44  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k2_relat_1(B_5), A_4) | ~v5_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.16/1.44  tff(c_149, plain, (![A_4]: (r1_tarski('#skF_2', A_4) | ~v5_relat_1('#skF_4', A_4) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_131, c_6])).
% 3.16/1.44  tff(c_170, plain, (![A_65]: (r1_tarski('#skF_2', A_65) | ~v5_relat_1('#skF_4', A_65))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_149])).
% 3.16/1.44  tff(c_174, plain, (r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_88, c_170])).
% 3.16/1.44  tff(c_42, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_124, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_121])).
% 3.16/1.44  tff(c_129, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_124])).
% 3.16/1.44  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_48, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_103, plain, (![A_56, B_57, C_58]: (k1_relset_1(A_56, B_57, C_58)=k1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_56, B_57))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.16/1.44  tff(c_110, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_46, c_103])).
% 3.16/1.44  tff(c_208, plain, (![B_80, A_81, C_82]: (k1_xboole_0=B_80 | k1_relset_1(A_81, B_80, C_82)=A_81 | ~v1_funct_2(C_82, A_81, B_80) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_81, B_80))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.16/1.44  tff(c_211, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_208])).
% 3.16/1.44  tff(c_217, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_110, c_211])).
% 3.16/1.44  tff(c_218, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_217])).
% 3.16/1.44  tff(c_183, plain, (![B_73, A_74]: (k2_relat_1(k5_relat_1(B_73, A_74))=k2_relat_1(A_74) | ~r1_tarski(k1_relat_1(A_74), k2_relat_1(B_73)) | ~v1_relat_1(B_73) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.16/1.44  tff(c_186, plain, (![A_74]: (k2_relat_1(k5_relat_1('#skF_4', A_74))=k2_relat_1(A_74) | ~r1_tarski(k1_relat_1(A_74), '#skF_2') | ~v1_relat_1('#skF_4') | ~v1_relat_1(A_74))), inference(superposition, [status(thm), theory('equality')], [c_131, c_183])).
% 3.16/1.44  tff(c_191, plain, (![A_74]: (k2_relat_1(k5_relat_1('#skF_4', A_74))=k2_relat_1(A_74) | ~r1_tarski(k1_relat_1(A_74), '#skF_2') | ~v1_relat_1(A_74))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_186])).
% 3.16/1.44  tff(c_229, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_218, c_191])).
% 3.16/1.44  tff(c_238, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_174, c_129, c_229])).
% 3.16/1.44  tff(c_243, plain, (![A_85, E_88, F_86, B_84, D_83, C_87]: (k4_relset_1(A_85, B_84, C_87, D_83, E_88, F_86)=k5_relat_1(E_88, F_86) | ~m1_subset_1(F_86, k1_zfmisc_1(k2_zfmisc_1(C_87, D_83))) | ~m1_subset_1(E_88, k1_zfmisc_1(k2_zfmisc_1(A_85, B_84))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.16/1.44  tff(c_468, plain, (![A_104, B_105, E_106]: (k4_relset_1(A_104, B_105, '#skF_2', '#skF_3', E_106, '#skF_5')=k5_relat_1(E_106, '#skF_5') | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(resolution, [status(thm)], [c_46, c_243])).
% 3.16/1.44  tff(c_488, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_52, c_468])).
% 3.16/1.44  tff(c_16, plain, (![E_18, C_16, D_17, F_19, A_14, B_15]: (m1_subset_1(k4_relset_1(A_14, B_15, C_16, D_17, E_18, F_19), k1_zfmisc_1(k2_zfmisc_1(A_14, D_17))) | ~m1_subset_1(F_19, k1_zfmisc_1(k2_zfmisc_1(C_16, D_17))) | ~m1_subset_1(E_18, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.44  tff(c_578, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_488, c_16])).
% 3.16/1.44  tff(c_582, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_46, c_578])).
% 3.16/1.44  tff(c_20, plain, (![A_23, B_24, C_25]: (k2_relset_1(A_23, B_24, C_25)=k2_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.16/1.44  tff(c_605, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_582, c_20])).
% 3.16/1.44  tff(c_630, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_238, c_605])).
% 3.16/1.44  tff(c_56, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_50, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_448, plain, (![A_98, B_103, C_100, E_101, F_99, D_102]: (k1_partfun1(A_98, B_103, C_100, D_102, E_101, F_99)=k5_relat_1(E_101, F_99) | ~m1_subset_1(F_99, k1_zfmisc_1(k2_zfmisc_1(C_100, D_102))) | ~v1_funct_1(F_99) | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_98, B_103))) | ~v1_funct_1(E_101))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.16/1.44  tff(c_456, plain, (![A_98, B_103, E_101]: (k1_partfun1(A_98, B_103, '#skF_2', '#skF_3', E_101, '#skF_5')=k5_relat_1(E_101, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_98, B_103))) | ~v1_funct_1(E_101))), inference(resolution, [status(thm)], [c_46, c_448])).
% 3.16/1.44  tff(c_646, plain, (![A_110, B_111, E_112]: (k1_partfun1(A_110, B_111, '#skF_2', '#skF_3', E_112, '#skF_5')=k5_relat_1(E_112, '#skF_5') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~v1_funct_1(E_112))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_456])).
% 3.16/1.44  tff(c_667, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_52, c_646])).
% 3.16/1.44  tff(c_678, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_667])).
% 3.16/1.44  tff(c_38, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 3.16/1.44  tff(c_687, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_678, c_38])).
% 3.16/1.44  tff(c_690, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_630, c_687])).
% 3.16/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.44  
% 3.16/1.44  Inference rules
% 3.16/1.44  ----------------------
% 3.16/1.44  #Ref     : 0
% 3.16/1.44  #Sup     : 156
% 3.16/1.44  #Fact    : 0
% 3.16/1.44  #Define  : 0
% 3.16/1.44  #Split   : 5
% 3.16/1.44  #Chain   : 0
% 3.16/1.44  #Close   : 0
% 3.16/1.44  
% 3.16/1.44  Ordering : KBO
% 3.16/1.44  
% 3.16/1.44  Simplification rules
% 3.16/1.44  ----------------------
% 3.16/1.44  #Subsume      : 0
% 3.16/1.44  #Demod        : 55
% 3.16/1.44  #Tautology    : 43
% 3.16/1.44  #SimpNegUnit  : 6
% 3.16/1.44  #BackRed      : 3
% 3.16/1.44  
% 3.16/1.44  #Partial instantiations: 0
% 3.16/1.45  #Strategies tried      : 1
% 3.16/1.45  
% 3.16/1.45  Timing (in seconds)
% 3.16/1.45  ----------------------
% 3.16/1.45  Preprocessing        : 0.33
% 3.16/1.45  Parsing              : 0.17
% 3.16/1.45  CNF conversion       : 0.02
% 3.16/1.45  Main loop            : 0.35
% 3.16/1.45  Inferencing          : 0.13
% 3.16/1.45  Reduction            : 0.11
% 3.16/1.45  Demodulation         : 0.08
% 3.16/1.45  BG Simplification    : 0.02
% 3.16/1.45  Subsumption          : 0.06
% 3.16/1.45  Abstraction          : 0.02
% 3.16/1.45  MUC search           : 0.00
% 3.16/1.45  Cooper               : 0.00
% 3.16/1.45  Total                : 0.73
% 3.16/1.45  Index Insertion      : 0.00
% 3.16/1.45  Index Deletion       : 0.00
% 3.16/1.45  Index Matching       : 0.00
% 3.16/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
