%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:11 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 4.27s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 218 expanded)
%              Number of leaves         :   39 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  228 ( 858 expanded)
%              Number of equality atoms :   38 ( 109 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C,D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,A)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
               => ! [E] :
                    ( ( v1_funct_1(E)
                      & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C))) )
                   => ! [F] :
                        ( m1_subset_1(F,B)
                       => ( v1_partfun1(E,A)
                         => k3_funct_2(B,C,k8_funct_2(B,A,C,D,E),F) = k1_funct_1(E,k3_funct_2(B,A,D,F)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => ( v1_partfun1(B,A)
      <=> k1_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_114,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C,D,E] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
     => ( v1_funct_1(k8_funct_2(A,B,C,D,E))
        & v1_funct_2(k8_funct_2(A,B,C,D,E),A,C)
        & m1_subset_1(k8_funct_2(A,B,C,D,E),k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

tff(f_90,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(c_38,plain,(
    m1_subset_1('#skF_6','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_50,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_191,plain,(
    ! [A_102,B_103,C_104] :
      ( m1_subset_1(k2_relset_1(A_102,B_103,C_104),k1_zfmisc_1(B_103))
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_230,plain,(
    ! [A_108,B_109,C_110] :
      ( r1_tarski(k2_relset_1(A_108,B_109,C_110),B_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109))) ) ),
    inference(resolution,[status(thm)],[c_191,c_4])).

tff(c_243,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_230])).

tff(c_52,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_68,plain,(
    ! [B_80,A_81] :
      ( v1_relat_1(B_80)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81))
      | ~ v1_relat_1(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_77,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_68])).

tff(c_84,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_36,plain,(
    v1_partfun1('#skF_5','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_98,plain,(
    ! [C_84,A_85,B_86] :
      ( v4_relat_1(C_84,A_85)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_111,plain,(
    v4_relat_1('#skF_5','#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_149,plain,(
    ! [B_97,A_98] :
      ( k1_relat_1(B_97) = A_98
      | ~ v1_partfun1(B_97,A_98)
      | ~ v4_relat_1(B_97,A_98)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_152,plain,
    ( k1_relat_1('#skF_5') = '#skF_1'
    | ~ v1_partfun1('#skF_5','#skF_1')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_111,c_149])).

tff(c_158,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_36,c_152])).

tff(c_172,plain,(
    ! [A_99,B_100,C_101] :
      ( k1_relset_1(A_99,B_100,C_101) = k1_relat_1(C_101)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_182,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_172])).

tff(c_186,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_182])).

tff(c_648,plain,(
    ! [B_211,A_209,C_210,D_212,F_213,E_208] :
      ( k1_funct_1(k8_funct_2(B_211,C_210,A_209,D_212,E_208),F_213) = k1_funct_1(E_208,k1_funct_1(D_212,F_213))
      | k1_xboole_0 = B_211
      | ~ r1_tarski(k2_relset_1(B_211,C_210,D_212),k1_relset_1(C_210,A_209,E_208))
      | ~ m1_subset_1(F_213,B_211)
      | ~ m1_subset_1(E_208,k1_zfmisc_1(k2_zfmisc_1(C_210,A_209)))
      | ~ v1_funct_1(E_208)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(B_211,C_210)))
      | ~ v1_funct_2(D_212,B_211,C_210)
      | ~ v1_funct_1(D_212)
      | v1_xboole_0(C_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_652,plain,(
    ! [B_211,D_212,F_213] :
      ( k1_funct_1(k8_funct_2(B_211,'#skF_1','#skF_3',D_212,'#skF_5'),F_213) = k1_funct_1('#skF_5',k1_funct_1(D_212,F_213))
      | k1_xboole_0 = B_211
      | ~ r1_tarski(k2_relset_1(B_211,'#skF_1',D_212),'#skF_1')
      | ~ m1_subset_1(F_213,B_211)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(B_211,'#skF_1')))
      | ~ v1_funct_2(D_212,B_211,'#skF_1')
      | ~ v1_funct_1(D_212)
      | v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_648])).

tff(c_657,plain,(
    ! [B_211,D_212,F_213] :
      ( k1_funct_1(k8_funct_2(B_211,'#skF_1','#skF_3',D_212,'#skF_5'),F_213) = k1_funct_1('#skF_5',k1_funct_1(D_212,F_213))
      | k1_xboole_0 = B_211
      | ~ r1_tarski(k2_relset_1(B_211,'#skF_1',D_212),'#skF_1')
      | ~ m1_subset_1(F_213,B_211)
      | ~ m1_subset_1(D_212,k1_zfmisc_1(k2_zfmisc_1(B_211,'#skF_1')))
      | ~ v1_funct_2(D_212,B_211,'#skF_1')
      | ~ v1_funct_1(D_212)
      | v1_xboole_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_652])).

tff(c_699,plain,(
    ! [B_221,D_222,F_223] :
      ( k1_funct_1(k8_funct_2(B_221,'#skF_1','#skF_3',D_222,'#skF_5'),F_223) = k1_funct_1('#skF_5',k1_funct_1(D_222,F_223))
      | k1_xboole_0 = B_221
      | ~ r1_tarski(k2_relset_1(B_221,'#skF_1',D_222),'#skF_1')
      | ~ m1_subset_1(F_223,B_221)
      | ~ m1_subset_1(D_222,k1_zfmisc_1(k2_zfmisc_1(B_221,'#skF_1')))
      | ~ v1_funct_2(D_222,B_221,'#skF_1')
      | ~ v1_funct_1(D_222) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_657])).

tff(c_710,plain,(
    ! [F_223] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_223) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_223))
      | k1_xboole_0 = '#skF_2'
      | ~ r1_tarski(k2_relset_1('#skF_2','#skF_1','#skF_4'),'#skF_1')
      | ~ m1_subset_1(F_223,'#skF_2')
      | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_699])).

tff(c_716,plain,(
    ! [F_223] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_223) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_223))
      | k1_xboole_0 = '#skF_2'
      | ~ m1_subset_1(F_223,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_243,c_710])).

tff(c_717,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_716])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_720,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_717,c_2])).

tff(c_722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_720])).

tff(c_723,plain,(
    ! [F_223] :
      ( k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),F_223) = k1_funct_1('#skF_5',k1_funct_1('#skF_4',F_223))
      | ~ m1_subset_1(F_223,'#skF_2') ) ),
    inference(splitRight,[status(thm)],[c_716])).

tff(c_363,plain,(
    ! [B_140,A_141,D_142,E_139,C_138] :
      ( v1_funct_1(k8_funct_2(A_141,B_140,C_138,D_142,E_139))
      | ~ m1_subset_1(E_139,k1_zfmisc_1(k2_zfmisc_1(B_140,C_138)))
      | ~ v1_funct_1(E_139)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_141,B_140)))
      | ~ v1_funct_2(D_142,A_141,B_140)
      | ~ v1_funct_1(D_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_373,plain,(
    ! [A_141,D_142] :
      ( v1_funct_1(k8_funct_2(A_141,'#skF_1','#skF_3',D_142,'#skF_5'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_141,'#skF_1')))
      | ~ v1_funct_2(D_142,A_141,'#skF_1')
      | ~ v1_funct_1(D_142) ) ),
    inference(resolution,[status(thm)],[c_40,c_363])).

tff(c_409,plain,(
    ! [A_151,D_152] :
      ( v1_funct_1(k8_funct_2(A_151,'#skF_1','#skF_3',D_152,'#skF_5'))
      | ~ m1_subset_1(D_152,k1_zfmisc_1(k2_zfmisc_1(A_151,'#skF_1')))
      | ~ v1_funct_2(D_152,A_151,'#skF_1')
      | ~ v1_funct_1(D_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_373])).

tff(c_420,plain,
    ( v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_409])).

tff(c_425,plain,(
    v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_420])).

tff(c_473,plain,(
    ! [B_161,C_159,A_162,D_163,E_160] :
      ( v1_funct_2(k8_funct_2(A_162,B_161,C_159,D_163,E_160),A_162,C_159)
      | ~ m1_subset_1(E_160,k1_zfmisc_1(k2_zfmisc_1(B_161,C_159)))
      | ~ v1_funct_1(E_160)
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161)))
      | ~ v1_funct_2(D_163,A_162,B_161)
      | ~ v1_funct_1(D_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_483,plain,(
    ! [A_162,D_163] :
      ( v1_funct_2(k8_funct_2(A_162,'#skF_1','#skF_3',D_163,'#skF_5'),A_162,'#skF_3')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(D_163,k1_zfmisc_1(k2_zfmisc_1(A_162,'#skF_1')))
      | ~ v1_funct_2(D_163,A_162,'#skF_1')
      | ~ v1_funct_1(D_163) ) ),
    inference(resolution,[status(thm)],[c_40,c_473])).

tff(c_530,plain,(
    ! [A_178,D_179] :
      ( v1_funct_2(k8_funct_2(A_178,'#skF_1','#skF_3',D_179,'#skF_5'),A_178,'#skF_3')
      | ~ m1_subset_1(D_179,k1_zfmisc_1(k2_zfmisc_1(A_178,'#skF_1')))
      | ~ v1_funct_2(D_179,A_178,'#skF_1')
      | ~ v1_funct_1(D_179) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_483])).

tff(c_538,plain,
    ( v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_530])).

tff(c_543,plain,(
    v1_funct_2(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_538])).

tff(c_544,plain,(
    ! [D_184,E_181,C_180,A_183,B_182] :
      ( m1_subset_1(k8_funct_2(A_183,B_182,C_180,D_184,E_181),k1_zfmisc_1(k2_zfmisc_1(A_183,C_180)))
      | ~ m1_subset_1(E_181,k1_zfmisc_1(k2_zfmisc_1(B_182,C_180)))
      | ~ v1_funct_1(E_181)
      | ~ m1_subset_1(D_184,k1_zfmisc_1(k2_zfmisc_1(A_183,B_182)))
      | ~ v1_funct_2(D_184,A_183,B_182)
      | ~ v1_funct_1(D_184) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_255,plain,(
    ! [A_111,B_112,C_113,D_114] :
      ( k3_funct_2(A_111,B_112,C_113,D_114) = k1_funct_1(C_113,D_114)
      | ~ m1_subset_1(D_114,A_111)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112)))
      | ~ v1_funct_2(C_113,A_111,B_112)
      | ~ v1_funct_1(C_113)
      | v1_xboole_0(A_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_265,plain,(
    ! [B_112,C_113] :
      ( k3_funct_2('#skF_2',B_112,C_113,'#skF_6') = k1_funct_1(C_113,'#skF_6')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_112)))
      | ~ v1_funct_2(C_113,'#skF_2',B_112)
      | ~ v1_funct_1(C_113)
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_38,c_255])).

tff(c_272,plain,(
    ! [B_112,C_113] :
      ( k3_funct_2('#skF_2',B_112,C_113,'#skF_6') = k1_funct_1(C_113,'#skF_6')
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_112)))
      | ~ v1_funct_2(C_113,'#skF_2',B_112)
      | ~ v1_funct_1(C_113) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_265])).

tff(c_1244,plain,(
    ! [C_352,B_353,D_354,E_355] :
      ( k3_funct_2('#skF_2',C_352,k8_funct_2('#skF_2',B_353,C_352,D_354,E_355),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2',B_353,C_352,D_354,E_355),'#skF_6')
      | ~ v1_funct_2(k8_funct_2('#skF_2',B_353,C_352,D_354,E_355),'#skF_2',C_352)
      | ~ v1_funct_1(k8_funct_2('#skF_2',B_353,C_352,D_354,E_355))
      | ~ m1_subset_1(E_355,k1_zfmisc_1(k2_zfmisc_1(B_353,C_352)))
      | ~ v1_funct_1(E_355)
      | ~ m1_subset_1(D_354,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_353)))
      | ~ v1_funct_2(D_354,'#skF_2',B_353)
      | ~ v1_funct_1(D_354) ) ),
    inference(resolution,[status(thm)],[c_544,c_272])).

tff(c_1254,plain,
    ( k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6')
    | ~ v1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_543,c_1244])).

tff(c_1267,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') = k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_44,c_42,c_40,c_425,c_1254])).

tff(c_326,plain,(
    ! [B_124,C_125] :
      ( k3_funct_2('#skF_2',B_124,C_125,'#skF_6') = k1_funct_1(C_125,'#skF_6')
      | ~ m1_subset_1(C_125,k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_124)))
      | ~ v1_funct_2(C_125,'#skF_2',B_124)
      | ~ v1_funct_1(C_125) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_265])).

tff(c_337,plain,
    ( k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_326])).

tff(c_342,plain,(
    k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6') = k1_funct_1('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_337])).

tff(c_34,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k3_funct_2('#skF_2','#skF_1','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_343,plain,(
    k3_funct_2('#skF_2','#skF_3',k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_34])).

tff(c_1271,plain,(
    k1_funct_1(k8_funct_2('#skF_2','#skF_1','#skF_3','#skF_4','#skF_5'),'#skF_6') != k1_funct_1('#skF_5',k1_funct_1('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1267,c_343])).

tff(c_1278,plain,(
    ~ m1_subset_1('#skF_6','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_723,c_1271])).

tff(c_1282,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.73  
% 3.97/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.97/1.74  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_funct_2 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.97/1.74  
% 3.97/1.74  %Foreground sorts:
% 3.97/1.74  
% 3.97/1.74  
% 3.97/1.74  %Background operators:
% 3.97/1.74  
% 3.97/1.74  
% 3.97/1.74  %Foreground operators:
% 3.97/1.74  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.97/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.97/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.97/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.74  tff('#skF_5', type, '#skF_5': $i).
% 3.97/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.97/1.74  tff(k8_funct_2, type, k8_funct_2: ($i * $i * $i * $i * $i) > $i).
% 3.97/1.74  tff('#skF_6', type, '#skF_6': $i).
% 3.97/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.97/1.74  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.97/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.97/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.97/1.74  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.97/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.97/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.97/1.74  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.97/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.97/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.97/1.74  tff('#skF_4', type, '#skF_4': $i).
% 3.97/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.97/1.74  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.97/1.74  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 3.97/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.97/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.97/1.74  
% 4.27/1.76  tff(f_141, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C)))) => (![F]: (m1_subset_1(F, B) => (v1_partfun1(E, A) => (k3_funct_2(B, C, k8_funct_2(B, A, C, D, E), F) = k1_funct_1(E, k3_funct_2(B, A, D, F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_funct_2)).
% 4.27/1.76  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.27/1.76  tff(f_30, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.27/1.76  tff(f_39, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.27/1.76  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.27/1.76  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.27/1.76  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (v1_partfun1(B, A) <=> (k1_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_partfun1)).
% 4.27/1.76  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.27/1.76  tff(f_114, axiom, (![A, B, C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (![E]: ((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(C, A)))) => (![F]: (m1_subset_1(F, B) => (r1_tarski(k2_relset_1(B, C, D), k1_relset_1(C, A, E)) => ((B = k1_xboole_0) | (k1_funct_1(k8_funct_2(B, C, A, D, E), F) = k1_funct_1(E, k1_funct_1(D, F))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t185_funct_2)).
% 4.27/1.76  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.27/1.76  tff(f_77, axiom, (![A, B, C, D, E]: (((((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(E)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v1_funct_1(k8_funct_2(A, B, C, D, E)) & v1_funct_2(k8_funct_2(A, B, C, D, E), A, C)) & m1_subset_1(k8_funct_2(A, B, C, D, E), k1_zfmisc_1(k2_zfmisc_1(A, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_funct_2)).
% 4.27/1.76  tff(f_90, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.27/1.76  tff(c_38, plain, (m1_subset_1('#skF_6', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_50, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_191, plain, (![A_102, B_103, C_104]: (m1_subset_1(k2_relset_1(A_102, B_103, C_104), k1_zfmisc_1(B_103)) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.27/1.76  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.27/1.76  tff(c_230, plain, (![A_108, B_109, C_110]: (r1_tarski(k2_relset_1(A_108, B_109, C_110), B_109) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))))), inference(resolution, [status(thm)], [c_191, c_4])).
% 4.27/1.76  tff(c_243, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1')), inference(resolution, [status(thm)], [c_44, c_230])).
% 4.27/1.76  tff(c_52, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_40, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.27/1.76  tff(c_68, plain, (![B_80, A_81]: (v1_relat_1(B_80) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)) | ~v1_relat_1(A_81))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.27/1.76  tff(c_77, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_68])).
% 4.27/1.76  tff(c_84, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77])).
% 4.27/1.76  tff(c_36, plain, (v1_partfun1('#skF_5', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_98, plain, (![C_84, A_85, B_86]: (v4_relat_1(C_84, A_85) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.27/1.76  tff(c_111, plain, (v4_relat_1('#skF_5', '#skF_1')), inference(resolution, [status(thm)], [c_40, c_98])).
% 4.27/1.76  tff(c_149, plain, (![B_97, A_98]: (k1_relat_1(B_97)=A_98 | ~v1_partfun1(B_97, A_98) | ~v4_relat_1(B_97, A_98) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.27/1.76  tff(c_152, plain, (k1_relat_1('#skF_5')='#skF_1' | ~v1_partfun1('#skF_5', '#skF_1') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_111, c_149])).
% 4.27/1.76  tff(c_158, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_36, c_152])).
% 4.27/1.76  tff(c_172, plain, (![A_99, B_100, C_101]: (k1_relset_1(A_99, B_100, C_101)=k1_relat_1(C_101) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.27/1.76  tff(c_182, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_40, c_172])).
% 4.27/1.76  tff(c_186, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_158, c_182])).
% 4.27/1.76  tff(c_648, plain, (![B_211, A_209, C_210, D_212, F_213, E_208]: (k1_funct_1(k8_funct_2(B_211, C_210, A_209, D_212, E_208), F_213)=k1_funct_1(E_208, k1_funct_1(D_212, F_213)) | k1_xboole_0=B_211 | ~r1_tarski(k2_relset_1(B_211, C_210, D_212), k1_relset_1(C_210, A_209, E_208)) | ~m1_subset_1(F_213, B_211) | ~m1_subset_1(E_208, k1_zfmisc_1(k2_zfmisc_1(C_210, A_209))) | ~v1_funct_1(E_208) | ~m1_subset_1(D_212, k1_zfmisc_1(k2_zfmisc_1(B_211, C_210))) | ~v1_funct_2(D_212, B_211, C_210) | ~v1_funct_1(D_212) | v1_xboole_0(C_210))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.27/1.76  tff(c_652, plain, (![B_211, D_212, F_213]: (k1_funct_1(k8_funct_2(B_211, '#skF_1', '#skF_3', D_212, '#skF_5'), F_213)=k1_funct_1('#skF_5', k1_funct_1(D_212, F_213)) | k1_xboole_0=B_211 | ~r1_tarski(k2_relset_1(B_211, '#skF_1', D_212), '#skF_1') | ~m1_subset_1(F_213, B_211) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_212, k1_zfmisc_1(k2_zfmisc_1(B_211, '#skF_1'))) | ~v1_funct_2(D_212, B_211, '#skF_1') | ~v1_funct_1(D_212) | v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_186, c_648])).
% 4.27/1.76  tff(c_657, plain, (![B_211, D_212, F_213]: (k1_funct_1(k8_funct_2(B_211, '#skF_1', '#skF_3', D_212, '#skF_5'), F_213)=k1_funct_1('#skF_5', k1_funct_1(D_212, F_213)) | k1_xboole_0=B_211 | ~r1_tarski(k2_relset_1(B_211, '#skF_1', D_212), '#skF_1') | ~m1_subset_1(F_213, B_211) | ~m1_subset_1(D_212, k1_zfmisc_1(k2_zfmisc_1(B_211, '#skF_1'))) | ~v1_funct_2(D_212, B_211, '#skF_1') | ~v1_funct_1(D_212) | v1_xboole_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_652])).
% 4.27/1.76  tff(c_699, plain, (![B_221, D_222, F_223]: (k1_funct_1(k8_funct_2(B_221, '#skF_1', '#skF_3', D_222, '#skF_5'), F_223)=k1_funct_1('#skF_5', k1_funct_1(D_222, F_223)) | k1_xboole_0=B_221 | ~r1_tarski(k2_relset_1(B_221, '#skF_1', D_222), '#skF_1') | ~m1_subset_1(F_223, B_221) | ~m1_subset_1(D_222, k1_zfmisc_1(k2_zfmisc_1(B_221, '#skF_1'))) | ~v1_funct_2(D_222, B_221, '#skF_1') | ~v1_funct_1(D_222))), inference(negUnitSimplification, [status(thm)], [c_52, c_657])).
% 4.27/1.76  tff(c_710, plain, (![F_223]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_223)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_223)) | k1_xboole_0='#skF_2' | ~r1_tarski(k2_relset_1('#skF_2', '#skF_1', '#skF_4'), '#skF_1') | ~m1_subset_1(F_223, '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_699])).
% 4.27/1.76  tff(c_716, plain, (![F_223]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_223)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_223)) | k1_xboole_0='#skF_2' | ~m1_subset_1(F_223, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_243, c_710])).
% 4.27/1.76  tff(c_717, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_716])).
% 4.27/1.76  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.27/1.76  tff(c_720, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_717, c_2])).
% 4.27/1.76  tff(c_722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_720])).
% 4.27/1.76  tff(c_723, plain, (![F_223]: (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), F_223)=k1_funct_1('#skF_5', k1_funct_1('#skF_4', F_223)) | ~m1_subset_1(F_223, '#skF_2'))), inference(splitRight, [status(thm)], [c_716])).
% 4.27/1.76  tff(c_363, plain, (![B_140, A_141, D_142, E_139, C_138]: (v1_funct_1(k8_funct_2(A_141, B_140, C_138, D_142, E_139)) | ~m1_subset_1(E_139, k1_zfmisc_1(k2_zfmisc_1(B_140, C_138))) | ~v1_funct_1(E_139) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_141, B_140))) | ~v1_funct_2(D_142, A_141, B_140) | ~v1_funct_1(D_142))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.27/1.76  tff(c_373, plain, (![A_141, D_142]: (v1_funct_1(k8_funct_2(A_141, '#skF_1', '#skF_3', D_142, '#skF_5')) | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_141, '#skF_1'))) | ~v1_funct_2(D_142, A_141, '#skF_1') | ~v1_funct_1(D_142))), inference(resolution, [status(thm)], [c_40, c_363])).
% 4.27/1.76  tff(c_409, plain, (![A_151, D_152]: (v1_funct_1(k8_funct_2(A_151, '#skF_1', '#skF_3', D_152, '#skF_5')) | ~m1_subset_1(D_152, k1_zfmisc_1(k2_zfmisc_1(A_151, '#skF_1'))) | ~v1_funct_2(D_152, A_151, '#skF_1') | ~v1_funct_1(D_152))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_373])).
% 4.27/1.76  tff(c_420, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_409])).
% 4.27/1.76  tff(c_425, plain, (v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_420])).
% 4.27/1.76  tff(c_473, plain, (![B_161, C_159, A_162, D_163, E_160]: (v1_funct_2(k8_funct_2(A_162, B_161, C_159, D_163, E_160), A_162, C_159) | ~m1_subset_1(E_160, k1_zfmisc_1(k2_zfmisc_1(B_161, C_159))) | ~v1_funct_1(E_160) | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))) | ~v1_funct_2(D_163, A_162, B_161) | ~v1_funct_1(D_163))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.27/1.76  tff(c_483, plain, (![A_162, D_163]: (v1_funct_2(k8_funct_2(A_162, '#skF_1', '#skF_3', D_163, '#skF_5'), A_162, '#skF_3') | ~v1_funct_1('#skF_5') | ~m1_subset_1(D_163, k1_zfmisc_1(k2_zfmisc_1(A_162, '#skF_1'))) | ~v1_funct_2(D_163, A_162, '#skF_1') | ~v1_funct_1(D_163))), inference(resolution, [status(thm)], [c_40, c_473])).
% 4.27/1.76  tff(c_530, plain, (![A_178, D_179]: (v1_funct_2(k8_funct_2(A_178, '#skF_1', '#skF_3', D_179, '#skF_5'), A_178, '#skF_3') | ~m1_subset_1(D_179, k1_zfmisc_1(k2_zfmisc_1(A_178, '#skF_1'))) | ~v1_funct_2(D_179, A_178, '#skF_1') | ~v1_funct_1(D_179))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_483])).
% 4.27/1.76  tff(c_538, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_530])).
% 4.27/1.76  tff(c_543, plain, (v1_funct_2(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_538])).
% 4.27/1.76  tff(c_544, plain, (![D_184, E_181, C_180, A_183, B_182]: (m1_subset_1(k8_funct_2(A_183, B_182, C_180, D_184, E_181), k1_zfmisc_1(k2_zfmisc_1(A_183, C_180))) | ~m1_subset_1(E_181, k1_zfmisc_1(k2_zfmisc_1(B_182, C_180))) | ~v1_funct_1(E_181) | ~m1_subset_1(D_184, k1_zfmisc_1(k2_zfmisc_1(A_183, B_182))) | ~v1_funct_2(D_184, A_183, B_182) | ~v1_funct_1(D_184))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.27/1.76  tff(c_255, plain, (![A_111, B_112, C_113, D_114]: (k3_funct_2(A_111, B_112, C_113, D_114)=k1_funct_1(C_113, D_114) | ~m1_subset_1(D_114, A_111) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))) | ~v1_funct_2(C_113, A_111, B_112) | ~v1_funct_1(C_113) | v1_xboole_0(A_111))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.27/1.76  tff(c_265, plain, (![B_112, C_113]: (k3_funct_2('#skF_2', B_112, C_113, '#skF_6')=k1_funct_1(C_113, '#skF_6') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_112))) | ~v1_funct_2(C_113, '#skF_2', B_112) | ~v1_funct_1(C_113) | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_255])).
% 4.27/1.76  tff(c_272, plain, (![B_112, C_113]: (k3_funct_2('#skF_2', B_112, C_113, '#skF_6')=k1_funct_1(C_113, '#skF_6') | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_112))) | ~v1_funct_2(C_113, '#skF_2', B_112) | ~v1_funct_1(C_113))), inference(negUnitSimplification, [status(thm)], [c_50, c_265])).
% 4.27/1.76  tff(c_1244, plain, (![C_352, B_353, D_354, E_355]: (k3_funct_2('#skF_2', C_352, k8_funct_2('#skF_2', B_353, C_352, D_354, E_355), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', B_353, C_352, D_354, E_355), '#skF_6') | ~v1_funct_2(k8_funct_2('#skF_2', B_353, C_352, D_354, E_355), '#skF_2', C_352) | ~v1_funct_1(k8_funct_2('#skF_2', B_353, C_352, D_354, E_355)) | ~m1_subset_1(E_355, k1_zfmisc_1(k2_zfmisc_1(B_353, C_352))) | ~v1_funct_1(E_355) | ~m1_subset_1(D_354, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_353))) | ~v1_funct_2(D_354, '#skF_2', B_353) | ~v1_funct_1(D_354))), inference(resolution, [status(thm)], [c_544, c_272])).
% 4.27/1.76  tff(c_1254, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6') | ~v1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_543, c_1244])).
% 4.27/1.76  tff(c_1267, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')=k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_44, c_42, c_40, c_425, c_1254])).
% 4.27/1.76  tff(c_326, plain, (![B_124, C_125]: (k3_funct_2('#skF_2', B_124, C_125, '#skF_6')=k1_funct_1(C_125, '#skF_6') | ~m1_subset_1(C_125, k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_124))) | ~v1_funct_2(C_125, '#skF_2', B_124) | ~v1_funct_1(C_125))), inference(negUnitSimplification, [status(thm)], [c_50, c_265])).
% 4.27/1.76  tff(c_337, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_326])).
% 4.27/1.76  tff(c_342, plain, (k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6')=k1_funct_1('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_337])).
% 4.27/1.76  tff(c_34, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k3_funct_2('#skF_2', '#skF_1', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.27/1.76  tff(c_343, plain, (k3_funct_2('#skF_2', '#skF_3', k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_34])).
% 4.27/1.76  tff(c_1271, plain, (k1_funct_1(k8_funct_2('#skF_2', '#skF_1', '#skF_3', '#skF_4', '#skF_5'), '#skF_6')!=k1_funct_1('#skF_5', k1_funct_1('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_1267, c_343])).
% 4.27/1.76  tff(c_1278, plain, (~m1_subset_1('#skF_6', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_723, c_1271])).
% 4.27/1.76  tff(c_1282, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1278])).
% 4.27/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.27/1.76  
% 4.27/1.76  Inference rules
% 4.27/1.76  ----------------------
% 4.27/1.76  #Ref     : 0
% 4.27/1.76  #Sup     : 255
% 4.27/1.76  #Fact    : 0
% 4.27/1.76  #Define  : 0
% 4.27/1.76  #Split   : 8
% 4.27/1.76  #Chain   : 0
% 4.27/1.76  #Close   : 0
% 4.27/1.76  
% 4.27/1.76  Ordering : KBO
% 4.27/1.76  
% 4.27/1.76  Simplification rules
% 4.27/1.76  ----------------------
% 4.27/1.76  #Subsume      : 27
% 4.27/1.76  #Demod        : 109
% 4.27/1.76  #Tautology    : 27
% 4.27/1.76  #SimpNegUnit  : 6
% 4.27/1.76  #BackRed      : 5
% 4.27/1.76  
% 4.27/1.76  #Partial instantiations: 0
% 4.27/1.76  #Strategies tried      : 1
% 4.27/1.76  
% 4.27/1.76  Timing (in seconds)
% 4.27/1.76  ----------------------
% 4.34/1.76  Preprocessing        : 0.36
% 4.34/1.76  Parsing              : 0.20
% 4.34/1.76  CNF conversion       : 0.03
% 4.34/1.76  Main loop            : 0.56
% 4.34/1.76  Inferencing          : 0.21
% 4.34/1.76  Reduction            : 0.17
% 4.34/1.76  Demodulation         : 0.12
% 4.34/1.76  BG Simplification    : 0.03
% 4.34/1.76  Subsumption          : 0.11
% 4.34/1.76  Abstraction          : 0.03
% 4.34/1.76  MUC search           : 0.00
% 4.34/1.76  Cooper               : 0.00
% 4.34/1.76  Total                : 0.98
% 4.34/1.76  Index Insertion      : 0.00
% 4.34/1.76  Index Deletion       : 0.00
% 4.34/1.76  Index Matching       : 0.00
% 4.34/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
