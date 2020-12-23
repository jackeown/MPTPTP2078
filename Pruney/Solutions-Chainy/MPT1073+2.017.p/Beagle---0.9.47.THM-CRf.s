%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:00 EST 2020

% Result     : Theorem 6.62s
% Output     : CNFRefutation 7.06s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 229 expanded)
%              Number of leaves         :   49 ( 101 expanded)
%              Depth                    :   10
%              Number of atoms          :  171 ( 537 expanded)
%              Number of equality atoms :   35 ( 108 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

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

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_113,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
     => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
        & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( B = k2_relat_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ? [D] :
                  ( r2_hidden(D,k1_relat_1(A))
                  & C = k1_funct_1(A,D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(c_68,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_109,plain,(
    ! [C_94,A_95,B_96] :
      ( v1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_113,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_68,c_109])).

tff(c_72,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_136,plain,(
    ! [C_101,B_102,A_103] :
      ( v5_relat_1(C_101,B_102)
      | ~ m1_subset_1(C_101,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_145,plain,(
    v5_relat_1('#skF_10','#skF_9') ),
    inference(resolution,[status(thm)],[c_68,c_136])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_530,plain,(
    ! [B_187,C_188,A_189] :
      ( r2_hidden(k1_funct_1(B_187,C_188),A_189)
      | ~ r2_hidden(C_188,k1_relat_1(B_187))
      | ~ v1_funct_1(B_187)
      | ~ v5_relat_1(B_187,A_189)
      | ~ v1_relat_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_592,plain,(
    ! [A_190,C_191,B_192] :
      ( ~ v1_xboole_0(A_190)
      | ~ r2_hidden(C_191,k1_relat_1(B_192))
      | ~ v1_funct_1(B_192)
      | ~ v5_relat_1(B_192,A_190)
      | ~ v1_relat_1(B_192) ) ),
    inference(resolution,[status(thm)],[c_530,c_2])).

tff(c_616,plain,(
    ! [A_193,B_194] :
      ( ~ v1_xboole_0(A_193)
      | ~ v1_funct_1(B_194)
      | ~ v5_relat_1(B_194,A_193)
      | ~ v1_relat_1(B_194)
      | v1_xboole_0(k1_relat_1(B_194)) ) ),
    inference(resolution,[status(thm)],[c_4,c_592])).

tff(c_620,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_145,c_616])).

tff(c_624,plain,
    ( ~ v1_xboole_0('#skF_9')
    | v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_72,c_620])).

tff(c_625,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_624])).

tff(c_147,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_156,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_68,c_147])).

tff(c_66,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_160,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_66])).

tff(c_70,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1843,plain,(
    ! [B_299,A_300,C_301] :
      ( k1_xboole_0 = B_299
      | k8_relset_1(A_300,B_299,C_301,B_299) = A_300
      | ~ m1_subset_1(C_301,k1_zfmisc_1(k2_zfmisc_1(A_300,B_299)))
      | ~ v1_funct_2(C_301,A_300,B_299)
      | ~ v1_funct_1(C_301) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1857,plain,
    ( k1_xboole_0 = '#skF_9'
    | k8_relset_1('#skF_8','#skF_9','#skF_10','#skF_9') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | ~ v1_funct_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_68,c_1843])).

tff(c_1864,plain,
    ( k1_xboole_0 = '#skF_9'
    | k8_relset_1('#skF_8','#skF_9','#skF_10','#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_1857])).

tff(c_1865,plain,(
    k8_relset_1('#skF_8','#skF_9','#skF_10','#skF_9') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1864])).

tff(c_1668,plain,(
    ! [B_289,A_290,C_291] :
      ( k7_relset_1(B_289,A_290,C_291,k8_relset_1(B_289,A_290,C_291,A_290)) = k2_relset_1(B_289,A_290,C_291)
      | ~ m1_subset_1(C_291,k1_zfmisc_1(k2_zfmisc_1(B_289,A_290))) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1682,plain,(
    k7_relset_1('#skF_8','#skF_9','#skF_10',k8_relset_1('#skF_8','#skF_9','#skF_10','#skF_9')) = k2_relset_1('#skF_8','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_68,c_1668])).

tff(c_1688,plain,(
    k7_relset_1('#skF_8','#skF_9','#skF_10',k8_relset_1('#skF_8','#skF_9','#skF_10','#skF_9')) = k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_1682])).

tff(c_207,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k7_relset_1(A_127,B_128,C_129,D_130) = k9_relat_1(C_129,D_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_214,plain,(
    ! [D_130] : k7_relset_1('#skF_8','#skF_9','#skF_10',D_130) = k9_relat_1('#skF_10',D_130) ),
    inference(resolution,[status(thm)],[c_68,c_207])).

tff(c_1692,plain,(
    k9_relat_1('#skF_10',k8_relset_1('#skF_8','#skF_9','#skF_10','#skF_9')) = k2_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_214])).

tff(c_1867,plain,(
    k9_relat_1('#skF_10','#skF_8') = k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_1692])).

tff(c_181,plain,(
    ! [A_116,B_117,C_118] :
      ( r2_hidden('#skF_2'(A_116,B_117,C_118),B_117)
      | ~ r2_hidden(A_116,k9_relat_1(C_118,B_117))
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,B_7)
      | ~ r2_hidden(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_191,plain,(
    ! [A_116,B_117,C_118] :
      ( m1_subset_1('#skF_2'(A_116,B_117,C_118),B_117)
      | ~ r2_hidden(A_116,k9_relat_1(C_118,B_117))
      | ~ v1_relat_1(C_118) ) ),
    inference(resolution,[status(thm)],[c_181,c_8])).

tff(c_1901,plain,(
    ! [A_116] :
      ( m1_subset_1('#skF_2'(A_116,'#skF_8','#skF_10'),'#skF_8')
      | ~ r2_hidden(A_116,k2_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1867,c_191])).

tff(c_1973,plain,(
    ! [A_302] :
      ( m1_subset_1('#skF_2'(A_302,'#skF_8','#skF_10'),'#skF_8')
      | ~ r2_hidden(A_302,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_1901])).

tff(c_2018,plain,(
    m1_subset_1('#skF_2'('#skF_7','#skF_8','#skF_10'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_160,c_1973])).

tff(c_64,plain,(
    ! [E_83] :
      ( k1_funct_1('#skF_10',E_83) != '#skF_7'
      | ~ m1_subset_1(E_83,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2163,plain,(
    k1_funct_1('#skF_10','#skF_2'('#skF_7','#skF_8','#skF_10')) != '#skF_7' ),
    inference(resolution,[status(thm)],[c_2018,c_64])).

tff(c_421,plain,(
    ! [A_172,B_173,C_174] :
      ( r2_hidden(k4_tarski('#skF_2'(A_172,B_173,C_174),A_172),C_174)
      | ~ r2_hidden(A_172,k9_relat_1(C_174,B_173))
      | ~ v1_relat_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    ! [C_60,A_58,B_59] :
      ( k1_funct_1(C_60,A_58) = B_59
      | ~ r2_hidden(k4_tarski(A_58,B_59),C_60)
      | ~ v1_funct_1(C_60)
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4260,plain,(
    ! [C_450,A_451,B_452] :
      ( k1_funct_1(C_450,'#skF_2'(A_451,B_452,C_450)) = A_451
      | ~ v1_funct_1(C_450)
      | ~ r2_hidden(A_451,k9_relat_1(C_450,B_452))
      | ~ v1_relat_1(C_450) ) ),
    inference(resolution,[status(thm)],[c_421,c_40])).

tff(c_4274,plain,(
    ! [A_451] :
      ( k1_funct_1('#skF_10','#skF_2'(A_451,'#skF_8','#skF_10')) = A_451
      | ~ v1_funct_1('#skF_10')
      | ~ r2_hidden(A_451,k2_relat_1('#skF_10'))
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1867,c_4260])).

tff(c_4312,plain,(
    ! [A_453] :
      ( k1_funct_1('#skF_10','#skF_2'(A_453,'#skF_8','#skF_10')) = A_453
      | ~ r2_hidden(A_453,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_72,c_4274])).

tff(c_4359,plain,(
    k1_funct_1('#skF_10','#skF_2'('#skF_7','#skF_8','#skF_10')) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_160,c_4312])).

tff(c_4380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2163,c_4359])).

tff(c_4381,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1864])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [B_88,A_89] :
      ( ~ r1_tarski(B_88,A_89)
      | ~ r2_hidden(A_89,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_103,plain,(
    ! [A_93] :
      ( ~ r1_tarski(A_93,'#skF_1'(A_93))
      | v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_4,c_84])).

tff(c_108,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_103])).

tff(c_4395,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4381,c_108])).

tff(c_4398,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_625,c_4395])).

tff(c_4399,plain,(
    v1_xboole_0(k1_relat_1('#skF_10')) ),
    inference(splitRight,[status(thm)],[c_624])).

tff(c_4456,plain,(
    ! [A_469,C_470] :
      ( r2_hidden('#skF_6'(A_469,k2_relat_1(A_469),C_470),k1_relat_1(A_469))
      | ~ r2_hidden(C_470,k2_relat_1(A_469))
      | ~ v1_funct_1(A_469)
      | ~ v1_relat_1(A_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4545,plain,(
    ! [A_476,C_477] :
      ( ~ v1_xboole_0(k1_relat_1(A_476))
      | ~ r2_hidden(C_477,k2_relat_1(A_476))
      | ~ v1_funct_1(A_476)
      | ~ v1_relat_1(A_476) ) ),
    inference(resolution,[status(thm)],[c_4456,c_2])).

tff(c_4567,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_10'))
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_160,c_4545])).

tff(c_4580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_72,c_4399,c_4567])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:10 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.62/2.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.37  
% 6.62/2.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.62/2.37  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 6.62/2.37  
% 6.62/2.37  %Foreground sorts:
% 6.62/2.37  
% 6.62/2.37  
% 6.62/2.37  %Background operators:
% 6.62/2.37  
% 6.62/2.37  
% 6.62/2.37  %Foreground operators:
% 6.62/2.37  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.62/2.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.62/2.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.62/2.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.62/2.37  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.62/2.37  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.62/2.37  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.62/2.37  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.62/2.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.62/2.37  tff('#skF_7', type, '#skF_7': $i).
% 6.62/2.37  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.62/2.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.62/2.37  tff('#skF_10', type, '#skF_10': $i).
% 6.62/2.37  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.62/2.37  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.62/2.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.62/2.37  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.62/2.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.62/2.37  tff('#skF_9', type, '#skF_9': $i).
% 6.62/2.37  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.62/2.37  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.62/2.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.62/2.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.62/2.37  tff('#skF_8', type, '#skF_8': $i).
% 6.62/2.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.62/2.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.62/2.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.62/2.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.62/2.37  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.62/2.37  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.62/2.37  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 6.62/2.37  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.62/2.37  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.62/2.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.62/2.37  
% 7.06/2.41  tff(f_141, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 7.06/2.41  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.06/2.41  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.06/2.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.06/2.41  tff(f_74, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 7.06/2.41  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.06/2.41  tff(f_125, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_2)).
% 7.06/2.41  tff(f_113, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_relset_1)).
% 7.06/2.41  tff(f_107, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.06/2.41  tff(f_48, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 7.06/2.41  tff(f_37, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.06/2.41  tff(f_84, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 7.06/2.41  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.06/2.41  tff(f_89, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.06/2.41  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 7.06/2.41  tff(c_68, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.06/2.41  tff(c_109, plain, (![C_94, A_95, B_96]: (v1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.06/2.41  tff(c_113, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_68, c_109])).
% 7.06/2.41  tff(c_72, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.06/2.41  tff(c_136, plain, (![C_101, B_102, A_103]: (v5_relat_1(C_101, B_102) | ~m1_subset_1(C_101, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.06/2.41  tff(c_145, plain, (v5_relat_1('#skF_10', '#skF_9')), inference(resolution, [status(thm)], [c_68, c_136])).
% 7.06/2.41  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.06/2.41  tff(c_530, plain, (![B_187, C_188, A_189]: (r2_hidden(k1_funct_1(B_187, C_188), A_189) | ~r2_hidden(C_188, k1_relat_1(B_187)) | ~v1_funct_1(B_187) | ~v5_relat_1(B_187, A_189) | ~v1_relat_1(B_187))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.06/2.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.06/2.41  tff(c_592, plain, (![A_190, C_191, B_192]: (~v1_xboole_0(A_190) | ~r2_hidden(C_191, k1_relat_1(B_192)) | ~v1_funct_1(B_192) | ~v5_relat_1(B_192, A_190) | ~v1_relat_1(B_192))), inference(resolution, [status(thm)], [c_530, c_2])).
% 7.06/2.41  tff(c_616, plain, (![A_193, B_194]: (~v1_xboole_0(A_193) | ~v1_funct_1(B_194) | ~v5_relat_1(B_194, A_193) | ~v1_relat_1(B_194) | v1_xboole_0(k1_relat_1(B_194)))), inference(resolution, [status(thm)], [c_4, c_592])).
% 7.06/2.41  tff(c_620, plain, (~v1_xboole_0('#skF_9') | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10') | v1_xboole_0(k1_relat_1('#skF_10'))), inference(resolution, [status(thm)], [c_145, c_616])).
% 7.06/2.41  tff(c_624, plain, (~v1_xboole_0('#skF_9') | v1_xboole_0(k1_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_72, c_620])).
% 7.06/2.41  tff(c_625, plain, (~v1_xboole_0('#skF_9')), inference(splitLeft, [status(thm)], [c_624])).
% 7.06/2.41  tff(c_147, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.06/2.41  tff(c_156, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_68, c_147])).
% 7.06/2.41  tff(c_66, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.06/2.41  tff(c_160, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_66])).
% 7.06/2.41  tff(c_70, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.06/2.41  tff(c_1843, plain, (![B_299, A_300, C_301]: (k1_xboole_0=B_299 | k8_relset_1(A_300, B_299, C_301, B_299)=A_300 | ~m1_subset_1(C_301, k1_zfmisc_1(k2_zfmisc_1(A_300, B_299))) | ~v1_funct_2(C_301, A_300, B_299) | ~v1_funct_1(C_301))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.06/2.41  tff(c_1857, plain, (k1_xboole_0='#skF_9' | k8_relset_1('#skF_8', '#skF_9', '#skF_10', '#skF_9')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | ~v1_funct_1('#skF_10')), inference(resolution, [status(thm)], [c_68, c_1843])).
% 7.06/2.41  tff(c_1864, plain, (k1_xboole_0='#skF_9' | k8_relset_1('#skF_8', '#skF_9', '#skF_10', '#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_1857])).
% 7.06/2.41  tff(c_1865, plain, (k8_relset_1('#skF_8', '#skF_9', '#skF_10', '#skF_9')='#skF_8'), inference(splitLeft, [status(thm)], [c_1864])).
% 7.06/2.41  tff(c_1668, plain, (![B_289, A_290, C_291]: (k7_relset_1(B_289, A_290, C_291, k8_relset_1(B_289, A_290, C_291, A_290))=k2_relset_1(B_289, A_290, C_291) | ~m1_subset_1(C_291, k1_zfmisc_1(k2_zfmisc_1(B_289, A_290))))), inference(cnfTransformation, [status(thm)], [f_113])).
% 7.06/2.41  tff(c_1682, plain, (k7_relset_1('#skF_8', '#skF_9', '#skF_10', k8_relset_1('#skF_8', '#skF_9', '#skF_10', '#skF_9'))=k2_relset_1('#skF_8', '#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_68, c_1668])).
% 7.06/2.41  tff(c_1688, plain, (k7_relset_1('#skF_8', '#skF_9', '#skF_10', k8_relset_1('#skF_8', '#skF_9', '#skF_10', '#skF_9'))=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_1682])).
% 7.06/2.41  tff(c_207, plain, (![A_127, B_128, C_129, D_130]: (k7_relset_1(A_127, B_128, C_129, D_130)=k9_relat_1(C_129, D_130) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.06/2.41  tff(c_214, plain, (![D_130]: (k7_relset_1('#skF_8', '#skF_9', '#skF_10', D_130)=k9_relat_1('#skF_10', D_130))), inference(resolution, [status(thm)], [c_68, c_207])).
% 7.06/2.41  tff(c_1692, plain, (k9_relat_1('#skF_10', k8_relset_1('#skF_8', '#skF_9', '#skF_10', '#skF_9'))=k2_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_1688, c_214])).
% 7.06/2.41  tff(c_1867, plain, (k9_relat_1('#skF_10', '#skF_8')=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_1692])).
% 7.06/2.41  tff(c_181, plain, (![A_116, B_117, C_118]: (r2_hidden('#skF_2'(A_116, B_117, C_118), B_117) | ~r2_hidden(A_116, k9_relat_1(C_118, B_117)) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.06/2.41  tff(c_8, plain, (![A_6, B_7]: (m1_subset_1(A_6, B_7) | ~r2_hidden(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.06/2.41  tff(c_191, plain, (![A_116, B_117, C_118]: (m1_subset_1('#skF_2'(A_116, B_117, C_118), B_117) | ~r2_hidden(A_116, k9_relat_1(C_118, B_117)) | ~v1_relat_1(C_118))), inference(resolution, [status(thm)], [c_181, c_8])).
% 7.06/2.41  tff(c_1901, plain, (![A_116]: (m1_subset_1('#skF_2'(A_116, '#skF_8', '#skF_10'), '#skF_8') | ~r2_hidden(A_116, k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1867, c_191])).
% 7.06/2.41  tff(c_1973, plain, (![A_302]: (m1_subset_1('#skF_2'(A_302, '#skF_8', '#skF_10'), '#skF_8') | ~r2_hidden(A_302, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_1901])).
% 7.06/2.41  tff(c_2018, plain, (m1_subset_1('#skF_2'('#skF_7', '#skF_8', '#skF_10'), '#skF_8')), inference(resolution, [status(thm)], [c_160, c_1973])).
% 7.06/2.41  tff(c_64, plain, (![E_83]: (k1_funct_1('#skF_10', E_83)!='#skF_7' | ~m1_subset_1(E_83, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 7.06/2.41  tff(c_2163, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_7', '#skF_8', '#skF_10'))!='#skF_7'), inference(resolution, [status(thm)], [c_2018, c_64])).
% 7.06/2.41  tff(c_421, plain, (![A_172, B_173, C_174]: (r2_hidden(k4_tarski('#skF_2'(A_172, B_173, C_174), A_172), C_174) | ~r2_hidden(A_172, k9_relat_1(C_174, B_173)) | ~v1_relat_1(C_174))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.06/2.41  tff(c_40, plain, (![C_60, A_58, B_59]: (k1_funct_1(C_60, A_58)=B_59 | ~r2_hidden(k4_tarski(A_58, B_59), C_60) | ~v1_funct_1(C_60) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.06/2.41  tff(c_4260, plain, (![C_450, A_451, B_452]: (k1_funct_1(C_450, '#skF_2'(A_451, B_452, C_450))=A_451 | ~v1_funct_1(C_450) | ~r2_hidden(A_451, k9_relat_1(C_450, B_452)) | ~v1_relat_1(C_450))), inference(resolution, [status(thm)], [c_421, c_40])).
% 7.06/2.41  tff(c_4274, plain, (![A_451]: (k1_funct_1('#skF_10', '#skF_2'(A_451, '#skF_8', '#skF_10'))=A_451 | ~v1_funct_1('#skF_10') | ~r2_hidden(A_451, k2_relat_1('#skF_10')) | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1867, c_4260])).
% 7.06/2.41  tff(c_4312, plain, (![A_453]: (k1_funct_1('#skF_10', '#skF_2'(A_453, '#skF_8', '#skF_10'))=A_453 | ~r2_hidden(A_453, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_72, c_4274])).
% 7.06/2.41  tff(c_4359, plain, (k1_funct_1('#skF_10', '#skF_2'('#skF_7', '#skF_8', '#skF_10'))='#skF_7'), inference(resolution, [status(thm)], [c_160, c_4312])).
% 7.06/2.41  tff(c_4380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2163, c_4359])).
% 7.06/2.41  tff(c_4381, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_1864])).
% 7.06/2.41  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.06/2.41  tff(c_84, plain, (![B_88, A_89]: (~r1_tarski(B_88, A_89) | ~r2_hidden(A_89, B_88))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.06/2.41  tff(c_103, plain, (![A_93]: (~r1_tarski(A_93, '#skF_1'(A_93)) | v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_4, c_84])).
% 7.06/2.41  tff(c_108, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_103])).
% 7.06/2.41  tff(c_4395, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4381, c_108])).
% 7.06/2.41  tff(c_4398, plain, $false, inference(negUnitSimplification, [status(thm)], [c_625, c_4395])).
% 7.06/2.41  tff(c_4399, plain, (v1_xboole_0(k1_relat_1('#skF_10'))), inference(splitRight, [status(thm)], [c_624])).
% 7.06/2.41  tff(c_4456, plain, (![A_469, C_470]: (r2_hidden('#skF_6'(A_469, k2_relat_1(A_469), C_470), k1_relat_1(A_469)) | ~r2_hidden(C_470, k2_relat_1(A_469)) | ~v1_funct_1(A_469) | ~v1_relat_1(A_469))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.06/2.41  tff(c_4545, plain, (![A_476, C_477]: (~v1_xboole_0(k1_relat_1(A_476)) | ~r2_hidden(C_477, k2_relat_1(A_476)) | ~v1_funct_1(A_476) | ~v1_relat_1(A_476))), inference(resolution, [status(thm)], [c_4456, c_2])).
% 7.06/2.41  tff(c_4567, plain, (~v1_xboole_0(k1_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_160, c_4545])).
% 7.06/2.41  tff(c_4580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_113, c_72, c_4399, c_4567])).
% 7.06/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.06/2.41  
% 7.06/2.41  Inference rules
% 7.06/2.41  ----------------------
% 7.06/2.41  #Ref     : 0
% 7.06/2.41  #Sup     : 1026
% 7.06/2.41  #Fact    : 0
% 7.06/2.41  #Define  : 0
% 7.06/2.41  #Split   : 5
% 7.06/2.41  #Chain   : 0
% 7.06/2.41  #Close   : 0
% 7.06/2.41  
% 7.06/2.41  Ordering : KBO
% 7.06/2.41  
% 7.06/2.41  Simplification rules
% 7.06/2.41  ----------------------
% 7.06/2.41  #Subsume      : 121
% 7.06/2.41  #Demod        : 137
% 7.06/2.41  #Tautology    : 35
% 7.06/2.41  #SimpNegUnit  : 14
% 7.06/2.41  #BackRed      : 22
% 7.06/2.41  
% 7.06/2.41  #Partial instantiations: 0
% 7.06/2.41  #Strategies tried      : 1
% 7.06/2.41  
% 7.06/2.41  Timing (in seconds)
% 7.06/2.41  ----------------------
% 7.13/2.41  Preprocessing        : 0.36
% 7.13/2.41  Parsing              : 0.19
% 7.13/2.41  CNF conversion       : 0.03
% 7.13/2.41  Main loop            : 1.25
% 7.13/2.41  Inferencing          : 0.37
% 7.13/2.41  Reduction            : 0.28
% 7.13/2.42  Demodulation         : 0.19
% 7.13/2.42  BG Simplification    : 0.05
% 7.13/2.42  Subsumption          : 0.42
% 7.13/2.42  Abstraction          : 0.08
% 7.13/2.42  MUC search           : 0.00
% 7.13/2.42  Cooper               : 0.00
% 7.13/2.42  Total                : 1.67
% 7.13/2.42  Index Insertion      : 0.00
% 7.13/2.42  Index Deletion       : 0.00
% 7.13/2.42  Index Matching       : 0.00
% 7.13/2.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
