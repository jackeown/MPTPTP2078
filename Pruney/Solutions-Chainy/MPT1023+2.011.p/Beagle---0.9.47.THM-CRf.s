%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:18 EST 2020

% Result     : Theorem 4.49s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 547 expanded)
%              Number of leaves         :   34 ( 198 expanded)
%              Depth                    :   15
%              Number of atoms          :  240 (1684 expanded)
%              Number of equality atoms :   81 ( 386 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_141,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( ! [E] :
                  ( m1_subset_1(E,A)
                 => k1_funct_1(C,E) = k1_funct_1(D,E) )
             => r2_relset_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_120,axiom,(
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

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k1_relat_1(A) = k1_relat_1(B)
              & ! [C] :
                  ( r2_hidden(C,k1_relat_1(A))
                 => k1_funct_1(A,C) = k1_funct_1(B,C) ) )
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_55,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_204,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_223,plain,(
    r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_204])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_248,plain,(
    ! [A_79,B_80,C_81] :
      ( k1_relset_1(A_79,B_80,C_81) = k1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_271,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_248])).

tff(c_157,plain,(
    ! [C_62,B_63,A_64] :
      ( v1_xboole_0(C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(B_63,A_64)))
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_178,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_157])).

tff(c_182,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_133,plain,(
    ! [C_59,A_60,B_61] :
      ( v1_relat_1(C_59)
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_154,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_133])).

tff(c_838,plain,(
    ! [B_130,A_131,C_132] :
      ( k1_xboole_0 = B_130
      | k1_relset_1(A_131,B_130,C_132) = A_131
      | ~ v1_funct_2(C_132,A_131,B_130)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_131,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_856,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_838])).

tff(c_872,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_271,c_856])).

tff(c_878,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_872])).

tff(c_155,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_133])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_54,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_272,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_52,c_248])).

tff(c_859,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_838])).

tff(c_875,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_272,c_859])).

tff(c_884,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_875])).

tff(c_14,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_103,plain,(
    ! [E_53] :
      ( k1_funct_1('#skF_5',E_53) = k1_funct_1('#skF_6',E_53)
      | ~ m1_subset_1(E_53,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_108,plain,(
    ! [B_8] :
      ( k1_funct_1('#skF_5',B_8) = k1_funct_1('#skF_6',B_8)
      | ~ v1_xboole_0(B_8)
      | ~ v1_xboole_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_103])).

tff(c_289,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_108])).

tff(c_1048,plain,(
    ! [A_150,B_151] :
      ( r2_hidden('#skF_2'(A_150,B_151),k1_relat_1(A_150))
      | B_151 = A_150
      | k1_relat_1(B_151) != k1_relat_1(A_150)
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151)
      | ~ v1_funct_1(A_150)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1057,plain,(
    ! [B_151] :
      ( r2_hidden('#skF_2'('#skF_6',B_151),'#skF_3')
      | B_151 = '#skF_6'
      | k1_relat_1(B_151) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_151)
      | ~ v1_relat_1(B_151)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_884,c_1048])).

tff(c_1072,plain,(
    ! [B_152] :
      ( r2_hidden('#skF_2'('#skF_6',B_152),'#skF_3')
      | B_152 = '#skF_6'
      | k1_relat_1(B_152) != '#skF_3'
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_56,c_884,c_1057])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ r2_hidden(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1075,plain,(
    ! [B_152] :
      ( m1_subset_1('#skF_2'('#skF_6',B_152),'#skF_3')
      | v1_xboole_0('#skF_3')
      | B_152 = '#skF_6'
      | k1_relat_1(B_152) != '#skF_3'
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(resolution,[status(thm)],[c_1072,c_10])).

tff(c_1094,plain,(
    ! [B_154] :
      ( m1_subset_1('#skF_2'('#skF_6',B_154),'#skF_3')
      | B_154 = '#skF_6'
      | k1_relat_1(B_154) != '#skF_3'
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154) ) ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_1075])).

tff(c_50,plain,(
    ! [E_40] :
      ( k1_funct_1('#skF_5',E_40) = k1_funct_1('#skF_6',E_40)
      | ~ m1_subset_1(E_40,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1470,plain,(
    ! [B_178] :
      ( k1_funct_1('#skF_5','#skF_2'('#skF_6',B_178)) = k1_funct_1('#skF_6','#skF_2'('#skF_6',B_178))
      | B_178 = '#skF_6'
      | k1_relat_1(B_178) != '#skF_3'
      | ~ v1_funct_1(B_178)
      | ~ v1_relat_1(B_178) ) ),
    inference(resolution,[status(thm)],[c_1094,c_50])).

tff(c_22,plain,(
    ! [B_17,A_13] :
      ( k1_funct_1(B_17,'#skF_2'(A_13,B_17)) != k1_funct_1(A_13,'#skF_2'(A_13,B_17))
      | B_17 = A_13
      | k1_relat_1(B_17) != k1_relat_1(A_13)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1477,plain,
    ( k1_relat_1('#skF_5') != k1_relat_1('#skF_6')
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6')
    | '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1470,c_22])).

tff(c_1484,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_62,c_878,c_155,c_56,c_884,c_878,c_1477])).

tff(c_48,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_1498,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1484,c_48])).

tff(c_1508,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_1498])).

tff(c_1509,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_875])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1534,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_6])).

tff(c_1536,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1534])).

tff(c_1537,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_872])).

tff(c_1562,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1537,c_6])).

tff(c_1564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_1562])).

tff(c_1566,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_108])).

tff(c_67,plain,(
    ! [B_44,A_45] :
      ( ~ v1_xboole_0(B_44)
      | B_44 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_70,plain,(
    ! [A_45] :
      ( k1_xboole_0 = A_45
      | ~ v1_xboole_0(A_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_67])).

tff(c_1572,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1566,c_70])).

tff(c_44,plain,(
    ! [B_34,C_35] :
      ( k1_relset_1(k1_xboole_0,B_34,C_35) = k1_xboole_0
      | ~ v1_funct_2(C_35,k1_xboole_0,B_34)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1659,plain,(
    ! [B_188,C_189] :
      ( k1_relset_1('#skF_3',B_188,C_189) = '#skF_3'
      | ~ v1_funct_2(C_189,'#skF_3',B_188)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_188))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_1572,c_1572,c_1572,c_44])).

tff(c_1674,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_5') = '#skF_3'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1659])).

tff(c_1685,plain,(
    k1_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_271,c_1674])).

tff(c_1677,plain,
    ( k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_1659])).

tff(c_1688,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_272,c_1677])).

tff(c_2272,plain,(
    ! [A_241,B_242] :
      ( r2_hidden('#skF_2'(A_241,B_242),k1_relat_1(A_241))
      | B_242 = A_241
      | k1_relat_1(B_242) != k1_relat_1(A_241)
      | ~ v1_funct_1(B_242)
      | ~ v1_relat_1(B_242)
      | ~ v1_funct_1(A_241)
      | ~ v1_relat_1(A_241) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2284,plain,(
    ! [B_242] :
      ( r2_hidden('#skF_2'('#skF_6',B_242),'#skF_3')
      | B_242 = '#skF_6'
      | k1_relat_1(B_242) != k1_relat_1('#skF_6')
      | ~ v1_funct_1(B_242)
      | ~ v1_relat_1(B_242)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1688,c_2272])).

tff(c_2325,plain,(
    ! [B_244] :
      ( r2_hidden('#skF_2'('#skF_6',B_244),'#skF_3')
      | B_244 = '#skF_6'
      | k1_relat_1(B_244) != '#skF_3'
      | ~ v1_funct_1(B_244)
      | ~ v1_relat_1(B_244) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_56,c_1688,c_2284])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2333,plain,(
    ! [B_244] :
      ( ~ v1_xboole_0('#skF_3')
      | B_244 = '#skF_6'
      | k1_relat_1(B_244) != '#skF_3'
      | ~ v1_funct_1(B_244)
      | ~ v1_relat_1(B_244) ) ),
    inference(resolution,[status(thm)],[c_2325,c_2])).

tff(c_2340,plain,(
    ! [B_245] :
      ( B_245 = '#skF_6'
      | k1_relat_1(B_245) != '#skF_3'
      | ~ v1_funct_1(B_245)
      | ~ v1_relat_1(B_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_2333])).

tff(c_2352,plain,
    ( '#skF_5' = '#skF_6'
    | k1_relat_1('#skF_5') != '#skF_3'
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_154,c_2340])).

tff(c_2361,plain,(
    '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1685,c_2352])).

tff(c_2373,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2361,c_48])).

tff(c_2383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_2373])).

tff(c_2385,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2398,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2385,c_70])).

tff(c_2384,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2391,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_2384,c_70])).

tff(c_2429,plain,(
    '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2398,c_2391])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2421,plain,(
    ! [A_9] : m1_subset_1('#skF_5',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2391,c_18])).

tff(c_2486,plain,(
    ! [A_253] : m1_subset_1('#skF_4',k1_zfmisc_1(A_253)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_2421])).

tff(c_32,plain,(
    ! [A_29,B_30,D_32] :
      ( r2_relset_1(A_29,B_30,D_32,D_32)
      | ~ m1_subset_1(D_32,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2503,plain,(
    ! [A_29,B_30] : r2_relset_1(A_29,B_30,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2486,c_32])).

tff(c_179,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_157])).

tff(c_2447,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2385,c_179])).

tff(c_2420,plain,(
    ! [A_45] :
      ( A_45 = '#skF_5'
      | ~ v1_xboole_0(A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2391,c_70])).

tff(c_2452,plain,(
    ! [A_249] :
      ( A_249 = '#skF_4'
      | ~ v1_xboole_0(A_249) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_2420])).

tff(c_2459,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2447,c_2452])).

tff(c_2438,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2429,c_48])).

tff(c_2512,plain,(
    ~ r2_relset_1('#skF_3','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2459,c_2438])).

tff(c_2515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2503,c_2512])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:14:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.49/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.84  
% 4.49/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.49/1.84  %$ r2_relset_1 > v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2
% 4.49/1.84  
% 4.49/1.84  %Foreground sorts:
% 4.49/1.84  
% 4.49/1.84  
% 4.49/1.84  %Background operators:
% 4.49/1.84  
% 4.49/1.84  
% 4.49/1.84  %Foreground operators:
% 4.49/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.49/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.49/1.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.49/1.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.49/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.49/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.49/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.49/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.49/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.49/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.49/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.49/1.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.49/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.49/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.49/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.49/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.84  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.49/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.49/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.49/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.49/1.84  
% 4.69/1.86  tff(f_141, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![E]: (m1_subset_1(E, A) => (k1_funct_1(C, E) = k1_funct_1(D, E)))) => r2_relset_1(A, B, C, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_funct_2)).
% 4.69/1.86  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.69/1.86  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.69/1.86  tff(f_90, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 4.69/1.86  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.69/1.86  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.69/1.86  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.69/1.86  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k1_relat_1(A) = k1_relat_1(B)) & (![C]: (r2_hidden(C, k1_relat_1(A)) => (k1_funct_1(A, C) = k1_funct_1(B, C))))) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_1)).
% 4.69/1.86  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.69/1.86  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 4.69/1.86  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.69/1.86  tff(f_55, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 4.69/1.86  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_204, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.69/1.86  tff(c_223, plain, (r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(resolution, [status(thm)], [c_52, c_204])).
% 4.69/1.86  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_248, plain, (![A_79, B_80, C_81]: (k1_relset_1(A_79, B_80, C_81)=k1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.69/1.86  tff(c_271, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_248])).
% 4.69/1.86  tff(c_157, plain, (![C_62, B_63, A_64]: (v1_xboole_0(C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(B_63, A_64))) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.69/1.86  tff(c_178, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_58, c_157])).
% 4.69/1.86  tff(c_182, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_178])).
% 4.69/1.86  tff(c_133, plain, (![C_59, A_60, B_61]: (v1_relat_1(C_59) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.69/1.86  tff(c_154, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_133])).
% 4.69/1.86  tff(c_838, plain, (![B_130, A_131, C_132]: (k1_xboole_0=B_130 | k1_relset_1(A_131, B_130, C_132)=A_131 | ~v1_funct_2(C_132, A_131, B_130) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_131, B_130))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.86  tff(c_856, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_838])).
% 4.69/1.86  tff(c_872, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_271, c_856])).
% 4.69/1.86  tff(c_878, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(splitLeft, [status(thm)], [c_872])).
% 4.69/1.86  tff(c_155, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_133])).
% 4.69/1.86  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_54, plain, (v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_272, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_52, c_248])).
% 4.69/1.86  tff(c_859, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_838])).
% 4.69/1.86  tff(c_875, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_272, c_859])).
% 4.69/1.86  tff(c_884, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_875])).
% 4.69/1.86  tff(c_14, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~v1_xboole_0(B_8) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.69/1.86  tff(c_103, plain, (![E_53]: (k1_funct_1('#skF_5', E_53)=k1_funct_1('#skF_6', E_53) | ~m1_subset_1(E_53, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_108, plain, (![B_8]: (k1_funct_1('#skF_5', B_8)=k1_funct_1('#skF_6', B_8) | ~v1_xboole_0(B_8) | ~v1_xboole_0('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_103])).
% 4.69/1.86  tff(c_289, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_108])).
% 4.69/1.86  tff(c_1048, plain, (![A_150, B_151]: (r2_hidden('#skF_2'(A_150, B_151), k1_relat_1(A_150)) | B_151=A_150 | k1_relat_1(B_151)!=k1_relat_1(A_150) | ~v1_funct_1(B_151) | ~v1_relat_1(B_151) | ~v1_funct_1(A_150) | ~v1_relat_1(A_150))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.86  tff(c_1057, plain, (![B_151]: (r2_hidden('#skF_2'('#skF_6', B_151), '#skF_3') | B_151='#skF_6' | k1_relat_1(B_151)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_151) | ~v1_relat_1(B_151) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_884, c_1048])).
% 4.69/1.86  tff(c_1072, plain, (![B_152]: (r2_hidden('#skF_2'('#skF_6', B_152), '#skF_3') | B_152='#skF_6' | k1_relat_1(B_152)!='#skF_3' | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_56, c_884, c_1057])).
% 4.69/1.86  tff(c_10, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~r2_hidden(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.69/1.86  tff(c_1075, plain, (![B_152]: (m1_subset_1('#skF_2'('#skF_6', B_152), '#skF_3') | v1_xboole_0('#skF_3') | B_152='#skF_6' | k1_relat_1(B_152)!='#skF_3' | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(resolution, [status(thm)], [c_1072, c_10])).
% 4.69/1.86  tff(c_1094, plain, (![B_154]: (m1_subset_1('#skF_2'('#skF_6', B_154), '#skF_3') | B_154='#skF_6' | k1_relat_1(B_154)!='#skF_3' | ~v1_funct_1(B_154) | ~v1_relat_1(B_154))), inference(negUnitSimplification, [status(thm)], [c_289, c_1075])).
% 4.69/1.86  tff(c_50, plain, (![E_40]: (k1_funct_1('#skF_5', E_40)=k1_funct_1('#skF_6', E_40) | ~m1_subset_1(E_40, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_1470, plain, (![B_178]: (k1_funct_1('#skF_5', '#skF_2'('#skF_6', B_178))=k1_funct_1('#skF_6', '#skF_2'('#skF_6', B_178)) | B_178='#skF_6' | k1_relat_1(B_178)!='#skF_3' | ~v1_funct_1(B_178) | ~v1_relat_1(B_178))), inference(resolution, [status(thm)], [c_1094, c_50])).
% 4.69/1.86  tff(c_22, plain, (![B_17, A_13]: (k1_funct_1(B_17, '#skF_2'(A_13, B_17))!=k1_funct_1(A_13, '#skF_2'(A_13, B_17)) | B_17=A_13 | k1_relat_1(B_17)!=k1_relat_1(A_13) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.86  tff(c_1477, plain, (k1_relat_1('#skF_5')!=k1_relat_1('#skF_6') | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6') | '#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1470, c_22])).
% 4.69/1.86  tff(c_1484, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_62, c_878, c_155, c_56, c_884, c_878, c_1477])).
% 4.69/1.86  tff(c_48, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_141])).
% 4.69/1.86  tff(c_1498, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1484, c_48])).
% 4.69/1.86  tff(c_1508, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_1498])).
% 4.69/1.86  tff(c_1509, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_875])).
% 4.69/1.86  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.69/1.86  tff(c_1534, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_6])).
% 4.69/1.86  tff(c_1536, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_1534])).
% 4.69/1.86  tff(c_1537, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_872])).
% 4.69/1.86  tff(c_1562, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1537, c_6])).
% 4.69/1.86  tff(c_1564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_1562])).
% 4.69/1.86  tff(c_1566, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_108])).
% 4.69/1.86  tff(c_67, plain, (![B_44, A_45]: (~v1_xboole_0(B_44) | B_44=A_45 | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.69/1.86  tff(c_70, plain, (![A_45]: (k1_xboole_0=A_45 | ~v1_xboole_0(A_45))), inference(resolution, [status(thm)], [c_6, c_67])).
% 4.69/1.86  tff(c_1572, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1566, c_70])).
% 4.69/1.86  tff(c_44, plain, (![B_34, C_35]: (k1_relset_1(k1_xboole_0, B_34, C_35)=k1_xboole_0 | ~v1_funct_2(C_35, k1_xboole_0, B_34) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_34))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 4.69/1.86  tff(c_1659, plain, (![B_188, C_189]: (k1_relset_1('#skF_3', B_188, C_189)='#skF_3' | ~v1_funct_2(C_189, '#skF_3', B_188) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_188))))), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_1572, c_1572, c_1572, c_44])).
% 4.69/1.86  tff(c_1674, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')='#skF_3' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_1659])).
% 4.69/1.86  tff(c_1685, plain, (k1_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_271, c_1674])).
% 4.69/1.86  tff(c_1677, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_6')='#skF_3' | ~v1_funct_2('#skF_6', '#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_1659])).
% 4.69/1.86  tff(c_1688, plain, (k1_relat_1('#skF_6')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_54, c_272, c_1677])).
% 4.69/1.86  tff(c_2272, plain, (![A_241, B_242]: (r2_hidden('#skF_2'(A_241, B_242), k1_relat_1(A_241)) | B_242=A_241 | k1_relat_1(B_242)!=k1_relat_1(A_241) | ~v1_funct_1(B_242) | ~v1_relat_1(B_242) | ~v1_funct_1(A_241) | ~v1_relat_1(A_241))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.86  tff(c_2284, plain, (![B_242]: (r2_hidden('#skF_2'('#skF_6', B_242), '#skF_3') | B_242='#skF_6' | k1_relat_1(B_242)!=k1_relat_1('#skF_6') | ~v1_funct_1(B_242) | ~v1_relat_1(B_242) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1688, c_2272])).
% 4.69/1.86  tff(c_2325, plain, (![B_244]: (r2_hidden('#skF_2'('#skF_6', B_244), '#skF_3') | B_244='#skF_6' | k1_relat_1(B_244)!='#skF_3' | ~v1_funct_1(B_244) | ~v1_relat_1(B_244))), inference(demodulation, [status(thm), theory('equality')], [c_155, c_56, c_1688, c_2284])).
% 4.69/1.86  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.86  tff(c_2333, plain, (![B_244]: (~v1_xboole_0('#skF_3') | B_244='#skF_6' | k1_relat_1(B_244)!='#skF_3' | ~v1_funct_1(B_244) | ~v1_relat_1(B_244))), inference(resolution, [status(thm)], [c_2325, c_2])).
% 4.69/1.86  tff(c_2340, plain, (![B_245]: (B_245='#skF_6' | k1_relat_1(B_245)!='#skF_3' | ~v1_funct_1(B_245) | ~v1_relat_1(B_245))), inference(demodulation, [status(thm), theory('equality')], [c_1566, c_2333])).
% 4.69/1.86  tff(c_2352, plain, ('#skF_5'='#skF_6' | k1_relat_1('#skF_5')!='#skF_3' | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_154, c_2340])).
% 4.69/1.86  tff(c_2361, plain, ('#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1685, c_2352])).
% 4.69/1.86  tff(c_2373, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2361, c_48])).
% 4.69/1.86  tff(c_2383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_2373])).
% 4.69/1.86  tff(c_2385, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_178])).
% 4.69/1.86  tff(c_2398, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2385, c_70])).
% 4.69/1.86  tff(c_2384, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_178])).
% 4.69/1.86  tff(c_2391, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_2384, c_70])).
% 4.69/1.86  tff(c_2429, plain, ('#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2398, c_2391])).
% 4.69/1.86  tff(c_18, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.69/1.86  tff(c_2421, plain, (![A_9]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_2391, c_18])).
% 4.69/1.86  tff(c_2486, plain, (![A_253]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_253)))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_2421])).
% 4.69/1.86  tff(c_32, plain, (![A_29, B_30, D_32]: (r2_relset_1(A_29, B_30, D_32, D_32) | ~m1_subset_1(D_32, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.69/1.86  tff(c_2503, plain, (![A_29, B_30]: (r2_relset_1(A_29, B_30, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_2486, c_32])).
% 4.69/1.86  tff(c_179, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_52, c_157])).
% 4.69/1.86  tff(c_2447, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2385, c_179])).
% 4.69/1.86  tff(c_2420, plain, (![A_45]: (A_45='#skF_5' | ~v1_xboole_0(A_45))), inference(demodulation, [status(thm), theory('equality')], [c_2391, c_70])).
% 4.69/1.86  tff(c_2452, plain, (![A_249]: (A_249='#skF_4' | ~v1_xboole_0(A_249))), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_2420])).
% 4.69/1.86  tff(c_2459, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_2447, c_2452])).
% 4.69/1.86  tff(c_2438, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2429, c_48])).
% 4.69/1.86  tff(c_2512, plain, (~r2_relset_1('#skF_3', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2459, c_2438])).
% 4.69/1.86  tff(c_2515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2503, c_2512])).
% 4.69/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.69/1.86  
% 4.69/1.86  Inference rules
% 4.69/1.86  ----------------------
% 4.69/1.86  #Ref     : 1
% 4.69/1.86  #Sup     : 520
% 4.69/1.86  #Fact    : 0
% 4.69/1.86  #Define  : 0
% 4.69/1.86  #Split   : 14
% 4.69/1.86  #Chain   : 0
% 4.69/1.86  #Close   : 0
% 4.69/1.86  
% 4.69/1.86  Ordering : KBO
% 4.69/1.86  
% 4.69/1.86  Simplification rules
% 4.69/1.86  ----------------------
% 4.69/1.86  #Subsume      : 155
% 4.69/1.86  #Demod        : 399
% 4.69/1.86  #Tautology    : 204
% 4.69/1.86  #SimpNegUnit  : 82
% 4.69/1.86  #BackRed      : 101
% 4.69/1.86  
% 4.69/1.86  #Partial instantiations: 0
% 4.69/1.86  #Strategies tried      : 1
% 4.69/1.86  
% 4.69/1.86  Timing (in seconds)
% 4.69/1.86  ----------------------
% 4.69/1.86  Preprocessing        : 0.33
% 4.69/1.86  Parsing              : 0.17
% 4.69/1.86  CNF conversion       : 0.02
% 4.69/1.86  Main loop            : 0.70
% 4.69/1.86  Inferencing          : 0.23
% 4.69/1.86  Reduction            : 0.24
% 4.69/1.86  Demodulation         : 0.16
% 4.69/1.86  BG Simplification    : 0.03
% 4.69/1.86  Subsumption          : 0.13
% 4.69/1.86  Abstraction          : 0.03
% 4.69/1.86  MUC search           : 0.00
% 4.69/1.87  Cooper               : 0.00
% 4.69/1.87  Total                : 1.06
% 4.69/1.87  Index Insertion      : 0.00
% 4.69/1.87  Index Deletion       : 0.00
% 4.69/1.87  Index Matching       : 0.00
% 4.69/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
