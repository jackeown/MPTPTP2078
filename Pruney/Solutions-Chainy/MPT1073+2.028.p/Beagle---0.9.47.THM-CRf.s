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
% DateTime   : Thu Dec  3 10:18:01 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 357 expanded)
%              Number of leaves         :   43 ( 143 expanded)
%              Depth                    :   12
%              Number of atoms          :  186 ( 962 expanded)
%              Number of equality atoms :   53 ( 310 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4

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

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_71,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
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

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_10',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_9'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1198,plain,(
    ! [A_234,B_235,C_236] :
      ( k2_relset_1(A_234,B_235,C_236) = k2_relat_1(C_236)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1214,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_1198])).

tff(c_68,plain,(
    r2_hidden('#skF_7',k2_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_79,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_8','#skF_9','#skF_10')) ),
    inference(resolution,[status(thm)],[c_68,c_2])).

tff(c_1216,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1214,c_79])).

tff(c_102,plain,(
    ! [C_82,A_83,B_84] :
      ( v1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_111,plain,(
    v1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_102])).

tff(c_74,plain,(
    v1_funct_1('#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_26,plain,(
    ! [A_13,C_49] :
      ( k1_funct_1(A_13,'#skF_6'(A_13,k2_relat_1(A_13),C_49)) = C_49
      | ~ r2_hidden(C_49,k2_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_91,plain,(
    ! [B_80,A_81] :
      ( m1_subset_1(B_80,A_81)
      | ~ v1_xboole_0(B_80)
      | ~ v1_xboole_0(A_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_66,plain,(
    ! [E_73] :
      ( k1_funct_1('#skF_10',E_73) != '#skF_7'
      | ~ m1_subset_1(E_73,'#skF_8') ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_99,plain,(
    ! [B_80] :
      ( k1_funct_1('#skF_10',B_80) != '#skF_7'
      | ~ v1_xboole_0(B_80)
      | ~ v1_xboole_0('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_91,c_66])).

tff(c_152,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_99])).

tff(c_72,plain,(
    v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_195,plain,(
    ! [A_97,B_98,C_99] :
      ( k1_relset_1(A_97,B_98,C_99) = k1_relat_1(C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_211,plain,(
    k1_relset_1('#skF_8','#skF_9','#skF_10') = k1_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_195])).

tff(c_921,plain,(
    ! [B_206,A_207,C_208] :
      ( k1_xboole_0 = B_206
      | k1_relset_1(A_207,B_206,C_208) = A_207
      | ~ v1_funct_2(C_208,A_207,B_206)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_207,B_206))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_932,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relset_1('#skF_8','#skF_9','#skF_10') = '#skF_8'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_70,c_921])).

tff(c_939,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_relat_1('#skF_10') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_211,c_932])).

tff(c_940,plain,(
    k1_relat_1('#skF_10') = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_939])).

tff(c_28,plain,(
    ! [A_13,C_49] :
      ( r2_hidden('#skF_6'(A_13,k2_relat_1(A_13),C_49),k1_relat_1(A_13))
      | ~ r2_hidden(C_49,k2_relat_1(A_13))
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_949,plain,(
    ! [C_49] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_49),'#skF_8')
      | ~ r2_hidden(C_49,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_940,c_28])).

tff(c_991,plain,(
    ! [C_212] :
      ( r2_hidden('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_212),'#skF_8')
      | ~ r2_hidden(C_212,k2_relat_1('#skF_10')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_74,c_949])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ r2_hidden(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_994,plain,(
    ! [C_212] :
      ( m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_212),'#skF_8')
      | v1_xboole_0('#skF_8')
      | ~ r2_hidden(C_212,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_991,c_8])).

tff(c_1047,plain,(
    ! [C_218] :
      ( m1_subset_1('#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_218),'#skF_8')
      | ~ r2_hidden(C_218,k2_relat_1('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_994])).

tff(c_1056,plain,(
    ! [C_219] :
      ( k1_funct_1('#skF_10','#skF_6'('#skF_10',k2_relat_1('#skF_10'),C_219)) != '#skF_7'
      | ~ r2_hidden(C_219,k2_relat_1('#skF_10')) ) ),
    inference(resolution,[status(thm)],[c_1047,c_66])).

tff(c_1060,plain,(
    ! [C_49] :
      ( C_49 != '#skF_7'
      | ~ r2_hidden(C_49,k2_relat_1('#skF_10'))
      | ~ r2_hidden(C_49,k2_relat_1('#skF_10'))
      | ~ v1_funct_1('#skF_10')
      | ~ v1_relat_1('#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1056])).

tff(c_1063,plain,(
    ~ r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_74,c_1060])).

tff(c_155,plain,(
    ! [A_92,B_93,C_94] :
      ( k2_relset_1(A_92,B_93,C_94) = k2_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_171,plain,(
    k2_relset_1('#skF_8','#skF_9','#skF_10') = k2_relat_1('#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_155])).

tff(c_174,plain,(
    r2_hidden('#skF_7',k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_68])).

tff(c_1065,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1063,c_174])).

tff(c_1066,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_939])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1073,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_6])).

tff(c_56,plain,(
    ! [C_71,A_69] :
      ( k1_xboole_0 = C_71
      | ~ v1_funct_2(C_71,A_69,k1_xboole_0)
      | k1_xboole_0 = A_69
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_69,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1085,plain,(
    ! [C_221,A_222] :
      ( C_221 = '#skF_9'
      | ~ v1_funct_2(C_221,A_222,'#skF_9')
      | A_222 = '#skF_9'
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_222,'#skF_9'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1066,c_1066,c_1066,c_1066,c_56])).

tff(c_1096,plain,
    ( '#skF_10' = '#skF_9'
    | ~ v1_funct_2('#skF_10','#skF_8','#skF_9')
    | '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_70,c_1085])).

tff(c_1103,plain,
    ( '#skF_10' = '#skF_9'
    | '#skF_9' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1096])).

tff(c_1104,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1103])).

tff(c_1113,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1104,c_1073])).

tff(c_1122,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_152,c_1113])).

tff(c_1123,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1103])).

tff(c_173,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_79])).

tff(c_232,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k7_relset_1(A_104,B_105,C_106,D_107) = k9_relat_1(C_106,D_107)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_245,plain,(
    ! [D_107] : k7_relset_1('#skF_8','#skF_9','#skF_10',D_107) = k9_relat_1('#skF_10',D_107) ),
    inference(resolution,[status(thm)],[c_70,c_232])).

tff(c_452,plain,(
    ! [A_153,B_154,C_155] :
      ( k7_relset_1(A_153,B_154,C_155,A_153) = k2_relset_1(A_153,B_154,C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_460,plain,(
    k7_relset_1('#skF_8','#skF_9','#skF_10','#skF_8') = k2_relset_1('#skF_8','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_452])).

tff(c_466,plain,(
    k9_relat_1('#skF_10','#skF_8') = k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_245,c_171,c_460])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_358,plain,(
    ! [A_136,B_137,C_138] :
      ( r2_hidden(k4_tarski('#skF_2'(A_136,B_137,C_138),A_136),C_138)
      | ~ r2_hidden(A_136,k9_relat_1(C_138,B_137))
      | ~ v1_relat_1(C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_387,plain,(
    ! [C_139,A_140,B_141] :
      ( ~ v1_xboole_0(C_139)
      | ~ r2_hidden(A_140,k9_relat_1(C_139,B_141))
      | ~ v1_relat_1(C_139) ) ),
    inference(resolution,[status(thm)],[c_358,c_2])).

tff(c_407,plain,(
    ! [C_139,B_141] :
      ( ~ v1_xboole_0(C_139)
      | ~ v1_relat_1(C_139)
      | v1_xboole_0(k9_relat_1(C_139,B_141)) ) ),
    inference(resolution,[status(thm)],[c_4,c_387])).

tff(c_479,plain,
    ( ~ v1_xboole_0('#skF_10')
    | ~ v1_relat_1('#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_407])).

tff(c_511,plain,
    ( ~ v1_xboole_0('#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_479])).

tff(c_512,plain,(
    ~ v1_xboole_0('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_511])).

tff(c_1138,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_512])).

tff(c_1154,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1073,c_1138])).

tff(c_1156,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_99])).

tff(c_1344,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( k7_relset_1(A_265,B_266,C_267,D_268) = k9_relat_1(C_267,D_268)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1357,plain,(
    ! [D_268] : k7_relset_1('#skF_8','#skF_9','#skF_10',D_268) = k9_relat_1('#skF_10',D_268) ),
    inference(resolution,[status(thm)],[c_70,c_1344])).

tff(c_1428,plain,(
    ! [A_290,B_291,C_292] :
      ( k7_relset_1(A_290,B_291,C_292,A_290) = k2_relset_1(A_290,B_291,C_292)
      | ~ m1_subset_1(C_292,k1_zfmisc_1(k2_zfmisc_1(A_290,B_291))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1436,plain,(
    k7_relset_1('#skF_8','#skF_9','#skF_10','#skF_8') = k2_relset_1('#skF_8','#skF_9','#skF_10') ),
    inference(resolution,[status(thm)],[c_70,c_1428])).

tff(c_1442,plain,(
    k9_relat_1('#skF_10','#skF_8') = k2_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1357,c_1214,c_1436])).

tff(c_1236,plain,(
    ! [A_237,B_238,C_239] :
      ( r2_hidden('#skF_2'(A_237,B_238,C_239),B_238)
      | ~ r2_hidden(A_237,k9_relat_1(C_239,B_238))
      | ~ v1_relat_1(C_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1245,plain,(
    ! [B_240,A_241,C_242] :
      ( ~ v1_xboole_0(B_240)
      | ~ r2_hidden(A_241,k9_relat_1(C_242,B_240))
      | ~ v1_relat_1(C_242) ) ),
    inference(resolution,[status(thm)],[c_1236,c_2])).

tff(c_1260,plain,(
    ! [B_240,C_242] :
      ( ~ v1_xboole_0(B_240)
      | ~ v1_relat_1(C_242)
      | v1_xboole_0(k9_relat_1(C_242,B_240)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1245])).

tff(c_1477,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_relat_1('#skF_10')
    | v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1442,c_1260])).

tff(c_1508,plain,(
    v1_xboole_0(k2_relat_1('#skF_10')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_1156,c_1477])).

tff(c_1510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1216,c_1508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:36:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.70/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.60  
% 3.70/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.60  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_4
% 3.70/1.60  
% 3.70/1.60  %Foreground sorts:
% 3.70/1.60  
% 3.70/1.60  
% 3.70/1.60  %Background operators:
% 3.70/1.60  
% 3.70/1.60  
% 3.70/1.60  %Foreground operators:
% 3.70/1.60  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.70/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.70/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.70/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.70/1.60  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.70/1.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.70/1.60  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.70/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.70/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.70/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.70/1.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.70/1.60  tff('#skF_10', type, '#skF_10': $i).
% 3.70/1.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.70/1.60  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.70/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.70/1.60  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.70/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.70/1.60  tff('#skF_9', type, '#skF_9': $i).
% 3.70/1.60  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.70/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.70/1.60  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.70/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.70/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.70/1.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.70/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.70/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.70/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.70/1.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.70/1.60  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.70/1.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.70/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.70/1.60  
% 3.70/1.62  tff(f_127, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 3.70/1.62  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.70/1.62  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.70/1.62  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.70/1.62  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.70/1.62  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.70/1.62  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.70/1.62  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.70/1.62  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.70/1.62  tff(f_87, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.70/1.62  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 3.70/1.62  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 3.70/1.62  tff(c_70, plain, (m1_subset_1('#skF_10', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_9')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.70/1.62  tff(c_1198, plain, (![A_234, B_235, C_236]: (k2_relset_1(A_234, B_235, C_236)=k2_relat_1(C_236) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.70/1.62  tff(c_1214, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_1198])).
% 3.70/1.62  tff(c_68, plain, (r2_hidden('#skF_7', k2_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.70/1.62  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.62  tff(c_79, plain, (~v1_xboole_0(k2_relset_1('#skF_8', '#skF_9', '#skF_10'))), inference(resolution, [status(thm)], [c_68, c_2])).
% 3.70/1.62  tff(c_1216, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_1214, c_79])).
% 3.70/1.62  tff(c_102, plain, (![C_82, A_83, B_84]: (v1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.70/1.62  tff(c_111, plain, (v1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_102])).
% 3.70/1.62  tff(c_74, plain, (v1_funct_1('#skF_10')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.70/1.62  tff(c_26, plain, (![A_13, C_49]: (k1_funct_1(A_13, '#skF_6'(A_13, k2_relat_1(A_13), C_49))=C_49 | ~r2_hidden(C_49, k2_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.62  tff(c_91, plain, (![B_80, A_81]: (m1_subset_1(B_80, A_81) | ~v1_xboole_0(B_80) | ~v1_xboole_0(A_81))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.70/1.62  tff(c_66, plain, (![E_73]: (k1_funct_1('#skF_10', E_73)!='#skF_7' | ~m1_subset_1(E_73, '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.70/1.62  tff(c_99, plain, (![B_80]: (k1_funct_1('#skF_10', B_80)!='#skF_7' | ~v1_xboole_0(B_80) | ~v1_xboole_0('#skF_8'))), inference(resolution, [status(thm)], [c_91, c_66])).
% 3.70/1.62  tff(c_152, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_99])).
% 3.70/1.62  tff(c_72, plain, (v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.70/1.62  tff(c_195, plain, (![A_97, B_98, C_99]: (k1_relset_1(A_97, B_98, C_99)=k1_relat_1(C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.70/1.62  tff(c_211, plain, (k1_relset_1('#skF_8', '#skF_9', '#skF_10')=k1_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_195])).
% 3.70/1.62  tff(c_921, plain, (![B_206, A_207, C_208]: (k1_xboole_0=B_206 | k1_relset_1(A_207, B_206, C_208)=A_207 | ~v1_funct_2(C_208, A_207, B_206) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_207, B_206))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.70/1.62  tff(c_932, plain, (k1_xboole_0='#skF_9' | k1_relset_1('#skF_8', '#skF_9', '#skF_10')='#skF_8' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_70, c_921])).
% 3.70/1.62  tff(c_939, plain, (k1_xboole_0='#skF_9' | k1_relat_1('#skF_10')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_211, c_932])).
% 3.70/1.62  tff(c_940, plain, (k1_relat_1('#skF_10')='#skF_8'), inference(splitLeft, [status(thm)], [c_939])).
% 3.70/1.62  tff(c_28, plain, (![A_13, C_49]: (r2_hidden('#skF_6'(A_13, k2_relat_1(A_13), C_49), k1_relat_1(A_13)) | ~r2_hidden(C_49, k2_relat_1(A_13)) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.70/1.62  tff(c_949, plain, (![C_49]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_49), '#skF_8') | ~r2_hidden(C_49, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_940, c_28])).
% 3.70/1.62  tff(c_991, plain, (![C_212]: (r2_hidden('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_212), '#skF_8') | ~r2_hidden(C_212, k2_relat_1('#skF_10')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_74, c_949])).
% 3.70/1.62  tff(c_8, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~r2_hidden(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.70/1.62  tff(c_994, plain, (![C_212]: (m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_212), '#skF_8') | v1_xboole_0('#skF_8') | ~r2_hidden(C_212, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_991, c_8])).
% 3.70/1.62  tff(c_1047, plain, (![C_218]: (m1_subset_1('#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_218), '#skF_8') | ~r2_hidden(C_218, k2_relat_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_152, c_994])).
% 3.70/1.62  tff(c_1056, plain, (![C_219]: (k1_funct_1('#skF_10', '#skF_6'('#skF_10', k2_relat_1('#skF_10'), C_219))!='#skF_7' | ~r2_hidden(C_219, k2_relat_1('#skF_10')))), inference(resolution, [status(thm)], [c_1047, c_66])).
% 3.70/1.62  tff(c_1060, plain, (![C_49]: (C_49!='#skF_7' | ~r2_hidden(C_49, k2_relat_1('#skF_10')) | ~r2_hidden(C_49, k2_relat_1('#skF_10')) | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1056])).
% 3.70/1.62  tff(c_1063, plain, (~r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_74, c_1060])).
% 3.70/1.62  tff(c_155, plain, (![A_92, B_93, C_94]: (k2_relset_1(A_92, B_93, C_94)=k2_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.70/1.62  tff(c_171, plain, (k2_relset_1('#skF_8', '#skF_9', '#skF_10')=k2_relat_1('#skF_10')), inference(resolution, [status(thm)], [c_70, c_155])).
% 3.70/1.62  tff(c_174, plain, (r2_hidden('#skF_7', k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_68])).
% 3.70/1.62  tff(c_1065, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1063, c_174])).
% 3.70/1.62  tff(c_1066, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_939])).
% 3.70/1.62  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.70/1.62  tff(c_1073, plain, (v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_6])).
% 3.70/1.62  tff(c_56, plain, (![C_71, A_69]: (k1_xboole_0=C_71 | ~v1_funct_2(C_71, A_69, k1_xboole_0) | k1_xboole_0=A_69 | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_69, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.70/1.62  tff(c_1085, plain, (![C_221, A_222]: (C_221='#skF_9' | ~v1_funct_2(C_221, A_222, '#skF_9') | A_222='#skF_9' | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_222, '#skF_9'))))), inference(demodulation, [status(thm), theory('equality')], [c_1066, c_1066, c_1066, c_1066, c_56])).
% 3.70/1.62  tff(c_1096, plain, ('#skF_10'='#skF_9' | ~v1_funct_2('#skF_10', '#skF_8', '#skF_9') | '#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_70, c_1085])).
% 3.70/1.62  tff(c_1103, plain, ('#skF_10'='#skF_9' | '#skF_9'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1096])).
% 3.70/1.62  tff(c_1104, plain, ('#skF_9'='#skF_8'), inference(splitLeft, [status(thm)], [c_1103])).
% 3.70/1.62  tff(c_1113, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1104, c_1073])).
% 3.70/1.62  tff(c_1122, plain, $false, inference(negUnitSimplification, [status(thm)], [c_152, c_1113])).
% 3.70/1.62  tff(c_1123, plain, ('#skF_10'='#skF_9'), inference(splitRight, [status(thm)], [c_1103])).
% 3.70/1.62  tff(c_173, plain, (~v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_171, c_79])).
% 3.70/1.62  tff(c_232, plain, (![A_104, B_105, C_106, D_107]: (k7_relset_1(A_104, B_105, C_106, D_107)=k9_relat_1(C_106, D_107) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.70/1.62  tff(c_245, plain, (![D_107]: (k7_relset_1('#skF_8', '#skF_9', '#skF_10', D_107)=k9_relat_1('#skF_10', D_107))), inference(resolution, [status(thm)], [c_70, c_232])).
% 3.70/1.62  tff(c_452, plain, (![A_153, B_154, C_155]: (k7_relset_1(A_153, B_154, C_155, A_153)=k2_relset_1(A_153, B_154, C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.70/1.62  tff(c_460, plain, (k7_relset_1('#skF_8', '#skF_9', '#skF_10', '#skF_8')=k2_relset_1('#skF_8', '#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_70, c_452])).
% 3.70/1.62  tff(c_466, plain, (k9_relat_1('#skF_10', '#skF_8')=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_245, c_171, c_460])).
% 3.70/1.62  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.70/1.62  tff(c_358, plain, (![A_136, B_137, C_138]: (r2_hidden(k4_tarski('#skF_2'(A_136, B_137, C_138), A_136), C_138) | ~r2_hidden(A_136, k9_relat_1(C_138, B_137)) | ~v1_relat_1(C_138))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.70/1.62  tff(c_387, plain, (![C_139, A_140, B_141]: (~v1_xboole_0(C_139) | ~r2_hidden(A_140, k9_relat_1(C_139, B_141)) | ~v1_relat_1(C_139))), inference(resolution, [status(thm)], [c_358, c_2])).
% 3.70/1.62  tff(c_407, plain, (![C_139, B_141]: (~v1_xboole_0(C_139) | ~v1_relat_1(C_139) | v1_xboole_0(k9_relat_1(C_139, B_141)))), inference(resolution, [status(thm)], [c_4, c_387])).
% 3.70/1.62  tff(c_479, plain, (~v1_xboole_0('#skF_10') | ~v1_relat_1('#skF_10') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_466, c_407])).
% 3.70/1.62  tff(c_511, plain, (~v1_xboole_0('#skF_10') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_479])).
% 3.70/1.62  tff(c_512, plain, (~v1_xboole_0('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_173, c_511])).
% 3.70/1.62  tff(c_1138, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_512])).
% 3.70/1.62  tff(c_1154, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1073, c_1138])).
% 3.70/1.62  tff(c_1156, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_99])).
% 3.70/1.62  tff(c_1344, plain, (![A_265, B_266, C_267, D_268]: (k7_relset_1(A_265, B_266, C_267, D_268)=k9_relat_1(C_267, D_268) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.70/1.62  tff(c_1357, plain, (![D_268]: (k7_relset_1('#skF_8', '#skF_9', '#skF_10', D_268)=k9_relat_1('#skF_10', D_268))), inference(resolution, [status(thm)], [c_70, c_1344])).
% 3.70/1.62  tff(c_1428, plain, (![A_290, B_291, C_292]: (k7_relset_1(A_290, B_291, C_292, A_290)=k2_relset_1(A_290, B_291, C_292) | ~m1_subset_1(C_292, k1_zfmisc_1(k2_zfmisc_1(A_290, B_291))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.70/1.62  tff(c_1436, plain, (k7_relset_1('#skF_8', '#skF_9', '#skF_10', '#skF_8')=k2_relset_1('#skF_8', '#skF_9', '#skF_10')), inference(resolution, [status(thm)], [c_70, c_1428])).
% 3.70/1.62  tff(c_1442, plain, (k9_relat_1('#skF_10', '#skF_8')=k2_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_1357, c_1214, c_1436])).
% 3.70/1.62  tff(c_1236, plain, (![A_237, B_238, C_239]: (r2_hidden('#skF_2'(A_237, B_238, C_239), B_238) | ~r2_hidden(A_237, k9_relat_1(C_239, B_238)) | ~v1_relat_1(C_239))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.70/1.62  tff(c_1245, plain, (![B_240, A_241, C_242]: (~v1_xboole_0(B_240) | ~r2_hidden(A_241, k9_relat_1(C_242, B_240)) | ~v1_relat_1(C_242))), inference(resolution, [status(thm)], [c_1236, c_2])).
% 3.70/1.62  tff(c_1260, plain, (![B_240, C_242]: (~v1_xboole_0(B_240) | ~v1_relat_1(C_242) | v1_xboole_0(k9_relat_1(C_242, B_240)))), inference(resolution, [status(thm)], [c_4, c_1245])).
% 3.70/1.62  tff(c_1477, plain, (~v1_xboole_0('#skF_8') | ~v1_relat_1('#skF_10') | v1_xboole_0(k2_relat_1('#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_1442, c_1260])).
% 3.70/1.62  tff(c_1508, plain, (v1_xboole_0(k2_relat_1('#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_1156, c_1477])).
% 3.70/1.62  tff(c_1510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1216, c_1508])).
% 3.70/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.70/1.62  
% 3.70/1.62  Inference rules
% 3.70/1.62  ----------------------
% 3.70/1.62  #Ref     : 0
% 3.70/1.62  #Sup     : 272
% 3.70/1.62  #Fact    : 0
% 3.70/1.62  #Define  : 0
% 3.70/1.62  #Split   : 7
% 3.70/1.62  #Chain   : 0
% 3.70/1.62  #Close   : 0
% 3.70/1.62  
% 3.70/1.62  Ordering : KBO
% 3.70/1.62  
% 3.70/1.62  Simplification rules
% 3.70/1.62  ----------------------
% 3.70/1.62  #Subsume      : 75
% 3.70/1.62  #Demod        : 176
% 3.70/1.62  #Tautology    : 40
% 3.70/1.62  #SimpNegUnit  : 38
% 3.70/1.62  #BackRed      : 55
% 3.70/1.62  
% 3.70/1.62  #Partial instantiations: 0
% 3.70/1.62  #Strategies tried      : 1
% 3.70/1.62  
% 3.70/1.62  Timing (in seconds)
% 3.70/1.62  ----------------------
% 3.70/1.63  Preprocessing        : 0.35
% 3.70/1.63  Parsing              : 0.17
% 3.70/1.63  CNF conversion       : 0.03
% 3.70/1.63  Main loop            : 0.51
% 3.70/1.63  Inferencing          : 0.19
% 3.70/1.63  Reduction            : 0.14
% 3.70/1.63  Demodulation         : 0.09
% 3.70/1.63  BG Simplification    : 0.03
% 3.70/1.63  Subsumption          : 0.10
% 3.70/1.63  Abstraction          : 0.03
% 3.70/1.63  MUC search           : 0.00
% 3.70/1.63  Cooper               : 0.00
% 3.70/1.63  Total                : 0.90
% 3.70/1.63  Index Insertion      : 0.00
% 3.70/1.63  Index Deletion       : 0.00
% 3.70/1.63  Index Matching       : 0.00
% 3.70/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
