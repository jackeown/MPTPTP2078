%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:36 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 154 expanded)
%              Number of leaves         :   37 (  70 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 373 expanded)
%              Number of equality atoms :   29 (  77 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ( m1_subset_1(F,A)
                 => ~ ( r2_hidden(F,C)
                      & E = k1_funct_1(D,F) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k9_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(E,k1_relat_1(A))
                  & r2_hidden(E,B)
                  & D = k1_funct_1(A,E) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_71,axiom,(
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

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_58,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_92,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_95,plain,(
    ! [D_89] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_89) = k9_relat_1('#skF_8',D_89) ),
    inference(resolution,[status(thm)],[c_58,c_92])).

tff(c_112,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( m1_subset_1(k7_relset_1(A_91,B_92,C_93,D_94),k1_zfmisc_1(B_92))
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_127,plain,(
    ! [D_89] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_89),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_112])).

tff(c_134,plain,(
    ! [D_95] : m1_subset_1(k9_relat_1('#skF_8',D_95),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_127])).

tff(c_6,plain,(
    ! [C_5,B_4,A_3] :
      ( ~ v1_xboole_0(C_5)
      | ~ m1_subset_1(B_4,k1_zfmisc_1(C_5))
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [A_3,D_95] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_3,k9_relat_1('#skF_8',D_95)) ) ),
    inference(resolution,[status(thm)],[c_134,c_6])).

tff(c_149,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_10,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_69,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(B_76)
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_77))
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_72,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_58,c_69])).

tff(c_75,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_72])).

tff(c_62,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_14,plain,(
    ! [A_11,B_34,D_49] :
      ( k1_funct_1(A_11,'#skF_4'(A_11,B_34,k9_relat_1(A_11,B_34),D_49)) = D_49
      | ~ r2_hidden(D_49,k9_relat_1(A_11,B_34))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_60,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_83,plain,(
    ! [A_83,B_84,C_85] :
      ( k1_relset_1(A_83,B_84,C_85) = k1_relat_1(C_85)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_87,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_83])).

tff(c_187,plain,(
    ! [B_114,A_115,C_116] :
      ( k1_xboole_0 = B_114
      | k1_relset_1(A_115,B_114,C_116) = A_115
      | ~ v1_funct_2(C_116,A_115,B_114)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_115,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_194,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_58,c_187])).

tff(c_198,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_87,c_194])).

tff(c_204,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_198])).

tff(c_277,plain,(
    ! [A_129,B_130,D_131] :
      ( r2_hidden('#skF_4'(A_129,B_130,k9_relat_1(A_129,B_130),D_131),k1_relat_1(A_129))
      | ~ r2_hidden(D_131,k9_relat_1(A_129,B_130))
      | ~ v1_funct_1(A_129)
      | ~ v1_relat_1(A_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_283,plain,(
    ! [B_130,D_131] :
      ( r2_hidden('#skF_4'('#skF_8',B_130,k9_relat_1('#skF_8',B_130),D_131),'#skF_5')
      | ~ r2_hidden(D_131,k9_relat_1('#skF_8',B_130))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_277])).

tff(c_287,plain,(
    ! [B_132,D_133] :
      ( r2_hidden('#skF_4'('#skF_8',B_132,k9_relat_1('#skF_8',B_132),D_133),'#skF_5')
      | ~ r2_hidden(D_133,k9_relat_1('#skF_8',B_132)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_62,c_283])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,B_2)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_291,plain,(
    ! [B_132,D_133] :
      ( m1_subset_1('#skF_4'('#skF_8',B_132,k9_relat_1('#skF_8',B_132),D_133),'#skF_5')
      | ~ r2_hidden(D_133,k9_relat_1('#skF_8',B_132)) ) ),
    inference(resolution,[status(thm)],[c_287,c_4])).

tff(c_214,plain,(
    ! [A_120,B_121,D_122] :
      ( r2_hidden('#skF_4'(A_120,B_121,k9_relat_1(A_120,B_121),D_122),B_121)
      | ~ r2_hidden(D_122,k9_relat_1(A_120,B_121))
      | ~ v1_funct_1(A_120)
      | ~ v1_relat_1(A_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_54,plain,(
    ! [F_71] :
      ( k1_funct_1('#skF_8',F_71) != '#skF_9'
      | ~ r2_hidden(F_71,'#skF_7')
      | ~ m1_subset_1(F_71,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1594,plain,(
    ! [A_247,D_248] :
      ( k1_funct_1('#skF_8','#skF_4'(A_247,'#skF_7',k9_relat_1(A_247,'#skF_7'),D_248)) != '#skF_9'
      | ~ m1_subset_1('#skF_4'(A_247,'#skF_7',k9_relat_1(A_247,'#skF_7'),D_248),'#skF_5')
      | ~ r2_hidden(D_248,k9_relat_1(A_247,'#skF_7'))
      | ~ v1_funct_1(A_247)
      | ~ v1_relat_1(A_247) ) ),
    inference(resolution,[status(thm)],[c_214,c_54])).

tff(c_1598,plain,(
    ! [D_133] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_133)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_133,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_291,c_1594])).

tff(c_1602,plain,(
    ! [D_249] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_249)) != '#skF_9'
      | ~ r2_hidden(D_249,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_62,c_1598])).

tff(c_1606,plain,(
    ! [D_49] :
      ( D_49 != '#skF_9'
      | ~ r2_hidden(D_49,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_49,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1602])).

tff(c_1609,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_62,c_1606])).

tff(c_56,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_97,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_56])).

tff(c_1611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1609,c_97])).

tff(c_1612,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_198])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_1620,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1612,c_2])).

tff(c_1622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_1620])).

tff(c_1623,plain,(
    ! [A_3,D_95] : ~ r2_hidden(A_3,k9_relat_1('#skF_8',D_95)) ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_1626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1623,c_97])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:45:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.68  
% 3.90/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.68  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.90/1.68  
% 3.90/1.68  %Foreground sorts:
% 3.90/1.68  
% 3.90/1.68  
% 3.90/1.68  %Background operators:
% 3.90/1.68  
% 3.90/1.68  
% 3.90/1.68  %Foreground operators:
% 3.90/1.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.90/1.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.90/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.90/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.90/1.68  tff('#skF_7', type, '#skF_7': $i).
% 3.90/1.68  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.90/1.68  tff('#skF_5', type, '#skF_5': $i).
% 3.90/1.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.90/1.68  tff('#skF_6', type, '#skF_6': $i).
% 3.90/1.68  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.90/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.90/1.68  tff('#skF_9', type, '#skF_9': $i).
% 3.90/1.68  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.90/1.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.68  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.90/1.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.90/1.68  tff('#skF_8', type, '#skF_8': $i).
% 3.90/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.90/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.90/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.90/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.90/1.68  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.90/1.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.68  
% 4.17/1.70  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t116_funct_2)).
% 4.17/1.70  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.17/1.70  tff(f_67, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 4.17/1.70  tff(f_37, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 4.17/1.70  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.17/1.70  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.17/1.70  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 4.17/1.70  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.17/1.70  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.17/1.70  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.17/1.70  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.17/1.70  tff(c_58, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.17/1.70  tff(c_92, plain, (![A_86, B_87, C_88, D_89]: (k7_relset_1(A_86, B_87, C_88, D_89)=k9_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.17/1.70  tff(c_95, plain, (![D_89]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_89)=k9_relat_1('#skF_8', D_89))), inference(resolution, [status(thm)], [c_58, c_92])).
% 4.17/1.70  tff(c_112, plain, (![A_91, B_92, C_93, D_94]: (m1_subset_1(k7_relset_1(A_91, B_92, C_93, D_94), k1_zfmisc_1(B_92)) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.17/1.70  tff(c_127, plain, (![D_89]: (m1_subset_1(k9_relat_1('#skF_8', D_89), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_95, c_112])).
% 4.17/1.70  tff(c_134, plain, (![D_95]: (m1_subset_1(k9_relat_1('#skF_8', D_95), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_127])).
% 4.17/1.70  tff(c_6, plain, (![C_5, B_4, A_3]: (~v1_xboole_0(C_5) | ~m1_subset_1(B_4, k1_zfmisc_1(C_5)) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.17/1.70  tff(c_140, plain, (![A_3, D_95]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_3, k9_relat_1('#skF_8', D_95)))), inference(resolution, [status(thm)], [c_134, c_6])).
% 4.17/1.70  tff(c_149, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_140])).
% 4.17/1.70  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.17/1.70  tff(c_69, plain, (![B_76, A_77]: (v1_relat_1(B_76) | ~m1_subset_1(B_76, k1_zfmisc_1(A_77)) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.17/1.70  tff(c_72, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_58, c_69])).
% 4.17/1.70  tff(c_75, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_72])).
% 4.17/1.70  tff(c_62, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.17/1.70  tff(c_14, plain, (![A_11, B_34, D_49]: (k1_funct_1(A_11, '#skF_4'(A_11, B_34, k9_relat_1(A_11, B_34), D_49))=D_49 | ~r2_hidden(D_49, k9_relat_1(A_11, B_34)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/1.70  tff(c_60, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.17/1.70  tff(c_83, plain, (![A_83, B_84, C_85]: (k1_relset_1(A_83, B_84, C_85)=k1_relat_1(C_85) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.17/1.70  tff(c_87, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_58, c_83])).
% 4.17/1.70  tff(c_187, plain, (![B_114, A_115, C_116]: (k1_xboole_0=B_114 | k1_relset_1(A_115, B_114, C_116)=A_115 | ~v1_funct_2(C_116, A_115, B_114) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_115, B_114))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.17/1.70  tff(c_194, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_58, c_187])).
% 4.17/1.70  tff(c_198, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_87, c_194])).
% 4.17/1.70  tff(c_204, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_198])).
% 4.17/1.70  tff(c_277, plain, (![A_129, B_130, D_131]: (r2_hidden('#skF_4'(A_129, B_130, k9_relat_1(A_129, B_130), D_131), k1_relat_1(A_129)) | ~r2_hidden(D_131, k9_relat_1(A_129, B_130)) | ~v1_funct_1(A_129) | ~v1_relat_1(A_129))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/1.70  tff(c_283, plain, (![B_130, D_131]: (r2_hidden('#skF_4'('#skF_8', B_130, k9_relat_1('#skF_8', B_130), D_131), '#skF_5') | ~r2_hidden(D_131, k9_relat_1('#skF_8', B_130)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_204, c_277])).
% 4.17/1.70  tff(c_287, plain, (![B_132, D_133]: (r2_hidden('#skF_4'('#skF_8', B_132, k9_relat_1('#skF_8', B_132), D_133), '#skF_5') | ~r2_hidden(D_133, k9_relat_1('#skF_8', B_132)))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_62, c_283])).
% 4.17/1.70  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, B_2) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 4.17/1.70  tff(c_291, plain, (![B_132, D_133]: (m1_subset_1('#skF_4'('#skF_8', B_132, k9_relat_1('#skF_8', B_132), D_133), '#skF_5') | ~r2_hidden(D_133, k9_relat_1('#skF_8', B_132)))), inference(resolution, [status(thm)], [c_287, c_4])).
% 4.17/1.70  tff(c_214, plain, (![A_120, B_121, D_122]: (r2_hidden('#skF_4'(A_120, B_121, k9_relat_1(A_120, B_121), D_122), B_121) | ~r2_hidden(D_122, k9_relat_1(A_120, B_121)) | ~v1_funct_1(A_120) | ~v1_relat_1(A_120))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.17/1.70  tff(c_54, plain, (![F_71]: (k1_funct_1('#skF_8', F_71)!='#skF_9' | ~r2_hidden(F_71, '#skF_7') | ~m1_subset_1(F_71, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.17/1.70  tff(c_1594, plain, (![A_247, D_248]: (k1_funct_1('#skF_8', '#skF_4'(A_247, '#skF_7', k9_relat_1(A_247, '#skF_7'), D_248))!='#skF_9' | ~m1_subset_1('#skF_4'(A_247, '#skF_7', k9_relat_1(A_247, '#skF_7'), D_248), '#skF_5') | ~r2_hidden(D_248, k9_relat_1(A_247, '#skF_7')) | ~v1_funct_1(A_247) | ~v1_relat_1(A_247))), inference(resolution, [status(thm)], [c_214, c_54])).
% 4.17/1.70  tff(c_1598, plain, (![D_133]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_133))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_133, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_291, c_1594])).
% 4.17/1.70  tff(c_1602, plain, (![D_249]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_249))!='#skF_9' | ~r2_hidden(D_249, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_62, c_1598])).
% 4.17/1.70  tff(c_1606, plain, (![D_49]: (D_49!='#skF_9' | ~r2_hidden(D_49, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_49, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1602])).
% 4.17/1.70  tff(c_1609, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_62, c_1606])).
% 4.17/1.70  tff(c_56, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.17/1.70  tff(c_97, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_56])).
% 4.17/1.70  tff(c_1611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1609, c_97])).
% 4.17/1.70  tff(c_1612, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_198])).
% 4.17/1.70  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 4.17/1.70  tff(c_1620, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1612, c_2])).
% 4.17/1.70  tff(c_1622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149, c_1620])).
% 4.17/1.70  tff(c_1623, plain, (![A_3, D_95]: (~r2_hidden(A_3, k9_relat_1('#skF_8', D_95)))), inference(splitRight, [status(thm)], [c_140])).
% 4.17/1.70  tff(c_1626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1623, c_97])).
% 4.17/1.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.70  
% 4.17/1.70  Inference rules
% 4.17/1.70  ----------------------
% 4.17/1.70  #Ref     : 0
% 4.17/1.70  #Sup     : 327
% 4.17/1.70  #Fact    : 0
% 4.17/1.70  #Define  : 0
% 4.17/1.70  #Split   : 4
% 4.17/1.70  #Chain   : 0
% 4.17/1.70  #Close   : 0
% 4.17/1.70  
% 4.17/1.70  Ordering : KBO
% 4.17/1.70  
% 4.17/1.70  Simplification rules
% 4.17/1.70  ----------------------
% 4.17/1.70  #Subsume      : 13
% 4.17/1.70  #Demod        : 55
% 4.17/1.70  #Tautology    : 18
% 4.17/1.70  #SimpNegUnit  : 3
% 4.17/1.70  #BackRed      : 12
% 4.17/1.70  
% 4.17/1.70  #Partial instantiations: 0
% 4.17/1.70  #Strategies tried      : 1
% 4.17/1.70  
% 4.17/1.70  Timing (in seconds)
% 4.17/1.70  ----------------------
% 4.17/1.70  Preprocessing        : 0.34
% 4.17/1.70  Parsing              : 0.17
% 4.17/1.70  CNF conversion       : 0.03
% 4.17/1.70  Main loop            : 0.59
% 4.17/1.70  Inferencing          : 0.22
% 4.17/1.70  Reduction            : 0.16
% 4.17/1.70  Demodulation         : 0.11
% 4.17/1.70  BG Simplification    : 0.04
% 4.17/1.70  Subsumption          : 0.11
% 4.17/1.70  Abstraction          : 0.05
% 4.17/1.70  MUC search           : 0.00
% 4.17/1.70  Cooper               : 0.00
% 4.17/1.70  Total                : 0.96
% 4.17/1.70  Index Insertion      : 0.00
% 4.17/1.70  Index Deletion       : 0.00
% 4.17/1.70  Index Matching       : 0.00
% 4.17/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
