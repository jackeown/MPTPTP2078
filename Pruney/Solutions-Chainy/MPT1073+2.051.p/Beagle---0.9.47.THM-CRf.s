%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:05 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 550 expanded)
%              Number of leaves         :   38 ( 208 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 (1653 expanded)
%              Number of equality atoms :   45 ( 644 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_60,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_12,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_58,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_91,plain,(
    ! [B_75,A_76] :
      ( v1_relat_1(B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_76))
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_98,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_58,c_91])).

tff(c_102,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_98])).

tff(c_62,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_16,plain,(
    ! [A_12,C_48] :
      ( k1_funct_1(A_12,'#skF_5'(A_12,k2_relat_1(A_12),C_48)) = C_48
      | ~ r2_hidden(C_48,k2_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_131,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_140,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_313,plain,(
    ! [B_117,A_118,C_119] :
      ( k1_xboole_0 = B_117
      | k1_relset_1(A_118,B_117,C_119) = A_118
      | ~ v1_funct_2(C_119,A_118,B_117)
      | ~ m1_subset_1(C_119,k1_zfmisc_1(k2_zfmisc_1(A_118,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_324,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_58,c_313])).

tff(c_329,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_140,c_324])).

tff(c_330,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_329])).

tff(c_18,plain,(
    ! [A_12,C_48] :
      ( r2_hidden('#skF_5'(A_12,k2_relat_1(A_12),C_48),k1_relat_1(A_12))
      | ~ r2_hidden(C_48,k2_relat_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_335,plain,(
    ! [C_48] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_48),'#skF_7')
      | ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_18])).

tff(c_360,plain,(
    ! [C_120] :
      ( r2_hidden('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_120),'#skF_7')
      | ~ r2_hidden(C_120,k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_62,c_335])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,B_6)
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_430,plain,(
    ! [C_128] :
      ( m1_subset_1('#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_128),'#skF_7')
      | ~ r2_hidden(C_128,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_360,c_8])).

tff(c_54,plain,(
    ! [E_65] :
      ( k1_funct_1('#skF_9',E_65) != '#skF_6'
      | ~ m1_subset_1(E_65,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_435,plain,(
    ! [C_129] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',k2_relat_1('#skF_9'),C_129)) != '#skF_6'
      | ~ r2_hidden(C_129,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_430,c_54])).

tff(c_439,plain,(
    ! [C_48] :
      ( C_48 != '#skF_6'
      | ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ r2_hidden(C_48,k2_relat_1('#skF_9'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_435])).

tff(c_442,plain,(
    ~ r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_62,c_439])).

tff(c_104,plain,(
    ! [A_78,B_79,C_80] :
      ( k2_relset_1(A_78,B_79,C_80) = k2_relat_1(C_80)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_78,B_79))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_113,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k2_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_58,c_104])).

tff(c_56,plain,(
    r2_hidden('#skF_6',k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_116,plain,(
    r2_hidden('#skF_6',k2_relat_1('#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_56])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_442,c_116])).

tff(c_445,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_452,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_6])).

tff(c_44,plain,(
    ! [C_63,A_61] :
      ( k1_xboole_0 = C_63
      | ~ v1_funct_2(C_63,A_61,k1_xboole_0)
      | k1_xboole_0 = A_61
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_524,plain,(
    ! [C_138,A_139] :
      ( C_138 = '#skF_8'
      | ~ v1_funct_2(C_138,A_139,'#skF_8')
      | A_139 = '#skF_8'
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_139,'#skF_8'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_445,c_445,c_445,c_44])).

tff(c_535,plain,
    ( '#skF_9' = '#skF_8'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8')
    | '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_58,c_524])).

tff(c_540,plain,
    ( '#skF_9' = '#skF_8'
    | '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_535])).

tff(c_541,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_540])).

tff(c_446,plain,(
    k1_relat_1('#skF_9') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_329])).

tff(c_542,plain,(
    k1_relat_1('#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_446])).

tff(c_549,plain,(
    v1_funct_2('#skF_9','#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_60])).

tff(c_544,plain,(
    k1_relset_1('#skF_8','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_140])).

tff(c_548,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_8','#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_541,c_58])).

tff(c_50,plain,(
    ! [B_62,C_63] :
      ( k1_relset_1(k1_xboole_0,B_62,C_63) = k1_xboole_0
      | ~ v1_funct_2(C_63,k1_xboole_0,B_62)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_603,plain,(
    ! [B_143,C_144] :
      ( k1_relset_1('#skF_8',B_143,C_144) = '#skF_8'
      | ~ v1_funct_2(C_144,'#skF_8',B_143)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1('#skF_8',B_143))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_445,c_445,c_445,c_50])).

tff(c_606,plain,
    ( k1_relset_1('#skF_8','#skF_8','#skF_9') = '#skF_8'
    | ~ v1_funct_2('#skF_9','#skF_8','#skF_8') ),
    inference(resolution,[status(thm)],[c_548,c_603])).

tff(c_617,plain,(
    k1_relat_1('#skF_9') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_544,c_606])).

tff(c_619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_542,c_617])).

tff(c_620,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_540])).

tff(c_275,plain,(
    ! [A_113,C_114] :
      ( r2_hidden('#skF_5'(A_113,k2_relat_1(A_113),C_114),k1_relat_1(A_113))
      | ~ r2_hidden(C_114,k2_relat_1(A_113))
      | ~ v1_funct_1(A_113)
      | ~ v1_relat_1(A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_176,plain,(
    ! [A_102,C_103] :
      ( r2_hidden(k4_tarski(A_102,k1_funct_1(C_103,A_102)),C_103)
      | ~ r2_hidden(A_102,k1_relat_1(C_103))
      | ~ v1_funct_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_198,plain,(
    ! [C_103,A_102] :
      ( ~ v1_xboole_0(C_103)
      | ~ r2_hidden(A_102,k1_relat_1(C_103))
      | ~ v1_funct_1(C_103)
      | ~ v1_relat_1(C_103) ) ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_292,plain,(
    ! [A_115,C_116] :
      ( ~ v1_xboole_0(A_115)
      | ~ r2_hidden(C_116,k2_relat_1(A_115))
      | ~ v1_funct_1(A_115)
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_275,c_198])).

tff(c_302,plain,
    ( ~ v1_xboole_0('#skF_9')
    | ~ v1_funct_1('#skF_9')
    | ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_116,c_292])).

tff(c_311,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_62,c_302])).

tff(c_624,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_620,c_311])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_624])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:27:51 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  
% 2.87/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.87/1.44  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_9 > #skF_8 > #skF_2 > #skF_4
% 2.87/1.44  
% 2.87/1.44  %Foreground sorts:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Background operators:
% 2.87/1.44  
% 2.87/1.44  
% 2.87/1.44  %Foreground operators:
% 2.87/1.44  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.87/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.44  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.87/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.87/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.44  tff('#skF_7', type, '#skF_7': $i).
% 2.87/1.44  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.87/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.87/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.87/1.44  tff('#skF_6', type, '#skF_6': $i).
% 2.87/1.44  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.87/1.44  tff('#skF_9', type, '#skF_9': $i).
% 2.87/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.87/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.87/1.44  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.87/1.44  tff('#skF_8', type, '#skF_8': $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.44  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.87/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.87/1.44  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.87/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.44  
% 3.18/1.46  tff(f_45, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.18/1.46  tff(f_112, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t190_funct_2)).
% 3.18/1.46  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.18/1.46  tff(f_60, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 3.18/1.46  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.18/1.46  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.18/1.46  tff(f_36, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 3.18/1.46  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.18/1.46  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.18/1.46  tff(f_70, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 3.18/1.46  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.18/1.46  tff(c_12, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.46  tff(c_58, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.18/1.46  tff(c_91, plain, (![B_75, A_76]: (v1_relat_1(B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_76)) | ~v1_relat_1(A_76))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.46  tff(c_98, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_58, c_91])).
% 3.18/1.46  tff(c_102, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_98])).
% 3.18/1.46  tff(c_62, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.18/1.46  tff(c_16, plain, (![A_12, C_48]: (k1_funct_1(A_12, '#skF_5'(A_12, k2_relat_1(A_12), C_48))=C_48 | ~r2_hidden(C_48, k2_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.46  tff(c_60, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.18/1.46  tff(c_131, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.18/1.46  tff(c_140, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_131])).
% 3.18/1.46  tff(c_313, plain, (![B_117, A_118, C_119]: (k1_xboole_0=B_117 | k1_relset_1(A_118, B_117, C_119)=A_118 | ~v1_funct_2(C_119, A_118, B_117) | ~m1_subset_1(C_119, k1_zfmisc_1(k2_zfmisc_1(A_118, B_117))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.46  tff(c_324, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_58, c_313])).
% 3.18/1.46  tff(c_329, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_140, c_324])).
% 3.18/1.46  tff(c_330, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_329])).
% 3.18/1.46  tff(c_18, plain, (![A_12, C_48]: (r2_hidden('#skF_5'(A_12, k2_relat_1(A_12), C_48), k1_relat_1(A_12)) | ~r2_hidden(C_48, k2_relat_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.46  tff(c_335, plain, (![C_48]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_48), '#skF_7') | ~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_330, c_18])).
% 3.18/1.46  tff(c_360, plain, (![C_120]: (r2_hidden('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_120), '#skF_7') | ~r2_hidden(C_120, k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_62, c_335])).
% 3.18/1.46  tff(c_8, plain, (![A_5, B_6]: (m1_subset_1(A_5, B_6) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.18/1.46  tff(c_430, plain, (![C_128]: (m1_subset_1('#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_128), '#skF_7') | ~r2_hidden(C_128, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_360, c_8])).
% 3.18/1.46  tff(c_54, plain, (![E_65]: (k1_funct_1('#skF_9', E_65)!='#skF_6' | ~m1_subset_1(E_65, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.18/1.46  tff(c_435, plain, (![C_129]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', k2_relat_1('#skF_9'), C_129))!='#skF_6' | ~r2_hidden(C_129, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_430, c_54])).
% 3.18/1.46  tff(c_439, plain, (![C_48]: (C_48!='#skF_6' | ~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~r2_hidden(C_48, k2_relat_1('#skF_9')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_435])).
% 3.18/1.46  tff(c_442, plain, (~r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_62, c_439])).
% 3.18/1.46  tff(c_104, plain, (![A_78, B_79, C_80]: (k2_relset_1(A_78, B_79, C_80)=k2_relat_1(C_80) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_78, B_79))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.46  tff(c_113, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k2_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_58, c_104])).
% 3.18/1.46  tff(c_56, plain, (r2_hidden('#skF_6', k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.18/1.46  tff(c_116, plain, (r2_hidden('#skF_6', k2_relat_1('#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_56])).
% 3.18/1.46  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_442, c_116])).
% 3.18/1.46  tff(c_445, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_329])).
% 3.18/1.46  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.18/1.46  tff(c_452, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_6])).
% 3.18/1.46  tff(c_44, plain, (![C_63, A_61]: (k1_xboole_0=C_63 | ~v1_funct_2(C_63, A_61, k1_xboole_0) | k1_xboole_0=A_61 | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.46  tff(c_524, plain, (![C_138, A_139]: (C_138='#skF_8' | ~v1_funct_2(C_138, A_139, '#skF_8') | A_139='#skF_8' | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_139, '#skF_8'))))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_445, c_445, c_445, c_44])).
% 3.18/1.46  tff(c_535, plain, ('#skF_9'='#skF_8' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8') | '#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_58, c_524])).
% 3.18/1.46  tff(c_540, plain, ('#skF_9'='#skF_8' | '#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_535])).
% 3.18/1.46  tff(c_541, plain, ('#skF_7'='#skF_8'), inference(splitLeft, [status(thm)], [c_540])).
% 3.18/1.46  tff(c_446, plain, (k1_relat_1('#skF_9')!='#skF_7'), inference(splitRight, [status(thm)], [c_329])).
% 3.18/1.46  tff(c_542, plain, (k1_relat_1('#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_541, c_446])).
% 3.18/1.46  tff(c_549, plain, (v1_funct_2('#skF_9', '#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_60])).
% 3.18/1.46  tff(c_544, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_541, c_140])).
% 3.18/1.46  tff(c_548, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_8', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_541, c_58])).
% 3.18/1.46  tff(c_50, plain, (![B_62, C_63]: (k1_relset_1(k1_xboole_0, B_62, C_63)=k1_xboole_0 | ~v1_funct_2(C_63, k1_xboole_0, B_62) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_62))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.46  tff(c_603, plain, (![B_143, C_144]: (k1_relset_1('#skF_8', B_143, C_144)='#skF_8' | ~v1_funct_2(C_144, '#skF_8', B_143) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1('#skF_8', B_143))))), inference(demodulation, [status(thm), theory('equality')], [c_445, c_445, c_445, c_445, c_50])).
% 3.18/1.46  tff(c_606, plain, (k1_relset_1('#skF_8', '#skF_8', '#skF_9')='#skF_8' | ~v1_funct_2('#skF_9', '#skF_8', '#skF_8')), inference(resolution, [status(thm)], [c_548, c_603])).
% 3.18/1.46  tff(c_617, plain, (k1_relat_1('#skF_9')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_549, c_544, c_606])).
% 3.18/1.46  tff(c_619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_542, c_617])).
% 3.18/1.46  tff(c_620, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_540])).
% 3.18/1.46  tff(c_275, plain, (![A_113, C_114]: (r2_hidden('#skF_5'(A_113, k2_relat_1(A_113), C_114), k1_relat_1(A_113)) | ~r2_hidden(C_114, k2_relat_1(A_113)) | ~v1_funct_1(A_113) | ~v1_relat_1(A_113))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.18/1.46  tff(c_176, plain, (![A_102, C_103]: (r2_hidden(k4_tarski(A_102, k1_funct_1(C_103, A_102)), C_103) | ~r2_hidden(A_102, k1_relat_1(C_103)) | ~v1_funct_1(C_103) | ~v1_relat_1(C_103))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.18/1.46  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.46  tff(c_198, plain, (![C_103, A_102]: (~v1_xboole_0(C_103) | ~r2_hidden(A_102, k1_relat_1(C_103)) | ~v1_funct_1(C_103) | ~v1_relat_1(C_103))), inference(resolution, [status(thm)], [c_176, c_2])).
% 3.18/1.46  tff(c_292, plain, (![A_115, C_116]: (~v1_xboole_0(A_115) | ~r2_hidden(C_116, k2_relat_1(A_115)) | ~v1_funct_1(A_115) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_275, c_198])).
% 3.18/1.46  tff(c_302, plain, (~v1_xboole_0('#skF_9') | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_116, c_292])).
% 3.18/1.46  tff(c_311, plain, (~v1_xboole_0('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_62, c_302])).
% 3.18/1.46  tff(c_624, plain, (~v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_620, c_311])).
% 3.18/1.46  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_452, c_624])).
% 3.18/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.46  
% 3.18/1.46  Inference rules
% 3.18/1.46  ----------------------
% 3.18/1.46  #Ref     : 0
% 3.18/1.46  #Sup     : 110
% 3.18/1.46  #Fact    : 0
% 3.18/1.46  #Define  : 0
% 3.18/1.46  #Split   : 5
% 3.18/1.46  #Chain   : 0
% 3.18/1.46  #Close   : 0
% 3.18/1.46  
% 3.18/1.46  Ordering : KBO
% 3.18/1.46  
% 3.18/1.46  Simplification rules
% 3.18/1.46  ----------------------
% 3.18/1.46  #Subsume      : 21
% 3.18/1.46  #Demod        : 96
% 3.18/1.46  #Tautology    : 30
% 3.18/1.46  #SimpNegUnit  : 2
% 3.18/1.46  #BackRed      : 33
% 3.18/1.46  
% 3.18/1.46  #Partial instantiations: 0
% 3.18/1.46  #Strategies tried      : 1
% 3.18/1.46  
% 3.18/1.46  Timing (in seconds)
% 3.18/1.46  ----------------------
% 3.24/1.47  Preprocessing        : 0.35
% 3.24/1.47  Parsing              : 0.17
% 3.24/1.47  CNF conversion       : 0.03
% 3.24/1.47  Main loop            : 0.35
% 3.24/1.47  Inferencing          : 0.13
% 3.24/1.47  Reduction            : 0.11
% 3.24/1.47  Demodulation         : 0.07
% 3.24/1.47  BG Simplification    : 0.02
% 3.24/1.47  Subsumption          : 0.06
% 3.24/1.47  Abstraction          : 0.02
% 3.24/1.47  MUC search           : 0.00
% 3.24/1.47  Cooper               : 0.00
% 3.24/1.47  Total                : 0.75
% 3.24/1.47  Index Insertion      : 0.00
% 3.24/1.47  Index Deletion       : 0.00
% 3.24/1.47  Index Matching       : 0.00
% 3.24/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
