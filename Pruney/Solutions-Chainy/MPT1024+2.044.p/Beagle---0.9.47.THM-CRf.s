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
% DateTime   : Thu Dec  3 10:16:27 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 127 expanded)
%              Number of leaves         :   38 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  121 ( 304 expanded)
%              Number of equality atoms :   29 (  64 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ~ ( r2_hidden(E,k7_relset_1(A,B,D,C))
              & ! [F] :
                  ~ ( r2_hidden(F,A)
                    & r2_hidden(F,C)
                    & E = k1_funct_1(D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_77,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_60,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_133,plain,(
    ! [A_97,B_98,C_99,D_100] :
      ( m1_subset_1(k7_relset_1(A_97,B_98,C_99,D_100),k1_zfmisc_1(B_98))
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_58,plain,(
    r2_hidden('#skF_10',k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_89,plain,(
    ! [C_83,A_84,B_85] :
      ( r2_hidden(C_83,A_84)
      | ~ r2_hidden(C_83,B_85)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_94,plain,(
    ! [A_84] :
      ( r2_hidden('#skF_10',A_84)
      | ~ m1_subset_1(k7_relset_1('#skF_6','#skF_7','#skF_9','#skF_8'),k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_58,c_89])).

tff(c_145,plain,
    ( r2_hidden('#skF_10','#skF_7')
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(resolution,[status(thm)],[c_133,c_94])).

tff(c_156,plain,(
    r2_hidden('#skF_10','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_145])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_165,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_156,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,
    ( v1_relat_1('#skF_9')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_82])).

tff(c_88,plain,(
    v1_relat_1('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_85])).

tff(c_64,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_16,plain,(
    ! [A_14,B_37,D_52] :
      ( k1_funct_1(A_14,'#skF_5'(A_14,B_37,k9_relat_1(A_14,B_37),D_52)) = D_52
      | ~ r2_hidden(D_52,k9_relat_1(A_14,B_37))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [A_14,B_37,D_52] :
      ( r2_hidden('#skF_5'(A_14,B_37,k9_relat_1(A_14,B_37),D_52),B_37)
      | ~ r2_hidden(D_52,k9_relat_1(A_14,B_37))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_62,plain,(
    v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_123,plain,(
    ! [A_92,B_93,C_94] :
      ( k1_relset_1(A_92,B_93,C_94) = k1_relat_1(C_94)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_127,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_60,c_123])).

tff(c_300,plain,(
    ! [B_134,A_135,C_136] :
      ( k1_xboole_0 = B_134
      | k1_relset_1(A_135,B_134,C_136) = A_135
      | ~ v1_funct_2(C_136,A_135,B_134)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_135,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_307,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_9') = '#skF_6'
    | ~ v1_funct_2('#skF_9','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_300])).

tff(c_311,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_9') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_127,c_307])).

tff(c_312,plain,(
    k1_relat_1('#skF_9') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_424,plain,(
    ! [A_166,B_167,D_168] :
      ( r2_hidden('#skF_5'(A_166,B_167,k9_relat_1(A_166,B_167),D_168),k1_relat_1(A_166))
      | ~ r2_hidden(D_168,k9_relat_1(A_166,B_167))
      | ~ v1_funct_1(A_166)
      | ~ v1_relat_1(A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_432,plain,(
    ! [B_167,D_168] :
      ( r2_hidden('#skF_5'('#skF_9',B_167,k9_relat_1('#skF_9',B_167),D_168),'#skF_6')
      | ~ r2_hidden(D_168,k9_relat_1('#skF_9',B_167))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_424])).

tff(c_473,plain,(
    ! [B_174,D_175] :
      ( r2_hidden('#skF_5'('#skF_9',B_174,k9_relat_1('#skF_9',B_174),D_175),'#skF_6')
      | ~ r2_hidden(D_175,k9_relat_1('#skF_9',B_174)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_432])).

tff(c_56,plain,(
    ! [F_74] :
      ( k1_funct_1('#skF_9',F_74) != '#skF_10'
      | ~ r2_hidden(F_74,'#skF_8')
      | ~ r2_hidden(F_74,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_593,plain,(
    ! [B_192,D_193] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_192,k9_relat_1('#skF_9',B_192),D_193)) != '#skF_10'
      | ~ r2_hidden('#skF_5'('#skF_9',B_192,k9_relat_1('#skF_9',B_192),D_193),'#skF_8')
      | ~ r2_hidden(D_193,k9_relat_1('#skF_9',B_192)) ) ),
    inference(resolution,[status(thm)],[c_473,c_56])).

tff(c_601,plain,(
    ! [D_52] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_52)) != '#skF_10'
      | ~ r2_hidden(D_52,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_593])).

tff(c_607,plain,(
    ! [D_195] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9','#skF_8',k9_relat_1('#skF_9','#skF_8'),D_195)) != '#skF_10'
      | ~ r2_hidden(D_195,k9_relat_1('#skF_9','#skF_8')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_601])).

tff(c_611,plain,(
    ! [D_52] :
      ( D_52 != '#skF_10'
      | ~ r2_hidden(D_52,k9_relat_1('#skF_9','#skF_8'))
      | ~ r2_hidden(D_52,k9_relat_1('#skF_9','#skF_8'))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_607])).

tff(c_614,plain,(
    ~ r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_64,c_611])).

tff(c_179,plain,(
    ! [A_103,B_104,C_105,D_106] :
      ( k7_relset_1(A_103,B_104,C_105,D_106) = k9_relat_1(C_105,D_106)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_186,plain,(
    ! [D_106] : k7_relset_1('#skF_6','#skF_7','#skF_9',D_106) = k9_relat_1('#skF_9',D_106) ),
    inference(resolution,[status(thm)],[c_60,c_179])).

tff(c_189,plain,(
    r2_hidden('#skF_10',k9_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_58])).

tff(c_616,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_614,c_189])).

tff(c_617,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_625,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_6])).

tff(c_627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_625])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.48  
% 3.31/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.49  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_10 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 3.31/1.49  
% 3.31/1.49  %Foreground sorts:
% 3.31/1.49  
% 3.31/1.49  
% 3.31/1.49  %Background operators:
% 3.31/1.49  
% 3.31/1.49  
% 3.31/1.49  %Foreground operators:
% 3.31/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.31/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.31/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.31/1.49  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.31/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.31/1.49  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.31/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.31/1.49  tff('#skF_10', type, '#skF_10': $i).
% 3.31/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.31/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.31/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.31/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.31/1.49  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.31/1.49  tff('#skF_9', type, '#skF_9': $i).
% 3.31/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.31/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.31/1.49  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.31/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.31/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.31/1.49  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.31/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.31/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.31/1.49  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.31/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.31/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.31/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.31/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.31/1.49  
% 3.31/1.50  tff(f_114, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 3.31/1.50  tff(f_69, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.31/1.50  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.31/1.50  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.31/1.50  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.31/1.50  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.31/1.50  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 3.31/1.50  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.31/1.50  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.31/1.50  tff(f_77, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.31/1.50  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.31/1.50  tff(c_60, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.31/1.50  tff(c_133, plain, (![A_97, B_98, C_99, D_100]: (m1_subset_1(k7_relset_1(A_97, B_98, C_99, D_100), k1_zfmisc_1(B_98)) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.31/1.50  tff(c_58, plain, (r2_hidden('#skF_10', k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.31/1.50  tff(c_89, plain, (![C_83, A_84, B_85]: (r2_hidden(C_83, A_84) | ~r2_hidden(C_83, B_85) | ~m1_subset_1(B_85, k1_zfmisc_1(A_84)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.31/1.50  tff(c_94, plain, (![A_84]: (r2_hidden('#skF_10', A_84) | ~m1_subset_1(k7_relset_1('#skF_6', '#skF_7', '#skF_9', '#skF_8'), k1_zfmisc_1(A_84)))), inference(resolution, [status(thm)], [c_58, c_89])).
% 3.31/1.50  tff(c_145, plain, (r2_hidden('#skF_10', '#skF_7') | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_133, c_94])).
% 3.31/1.50  tff(c_156, plain, (r2_hidden('#skF_10', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_145])).
% 3.31/1.50  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.31/1.50  tff(c_165, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_156, c_2])).
% 3.31/1.50  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.31/1.50  tff(c_82, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.31/1.50  tff(c_85, plain, (v1_relat_1('#skF_9') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_82])).
% 3.31/1.50  tff(c_88, plain, (v1_relat_1('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_85])).
% 3.31/1.50  tff(c_64, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.31/1.50  tff(c_16, plain, (![A_14, B_37, D_52]: (k1_funct_1(A_14, '#skF_5'(A_14, B_37, k9_relat_1(A_14, B_37), D_52))=D_52 | ~r2_hidden(D_52, k9_relat_1(A_14, B_37)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.50  tff(c_18, plain, (![A_14, B_37, D_52]: (r2_hidden('#skF_5'(A_14, B_37, k9_relat_1(A_14, B_37), D_52), B_37) | ~r2_hidden(D_52, k9_relat_1(A_14, B_37)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.50  tff(c_62, plain, (v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.31/1.50  tff(c_123, plain, (![A_92, B_93, C_94]: (k1_relset_1(A_92, B_93, C_94)=k1_relat_1(C_94) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.31/1.50  tff(c_127, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_60, c_123])).
% 3.31/1.50  tff(c_300, plain, (![B_134, A_135, C_136]: (k1_xboole_0=B_134 | k1_relset_1(A_135, B_134, C_136)=A_135 | ~v1_funct_2(C_136, A_135, B_134) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_135, B_134))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.31/1.50  tff(c_307, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_9')='#skF_6' | ~v1_funct_2('#skF_9', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_300])).
% 3.31/1.50  tff(c_311, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_9')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_127, c_307])).
% 3.31/1.50  tff(c_312, plain, (k1_relat_1('#skF_9')='#skF_6'), inference(splitLeft, [status(thm)], [c_311])).
% 3.31/1.50  tff(c_424, plain, (![A_166, B_167, D_168]: (r2_hidden('#skF_5'(A_166, B_167, k9_relat_1(A_166, B_167), D_168), k1_relat_1(A_166)) | ~r2_hidden(D_168, k9_relat_1(A_166, B_167)) | ~v1_funct_1(A_166) | ~v1_relat_1(A_166))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.31/1.50  tff(c_432, plain, (![B_167, D_168]: (r2_hidden('#skF_5'('#skF_9', B_167, k9_relat_1('#skF_9', B_167), D_168), '#skF_6') | ~r2_hidden(D_168, k9_relat_1('#skF_9', B_167)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_312, c_424])).
% 3.31/1.50  tff(c_473, plain, (![B_174, D_175]: (r2_hidden('#skF_5'('#skF_9', B_174, k9_relat_1('#skF_9', B_174), D_175), '#skF_6') | ~r2_hidden(D_175, k9_relat_1('#skF_9', B_174)))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_432])).
% 3.31/1.50  tff(c_56, plain, (![F_74]: (k1_funct_1('#skF_9', F_74)!='#skF_10' | ~r2_hidden(F_74, '#skF_8') | ~r2_hidden(F_74, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.31/1.50  tff(c_593, plain, (![B_192, D_193]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_192, k9_relat_1('#skF_9', B_192), D_193))!='#skF_10' | ~r2_hidden('#skF_5'('#skF_9', B_192, k9_relat_1('#skF_9', B_192), D_193), '#skF_8') | ~r2_hidden(D_193, k9_relat_1('#skF_9', B_192)))), inference(resolution, [status(thm)], [c_473, c_56])).
% 3.31/1.50  tff(c_601, plain, (![D_52]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_52))!='#skF_10' | ~r2_hidden(D_52, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_18, c_593])).
% 3.31/1.50  tff(c_607, plain, (![D_195]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', '#skF_8', k9_relat_1('#skF_9', '#skF_8'), D_195))!='#skF_10' | ~r2_hidden(D_195, k9_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_601])).
% 3.31/1.50  tff(c_611, plain, (![D_52]: (D_52!='#skF_10' | ~r2_hidden(D_52, k9_relat_1('#skF_9', '#skF_8')) | ~r2_hidden(D_52, k9_relat_1('#skF_9', '#skF_8')) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_607])).
% 3.31/1.50  tff(c_614, plain, (~r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_64, c_611])).
% 3.31/1.50  tff(c_179, plain, (![A_103, B_104, C_105, D_106]: (k7_relset_1(A_103, B_104, C_105, D_106)=k9_relat_1(C_105, D_106) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.31/1.50  tff(c_186, plain, (![D_106]: (k7_relset_1('#skF_6', '#skF_7', '#skF_9', D_106)=k9_relat_1('#skF_9', D_106))), inference(resolution, [status(thm)], [c_60, c_179])).
% 3.31/1.50  tff(c_189, plain, (r2_hidden('#skF_10', k9_relat_1('#skF_9', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_58])).
% 3.31/1.50  tff(c_616, plain, $false, inference(negUnitSimplification, [status(thm)], [c_614, c_189])).
% 3.31/1.50  tff(c_617, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_311])).
% 3.31/1.50  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.31/1.50  tff(c_625, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_6])).
% 3.31/1.50  tff(c_627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_625])).
% 3.31/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.31/1.50  
% 3.31/1.50  Inference rules
% 3.31/1.50  ----------------------
% 3.31/1.50  #Ref     : 0
% 3.31/1.50  #Sup     : 112
% 3.31/1.50  #Fact    : 0
% 3.31/1.50  #Define  : 0
% 3.31/1.50  #Split   : 7
% 3.31/1.50  #Chain   : 0
% 3.31/1.50  #Close   : 0
% 3.31/1.50  
% 3.31/1.50  Ordering : KBO
% 3.31/1.50  
% 3.31/1.50  Simplification rules
% 3.31/1.50  ----------------------
% 3.31/1.50  #Subsume      : 26
% 3.31/1.50  #Demod        : 52
% 3.31/1.50  #Tautology    : 13
% 3.31/1.50  #SimpNegUnit  : 3
% 3.31/1.50  #BackRed      : 13
% 3.31/1.50  
% 3.31/1.50  #Partial instantiations: 0
% 3.31/1.50  #Strategies tried      : 1
% 3.31/1.50  
% 3.31/1.50  Timing (in seconds)
% 3.31/1.50  ----------------------
% 3.31/1.51  Preprocessing        : 0.37
% 3.31/1.51  Parsing              : 0.18
% 3.31/1.51  CNF conversion       : 0.03
% 3.31/1.51  Main loop            : 0.39
% 3.31/1.51  Inferencing          : 0.14
% 3.31/1.51  Reduction            : 0.11
% 3.31/1.51  Demodulation         : 0.07
% 3.31/1.51  BG Simplification    : 0.03
% 3.31/1.51  Subsumption          : 0.09
% 3.31/1.51  Abstraction          : 0.02
% 3.31/1.51  MUC search           : 0.00
% 3.31/1.51  Cooper               : 0.00
% 3.31/1.51  Total                : 0.79
% 3.31/1.51  Index Insertion      : 0.00
% 3.31/1.51  Index Deletion       : 0.00
% 3.31/1.51  Index Matching       : 0.00
% 3.31/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
