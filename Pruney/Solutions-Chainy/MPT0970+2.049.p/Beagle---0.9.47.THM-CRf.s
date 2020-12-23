%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:25 EST 2020

% Result     : Theorem 3.75s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  131 (1054 expanded)
%              Number of leaves         :   36 ( 373 expanded)
%              Depth                    :   15
%              Number of atoms          :  235 (3154 expanded)
%              Number of equality atoms :   91 (1279 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ! [D] :
              ~ ( r2_hidden(D,B)
                & ! [E] :
                    ~ ( r2_hidden(E,A)
                      & D = k1_funct_1(C,E) ) )
         => k2_relset_1(A,B,C) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ! [C] :
            ~ ( r2_hidden(C,A)
              & ! [D] :
                  ~ ( r2_hidden(D,k1_relat_1(B))
                    & C = k1_funct_1(B,D) ) )
       => r1_tarski(A,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_funct_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_103,axiom,(
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

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_49,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_705,plain,(
    ! [A_155,B_156,C_157] :
      ( k2_relset_1(A_155,B_156,C_157) = k2_relat_1(C_157)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_709,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_705])).

tff(c_48,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_710,plain,(
    k2_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_48])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    ! [B_42,A_43] :
      ( v1_relat_1(B_42)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_87])).

tff(c_93,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_90])).

tff(c_660,plain,(
    ! [C_142,B_143,A_144] :
      ( v5_relat_1(C_142,B_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_143))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_664,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_660])).

tff(c_54,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_1'(A_11,B_12),A_11)
      | r1_tarski(A_11,k2_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_58,plain,(
    ! [D_33] :
      ( r2_hidden('#skF_5'(D_33),'#skF_2')
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_52,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_695,plain,(
    ! [A_151,B_152,C_153] :
      ( k1_relset_1(A_151,B_152,C_153) = k1_relat_1(C_153)
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_151,B_152))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_699,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_695])).

tff(c_792,plain,(
    ! [B_177,A_178,C_179] :
      ( k1_xboole_0 = B_177
      | k1_relset_1(A_178,B_177,C_179) = A_178
      | ~ v1_funct_2(C_179,A_178,B_177)
      | ~ m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(A_178,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_795,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_792])).

tff(c_798,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_699,c_795])).

tff(c_799,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_798])).

tff(c_56,plain,(
    ! [D_33] :
      ( k1_funct_1('#skF_4','#skF_5'(D_33)) = D_33
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_864,plain,(
    ! [B_186,D_187,A_188] :
      ( k1_funct_1(B_186,D_187) != '#skF_1'(A_188,B_186)
      | ~ r2_hidden(D_187,k1_relat_1(B_186))
      | r1_tarski(A_188,k2_relat_1(B_186))
      | ~ v1_funct_1(B_186)
      | ~ v1_relat_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_866,plain,(
    ! [D_33,A_188] :
      ( D_33 != '#skF_1'(A_188,'#skF_4')
      | ~ r2_hidden('#skF_5'(D_33),k1_relat_1('#skF_4'))
      | r1_tarski(A_188,k2_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_864])).

tff(c_868,plain,(
    ! [D_33,A_188] :
      ( D_33 != '#skF_1'(A_188,'#skF_4')
      | ~ r2_hidden('#skF_5'(D_33),'#skF_2')
      | r1_tarski(A_188,k2_relat_1('#skF_4'))
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_54,c_799,c_866])).

tff(c_874,plain,(
    ! [A_191] :
      ( ~ r2_hidden('#skF_5'('#skF_1'(A_191,'#skF_4')),'#skF_2')
      | r1_tarski(A_191,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_191,'#skF_4'),'#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_868])).

tff(c_879,plain,(
    ! [A_192] :
      ( r1_tarski(A_192,k2_relat_1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_192,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_874])).

tff(c_883,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_879])).

tff(c_886,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_54,c_883])).

tff(c_627,plain,(
    ! [B_138,A_139] :
      ( r1_tarski(k2_relat_1(B_138),A_139)
      | ~ v5_relat_1(B_138,A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_637,plain,(
    ! [B_138,A_139] :
      ( k2_relat_1(B_138) = A_139
      | ~ r1_tarski(A_139,k2_relat_1(B_138))
      | ~ v5_relat_1(B_138,A_139)
      | ~ v1_relat_1(B_138) ) ),
    inference(resolution,[status(thm)],[c_627,c_2])).

tff(c_889,plain,
    ( k2_relat_1('#skF_4') = '#skF_3'
    | ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_886,c_637])).

tff(c_894,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_664,c_889])).

tff(c_896,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_710,c_894])).

tff(c_897,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_798])).

tff(c_94,plain,(
    ! [A_44] :
      ( k1_relat_1(A_44) = k1_xboole_0
      | k2_relat_1(A_44) != k1_xboole_0
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_101,plain,
    ( k1_relat_1('#skF_4') = k1_xboole_0
    | k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_94])).

tff(c_103,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_104,plain,(
    ! [A_45] :
      ( k2_relat_1(A_45) = k1_xboole_0
      | k1_relat_1(A_45) != k1_xboole_0
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_111,plain,
    ( k2_relat_1('#skF_4') = k1_xboole_0
    | k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_93,c_104])).

tff(c_113,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_111])).

tff(c_915,plain,(
    k1_relat_1('#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_113])).

tff(c_38,plain,(
    ! [C_29,A_27] :
      ( k1_xboole_0 = C_29
      | ~ v1_funct_2(C_29,A_27,k1_xboole_0)
      | k1_xboole_0 = A_27
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1109,plain,(
    ! [C_222,A_223] :
      ( C_222 = '#skF_3'
      | ~ v1_funct_2(C_222,A_223,'#skF_3')
      | A_223 = '#skF_3'
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_223,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_897,c_897,c_897,c_38])).

tff(c_1112,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_1109])).

tff(c_1115,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1112])).

tff(c_1117,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1115])).

tff(c_1124,plain,(
    v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1117,c_52])).

tff(c_1120,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1117,c_699])).

tff(c_1123,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1117,c_50])).

tff(c_44,plain,(
    ! [B_28,C_29] :
      ( k1_relset_1(k1_xboole_0,B_28,C_29) = k1_xboole_0
      | ~ v1_funct_2(C_29,k1_xboole_0,B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1181,plain,(
    ! [B_227,C_228] :
      ( k1_relset_1('#skF_3',B_227,C_228) = '#skF_3'
      | ~ v1_funct_2(C_228,'#skF_3',B_227)
      | ~ m1_subset_1(C_228,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_227))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_897,c_897,c_897,c_44])).

tff(c_1184,plain,
    ( k1_relset_1('#skF_3','#skF_3','#skF_4') = '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1123,c_1181])).

tff(c_1187,plain,(
    k1_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1124,c_1120,c_1184])).

tff(c_1189,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_915,c_1187])).

tff(c_1190,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1115])).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_920,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_897,c_897,c_18])).

tff(c_1212,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_1190,c_920])).

tff(c_1211,plain,(
    k1_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1190,c_915])).

tff(c_1242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1212,c_1211])).

tff(c_1244,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_1371,plain,(
    ! [A_252,B_253,C_254] :
      ( k2_relset_1(A_252,B_253,C_254) = k2_relat_1(C_254)
      | ~ m1_subset_1(C_254,k1_zfmisc_1(k2_zfmisc_1(A_252,B_253))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1374,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1371])).

tff(c_1376,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_1374])).

tff(c_1377,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_48])).

tff(c_1243,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_1382,plain,(
    ! [A_255,B_256,C_257] :
      ( k1_relset_1(A_255,B_256,C_257) = k1_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1385,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1382])).

tff(c_1387,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1243,c_1385])).

tff(c_1533,plain,(
    ! [B_280,A_281,C_282] :
      ( k1_xboole_0 = B_280
      | k1_relset_1(A_281,B_280,C_282) = A_281
      | ~ v1_funct_2(C_282,A_281,B_280)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_281,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1536,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1533])).

tff(c_1539,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1387,c_1536])).

tff(c_1540,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_1377,c_1539])).

tff(c_1551,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1377])).

tff(c_1327,plain,(
    ! [C_242,B_243,A_244] :
      ( v5_relat_1(C_242,B_243)
      | ~ m1_subset_1(C_242,k1_zfmisc_1(k2_zfmisc_1(A_244,B_243))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1331,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1327])).

tff(c_1289,plain,(
    ! [B_236,A_237] :
      ( r1_tarski(k2_relat_1(B_236),A_237)
      | ~ v5_relat_1(B_236,A_237)
      | ~ v1_relat_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_1297,plain,(
    ! [A_237] :
      ( r1_tarski(k1_xboole_0,A_237)
      | ~ v5_relat_1('#skF_4',A_237)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_1289])).

tff(c_1304,plain,(
    ! [A_237] :
      ( r1_tarski(k1_xboole_0,A_237)
      | ~ v5_relat_1('#skF_4',A_237) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1297])).

tff(c_1335,plain,(
    r1_tarski(k1_xboole_0,'#skF_3') ),
    inference(resolution,[status(thm)],[c_1331,c_1304])).

tff(c_1558,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1335])).

tff(c_1574,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_1558,c_2])).

tff(c_1577,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1551,c_1574])).

tff(c_1563,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1244])).

tff(c_1564,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1540,c_1243])).

tff(c_1680,plain,(
    ! [B_288,D_289,A_290] :
      ( k1_funct_1(B_288,D_289) != '#skF_1'(A_290,B_288)
      | ~ r2_hidden(D_289,k1_relat_1(B_288))
      | r1_tarski(A_290,k2_relat_1(B_288))
      | ~ v1_funct_1(B_288)
      | ~ v1_relat_1(B_288) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1682,plain,(
    ! [D_33,A_290] :
      ( D_33 != '#skF_1'(A_290,'#skF_4')
      | ~ r2_hidden('#skF_5'(D_33),k1_relat_1('#skF_4'))
      | r1_tarski(A_290,k2_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4')
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1680])).

tff(c_1684,plain,(
    ! [D_33,A_290] :
      ( D_33 != '#skF_1'(A_290,'#skF_4')
      | ~ r2_hidden('#skF_5'(D_33),'#skF_2')
      | r1_tarski(A_290,'#skF_2')
      | ~ r2_hidden(D_33,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_54,c_1563,c_1564,c_1682])).

tff(c_1817,plain,(
    ! [A_306] :
      ( ~ r2_hidden('#skF_5'('#skF_1'(A_306,'#skF_4')),'#skF_2')
      | r1_tarski(A_306,'#skF_2')
      | ~ r2_hidden('#skF_1'(A_306,'#skF_4'),'#skF_3') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1684])).

tff(c_1822,plain,(
    ! [A_307] :
      ( r1_tarski(A_307,'#skF_2')
      | ~ r2_hidden('#skF_1'(A_307,'#skF_4'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_58,c_1817])).

tff(c_1826,plain,
    ( r1_tarski('#skF_3','#skF_2')
    | r1_tarski('#skF_3',k2_relat_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1822])).

tff(c_1829,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_54,c_1563,c_1826])).

tff(c_1831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1577,c_1829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.75/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.62  
% 3.75/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.63  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.75/1.63  
% 3.75/1.63  %Foreground sorts:
% 3.75/1.63  
% 3.75/1.63  
% 3.75/1.63  %Background operators:
% 3.75/1.63  
% 3.75/1.63  
% 3.75/1.63  %Foreground operators:
% 3.75/1.63  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.75/1.63  tff('#skF_5', type, '#skF_5': $i > $i).
% 3.75/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.75/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.75/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.75/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.63  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.75/1.63  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.75/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.75/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.75/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.75/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.75/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.63  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.75/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.75/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.75/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.63  
% 3.75/1.65  tff(f_122, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 3.75/1.65  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.75/1.65  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.75/1.65  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.75/1.65  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.75/1.65  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, k1_relat_1(B)) & (C = k1_funct_1(B, D)))))) => r1_tarski(A, k2_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_funct_1)).
% 3.75/1.65  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.75/1.65  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.75/1.65  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 3.75/1.65  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.75/1.65  tff(f_55, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 3.75/1.65  tff(f_49, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.75/1.65  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.75/1.65  tff(c_705, plain, (![A_155, B_156, C_157]: (k2_relset_1(A_155, B_156, C_157)=k2_relat_1(C_157) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.75/1.65  tff(c_709, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_705])).
% 3.75/1.65  tff(c_48, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.75/1.65  tff(c_710, plain, (k2_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_709, c_48])).
% 3.75/1.65  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.75/1.65  tff(c_87, plain, (![B_42, A_43]: (v1_relat_1(B_42) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.75/1.65  tff(c_90, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_87])).
% 3.75/1.65  tff(c_93, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_90])).
% 3.75/1.65  tff(c_660, plain, (![C_142, B_143, A_144]: (v5_relat_1(C_142, B_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_143))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.75/1.65  tff(c_664, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_660])).
% 3.75/1.65  tff(c_54, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.75/1.65  tff(c_26, plain, (![A_11, B_12]: (r2_hidden('#skF_1'(A_11, B_12), A_11) | r1_tarski(A_11, k2_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.75/1.65  tff(c_58, plain, (![D_33]: (r2_hidden('#skF_5'(D_33), '#skF_2') | ~r2_hidden(D_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.75/1.65  tff(c_52, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.75/1.65  tff(c_695, plain, (![A_151, B_152, C_153]: (k1_relset_1(A_151, B_152, C_153)=k1_relat_1(C_153) | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_151, B_152))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.75/1.65  tff(c_699, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_695])).
% 3.75/1.65  tff(c_792, plain, (![B_177, A_178, C_179]: (k1_xboole_0=B_177 | k1_relset_1(A_178, B_177, C_179)=A_178 | ~v1_funct_2(C_179, A_178, B_177) | ~m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(A_178, B_177))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.75/1.65  tff(c_795, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_792])).
% 3.75/1.65  tff(c_798, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_699, c_795])).
% 3.75/1.65  tff(c_799, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitLeft, [status(thm)], [c_798])).
% 3.75/1.65  tff(c_56, plain, (![D_33]: (k1_funct_1('#skF_4', '#skF_5'(D_33))=D_33 | ~r2_hidden(D_33, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.75/1.65  tff(c_864, plain, (![B_186, D_187, A_188]: (k1_funct_1(B_186, D_187)!='#skF_1'(A_188, B_186) | ~r2_hidden(D_187, k1_relat_1(B_186)) | r1_tarski(A_188, k2_relat_1(B_186)) | ~v1_funct_1(B_186) | ~v1_relat_1(B_186))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.75/1.65  tff(c_866, plain, (![D_33, A_188]: (D_33!='#skF_1'(A_188, '#skF_4') | ~r2_hidden('#skF_5'(D_33), k1_relat_1('#skF_4')) | r1_tarski(A_188, k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_33, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_864])).
% 3.75/1.65  tff(c_868, plain, (![D_33, A_188]: (D_33!='#skF_1'(A_188, '#skF_4') | ~r2_hidden('#skF_5'(D_33), '#skF_2') | r1_tarski(A_188, k2_relat_1('#skF_4')) | ~r2_hidden(D_33, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_54, c_799, c_866])).
% 3.75/1.65  tff(c_874, plain, (![A_191]: (~r2_hidden('#skF_5'('#skF_1'(A_191, '#skF_4')), '#skF_2') | r1_tarski(A_191, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_191, '#skF_4'), '#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_868])).
% 3.75/1.65  tff(c_879, plain, (![A_192]: (r1_tarski(A_192, k2_relat_1('#skF_4')) | ~r2_hidden('#skF_1'(A_192, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_874])).
% 3.75/1.65  tff(c_883, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_879])).
% 3.75/1.65  tff(c_886, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_54, c_883])).
% 3.75/1.65  tff(c_627, plain, (![B_138, A_139]: (r1_tarski(k2_relat_1(B_138), A_139) | ~v5_relat_1(B_138, A_139) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.75/1.65  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.75/1.65  tff(c_637, plain, (![B_138, A_139]: (k2_relat_1(B_138)=A_139 | ~r1_tarski(A_139, k2_relat_1(B_138)) | ~v5_relat_1(B_138, A_139) | ~v1_relat_1(B_138))), inference(resolution, [status(thm)], [c_627, c_2])).
% 3.75/1.65  tff(c_889, plain, (k2_relat_1('#skF_4')='#skF_3' | ~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_886, c_637])).
% 3.75/1.65  tff(c_894, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_664, c_889])).
% 3.75/1.65  tff(c_896, plain, $false, inference(negUnitSimplification, [status(thm)], [c_710, c_894])).
% 3.75/1.65  tff(c_897, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_798])).
% 3.75/1.65  tff(c_94, plain, (![A_44]: (k1_relat_1(A_44)=k1_xboole_0 | k2_relat_1(A_44)!=k1_xboole_0 | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.75/1.65  tff(c_101, plain, (k1_relat_1('#skF_4')=k1_xboole_0 | k2_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_94])).
% 3.75/1.65  tff(c_103, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_101])).
% 3.75/1.65  tff(c_104, plain, (![A_45]: (k2_relat_1(A_45)=k1_xboole_0 | k1_relat_1(A_45)!=k1_xboole_0 | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.75/1.65  tff(c_111, plain, (k2_relat_1('#skF_4')=k1_xboole_0 | k1_relat_1('#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_93, c_104])).
% 3.75/1.65  tff(c_113, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_103, c_111])).
% 3.75/1.65  tff(c_915, plain, (k1_relat_1('#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_897, c_113])).
% 3.75/1.65  tff(c_38, plain, (![C_29, A_27]: (k1_xboole_0=C_29 | ~v1_funct_2(C_29, A_27, k1_xboole_0) | k1_xboole_0=A_27 | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.75/1.65  tff(c_1109, plain, (![C_222, A_223]: (C_222='#skF_3' | ~v1_funct_2(C_222, A_223, '#skF_3') | A_223='#skF_3' | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_223, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_897, c_897, c_897, c_38])).
% 3.75/1.65  tff(c_1112, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_50, c_1109])).
% 3.75/1.65  tff(c_1115, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1112])).
% 3.75/1.65  tff(c_1117, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_1115])).
% 3.75/1.65  tff(c_1124, plain, (v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1117, c_52])).
% 3.75/1.65  tff(c_1120, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1117, c_699])).
% 3.75/1.65  tff(c_1123, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1117, c_50])).
% 3.75/1.65  tff(c_44, plain, (![B_28, C_29]: (k1_relset_1(k1_xboole_0, B_28, C_29)=k1_xboole_0 | ~v1_funct_2(C_29, k1_xboole_0, B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_28))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.75/1.65  tff(c_1181, plain, (![B_227, C_228]: (k1_relset_1('#skF_3', B_227, C_228)='#skF_3' | ~v1_funct_2(C_228, '#skF_3', B_227) | ~m1_subset_1(C_228, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_227))))), inference(demodulation, [status(thm), theory('equality')], [c_897, c_897, c_897, c_897, c_44])).
% 3.75/1.65  tff(c_1184, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3' | ~v1_funct_2('#skF_4', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1123, c_1181])).
% 3.75/1.65  tff(c_1187, plain, (k1_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1124, c_1120, c_1184])).
% 3.75/1.65  tff(c_1189, plain, $false, inference(negUnitSimplification, [status(thm)], [c_915, c_1187])).
% 3.75/1.65  tff(c_1190, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1115])).
% 3.75/1.65  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.75/1.65  tff(c_920, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_897, c_897, c_18])).
% 3.75/1.65  tff(c_1212, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_1190, c_920])).
% 3.75/1.65  tff(c_1211, plain, (k1_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1190, c_915])).
% 3.75/1.65  tff(c_1242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1212, c_1211])).
% 3.75/1.65  tff(c_1244, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_101])).
% 3.75/1.65  tff(c_1371, plain, (![A_252, B_253, C_254]: (k2_relset_1(A_252, B_253, C_254)=k2_relat_1(C_254) | ~m1_subset_1(C_254, k1_zfmisc_1(k2_zfmisc_1(A_252, B_253))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.75/1.65  tff(c_1374, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1371])).
% 3.75/1.65  tff(c_1376, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_1374])).
% 3.75/1.65  tff(c_1377, plain, (k1_xboole_0!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_48])).
% 3.75/1.65  tff(c_1243, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_101])).
% 3.75/1.65  tff(c_1382, plain, (![A_255, B_256, C_257]: (k1_relset_1(A_255, B_256, C_257)=k1_relat_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.75/1.65  tff(c_1385, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1382])).
% 3.75/1.65  tff(c_1387, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1243, c_1385])).
% 3.75/1.65  tff(c_1533, plain, (![B_280, A_281, C_282]: (k1_xboole_0=B_280 | k1_relset_1(A_281, B_280, C_282)=A_281 | ~v1_funct_2(C_282, A_281, B_280) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_281, B_280))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.75/1.65  tff(c_1536, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1533])).
% 3.75/1.65  tff(c_1539, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1387, c_1536])).
% 3.75/1.65  tff(c_1540, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_1377, c_1539])).
% 3.75/1.65  tff(c_1551, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1377])).
% 3.75/1.65  tff(c_1327, plain, (![C_242, B_243, A_244]: (v5_relat_1(C_242, B_243) | ~m1_subset_1(C_242, k1_zfmisc_1(k2_zfmisc_1(A_244, B_243))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.75/1.65  tff(c_1331, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1327])).
% 3.75/1.65  tff(c_1289, plain, (![B_236, A_237]: (r1_tarski(k2_relat_1(B_236), A_237) | ~v5_relat_1(B_236, A_237) | ~v1_relat_1(B_236))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.75/1.65  tff(c_1297, plain, (![A_237]: (r1_tarski(k1_xboole_0, A_237) | ~v5_relat_1('#skF_4', A_237) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1244, c_1289])).
% 3.75/1.65  tff(c_1304, plain, (![A_237]: (r1_tarski(k1_xboole_0, A_237) | ~v5_relat_1('#skF_4', A_237))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1297])).
% 3.75/1.65  tff(c_1335, plain, (r1_tarski(k1_xboole_0, '#skF_3')), inference(resolution, [status(thm)], [c_1331, c_1304])).
% 3.75/1.65  tff(c_1558, plain, (r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1335])).
% 3.75/1.65  tff(c_1574, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_1558, c_2])).
% 3.75/1.65  tff(c_1577, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1551, c_1574])).
% 3.75/1.65  tff(c_1563, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1244])).
% 3.75/1.65  tff(c_1564, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1540, c_1243])).
% 3.75/1.65  tff(c_1680, plain, (![B_288, D_289, A_290]: (k1_funct_1(B_288, D_289)!='#skF_1'(A_290, B_288) | ~r2_hidden(D_289, k1_relat_1(B_288)) | r1_tarski(A_290, k2_relat_1(B_288)) | ~v1_funct_1(B_288) | ~v1_relat_1(B_288))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.75/1.65  tff(c_1682, plain, (![D_33, A_290]: (D_33!='#skF_1'(A_290, '#skF_4') | ~r2_hidden('#skF_5'(D_33), k1_relat_1('#skF_4')) | r1_tarski(A_290, k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~r2_hidden(D_33, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1680])).
% 3.75/1.65  tff(c_1684, plain, (![D_33, A_290]: (D_33!='#skF_1'(A_290, '#skF_4') | ~r2_hidden('#skF_5'(D_33), '#skF_2') | r1_tarski(A_290, '#skF_2') | ~r2_hidden(D_33, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_54, c_1563, c_1564, c_1682])).
% 3.75/1.65  tff(c_1817, plain, (![A_306]: (~r2_hidden('#skF_5'('#skF_1'(A_306, '#skF_4')), '#skF_2') | r1_tarski(A_306, '#skF_2') | ~r2_hidden('#skF_1'(A_306, '#skF_4'), '#skF_3'))), inference(reflexivity, [status(thm), theory('equality')], [c_1684])).
% 3.75/1.65  tff(c_1822, plain, (![A_307]: (r1_tarski(A_307, '#skF_2') | ~r2_hidden('#skF_1'(A_307, '#skF_4'), '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_1817])).
% 3.75/1.65  tff(c_1826, plain, (r1_tarski('#skF_3', '#skF_2') | r1_tarski('#skF_3', k2_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1822])).
% 3.75/1.65  tff(c_1829, plain, (r1_tarski('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_54, c_1563, c_1826])).
% 3.75/1.65  tff(c_1831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1577, c_1829])).
% 3.75/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.75/1.65  
% 3.75/1.65  Inference rules
% 3.75/1.65  ----------------------
% 3.75/1.65  #Ref     : 5
% 3.75/1.65  #Sup     : 337
% 3.75/1.65  #Fact    : 0
% 3.75/1.65  #Define  : 0
% 3.75/1.65  #Split   : 8
% 3.75/1.65  #Chain   : 0
% 3.75/1.65  #Close   : 0
% 3.75/1.65  
% 3.75/1.65  Ordering : KBO
% 4.09/1.65  
% 4.09/1.65  Simplification rules
% 4.09/1.65  ----------------------
% 4.09/1.65  #Subsume      : 85
% 4.09/1.65  #Demod        : 527
% 4.09/1.65  #Tautology    : 175
% 4.09/1.65  #SimpNegUnit  : 15
% 4.09/1.65  #BackRed      : 147
% 4.09/1.65  
% 4.09/1.65  #Partial instantiations: 0
% 4.09/1.65  #Strategies tried      : 1
% 4.09/1.65  
% 4.09/1.65  Timing (in seconds)
% 4.09/1.65  ----------------------
% 4.09/1.65  Preprocessing        : 0.32
% 4.09/1.65  Parsing              : 0.16
% 4.09/1.65  CNF conversion       : 0.02
% 4.09/1.65  Main loop            : 0.56
% 4.09/1.65  Inferencing          : 0.20
% 4.09/1.65  Reduction            : 0.18
% 4.09/1.65  Demodulation         : 0.12
% 4.09/1.65  BG Simplification    : 0.02
% 4.09/1.65  Subsumption          : 0.10
% 4.09/1.65  Abstraction          : 0.03
% 4.09/1.65  MUC search           : 0.00
% 4.09/1.65  Cooper               : 0.00
% 4.09/1.65  Total                : 0.92
% 4.09/1.65  Index Insertion      : 0.00
% 4.09/1.65  Index Deletion       : 0.00
% 4.09/1.65  Index Matching       : 0.00
% 4.09/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
