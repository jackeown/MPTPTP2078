%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:21 EST 2020

% Result     : Theorem 3.40s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 130 expanded)
%              Number of leaves         :   36 (  61 expanded)
%              Depth                    :   15
%              Number of atoms          :  127 ( 262 expanded)
%              Number of equality atoms :   26 (  43 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
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

tff(f_39,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_54,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r2_hidden(A,k1_relat_1(B))
       => r2_hidden(k1_funct_1(B,A),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_269,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_277,plain,(
    k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_269])).

tff(c_693,plain,(
    ! [B_149,A_150,C_151] :
      ( k1_xboole_0 = B_149
      | k1_relset_1(A_150,B_149,C_151) = A_150
      | ~ v1_funct_2(C_151,A_150,B_149)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_150,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_700,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k1_tarski('#skF_4')
    | ~ v1_funct_2('#skF_6',k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_54,c_693])).

tff(c_708,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_277,c_700])).

tff(c_709,plain,(
    k1_tarski('#skF_4') = k1_relat_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_708])).

tff(c_10,plain,(
    ! [C_10] : r2_hidden(C_10,k1_tarski(C_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_742,plain,(
    r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_10])).

tff(c_28,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [B_45,A_46] :
      ( v1_relat_1(B_45)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_46))
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_90,plain,
    ( v1_relat_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_54,c_87])).

tff(c_96,plain,(
    v1_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_90])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_30,plain,(
    ! [B_20,A_19] :
      ( r2_hidden(k1_funct_1(B_20,A_19),k2_relat_1(B_20))
      | ~ r2_hidden(A_19,k1_relat_1(B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_98,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),A_47)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [C_10,A_6] :
      ( C_10 = A_6
      | ~ r2_hidden(C_10,k1_tarski(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_108,plain,(
    ! [A_6,B_48] :
      ( '#skF_1'(k1_tarski(A_6),B_48) = A_6
      | r1_tarski(k1_tarski(A_6),B_48) ) ),
    inference(resolution,[status(thm)],[c_98,c_8])).

tff(c_223,plain,(
    ! [A_73,B_74,C_75] :
      ( k2_relset_1(A_73,B_74,C_75) = k2_relat_1(C_75)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_73,B_74))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_231,plain,(
    k2_relset_1(k1_tarski('#skF_4'),'#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_54,c_223])).

tff(c_317,plain,(
    ! [A_95,B_96,C_97] :
      ( m1_subset_1(k2_relset_1(A_95,B_96,C_97),k1_zfmisc_1(B_96))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_337,plain,
    ( m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5'))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_5'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_317])).

tff(c_343,plain,(
    m1_subset_1(k2_relat_1('#skF_6'),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_337])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_351,plain,(
    r1_tarski(k2_relat_1('#skF_6'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_343,c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [C_52,B_53,A_54] :
      ( r2_hidden(C_52,B_53)
      | ~ r2_hidden(C_52,A_54)
      | ~ r1_tarski(A_54,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [A_65,B_66,B_67] :
      ( r2_hidden('#skF_1'(A_65,B_66),B_67)
      | ~ r1_tarski(A_65,B_67)
      | r1_tarski(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_989,plain,(
    ! [A_161,B_162,B_163,B_164] :
      ( r2_hidden('#skF_1'(A_161,B_162),B_163)
      | ~ r1_tarski(B_164,B_163)
      | ~ r1_tarski(A_161,B_164)
      | r1_tarski(A_161,B_162) ) ),
    inference(resolution,[status(thm)],[c_185,c_2])).

tff(c_1045,plain,(
    ! [A_168,B_169] :
      ( r2_hidden('#skF_1'(A_168,B_169),'#skF_5')
      | ~ r1_tarski(A_168,k2_relat_1('#skF_6'))
      | r1_tarski(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_351,c_989])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1066,plain,(
    ! [A_170] :
      ( ~ r1_tarski(A_170,k2_relat_1('#skF_6'))
      | r1_tarski(A_170,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1045,c_4])).

tff(c_1159,plain,(
    ! [A_173] :
      ( r1_tarski(k1_tarski(A_173),'#skF_5')
      | '#skF_1'(k1_tarski(A_173),k2_relat_1('#skF_6')) = A_173 ) ),
    inference(resolution,[status(thm)],[c_108,c_1066])).

tff(c_1278,plain,(
    ! [A_183] :
      ( ~ r2_hidden(A_183,k2_relat_1('#skF_6'))
      | r1_tarski(k1_tarski(A_183),k2_relat_1('#skF_6'))
      | r1_tarski(k1_tarski(A_183),'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1159,c_4])).

tff(c_1065,plain,(
    ! [A_168] :
      ( ~ r1_tarski(A_168,k2_relat_1('#skF_6'))
      | r1_tarski(A_168,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1045,c_4])).

tff(c_1301,plain,(
    ! [A_184] :
      ( ~ r2_hidden(A_184,k2_relat_1('#skF_6'))
      | r1_tarski(k1_tarski(A_184),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1278,c_1065])).

tff(c_1309,plain,(
    ! [A_19] :
      ( r1_tarski(k1_tarski(k1_funct_1('#skF_6',A_19)),'#skF_5')
      | ~ r2_hidden(A_19,k1_relat_1('#skF_6'))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_30,c_1301])).

tff(c_1334,plain,(
    ! [A_185] :
      ( r1_tarski(k1_tarski(k1_funct_1('#skF_6',A_185)),'#skF_5')
      | ~ r2_hidden(A_185,k1_relat_1('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_58,c_1309])).

tff(c_127,plain,(
    ! [C_10,B_53] :
      ( r2_hidden(C_10,B_53)
      | ~ r1_tarski(k1_tarski(C_10),B_53) ) ),
    inference(resolution,[status(thm)],[c_10,c_121])).

tff(c_1349,plain,(
    ! [A_186] :
      ( r2_hidden(k1_funct_1('#skF_6',A_186),'#skF_5')
      | ~ r2_hidden(A_186,k1_relat_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1334,c_127])).

tff(c_50,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1356,plain,(
    ~ r2_hidden('#skF_4',k1_relat_1('#skF_6')) ),
    inference(resolution,[status(thm)],[c_1349,c_50])).

tff(c_1362,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_1356])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:16:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.40/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.54  
% 3.40/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.54  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_1
% 3.40/1.54  
% 3.40/1.54  %Foreground sorts:
% 3.40/1.54  
% 3.40/1.54  
% 3.40/1.54  %Background operators:
% 3.40/1.54  
% 3.40/1.54  
% 3.40/1.54  %Foreground operators:
% 3.40/1.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.40/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.40/1.54  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.40/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.40/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.40/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.54  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.40/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.40/1.54  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.40/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.40/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.40/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.40/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.40/1.54  
% 3.47/1.56  tff(f_104, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 3.47/1.56  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.47/1.56  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.47/1.56  tff(f_39, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.47/1.56  tff(f_54, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.47/1.56  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 3.47/1.56  tff(f_62, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r2_hidden(A, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, A), k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_funct_1)).
% 3.47/1.56  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.47/1.56  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.47/1.56  tff(f_66, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 3.47/1.56  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.47/1.56  tff(c_52, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.47/1.56  tff(c_56, plain, (v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.47/1.56  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.47/1.56  tff(c_269, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.47/1.56  tff(c_277, plain, (k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_269])).
% 3.47/1.56  tff(c_693, plain, (![B_149, A_150, C_151]: (k1_xboole_0=B_149 | k1_relset_1(A_150, B_149, C_151)=A_150 | ~v1_funct_2(C_151, A_150, B_149) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_150, B_149))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.47/1.56  tff(c_700, plain, (k1_xboole_0='#skF_5' | k1_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k1_tarski('#skF_4') | ~v1_funct_2('#skF_6', k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_54, c_693])).
% 3.47/1.56  tff(c_708, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_277, c_700])).
% 3.47/1.56  tff(c_709, plain, (k1_tarski('#skF_4')=k1_relat_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_708])).
% 3.47/1.56  tff(c_10, plain, (![C_10]: (r2_hidden(C_10, k1_tarski(C_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.47/1.56  tff(c_742, plain, (r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_709, c_10])).
% 3.47/1.56  tff(c_28, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.47/1.56  tff(c_87, plain, (![B_45, A_46]: (v1_relat_1(B_45) | ~m1_subset_1(B_45, k1_zfmisc_1(A_46)) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.47/1.56  tff(c_90, plain, (v1_relat_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_54, c_87])).
% 3.47/1.56  tff(c_96, plain, (v1_relat_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_90])).
% 3.47/1.56  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.47/1.56  tff(c_30, plain, (![B_20, A_19]: (r2_hidden(k1_funct_1(B_20, A_19), k2_relat_1(B_20)) | ~r2_hidden(A_19, k1_relat_1(B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.47/1.56  tff(c_98, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47, B_48), A_47) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.56  tff(c_8, plain, (![C_10, A_6]: (C_10=A_6 | ~r2_hidden(C_10, k1_tarski(A_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.47/1.56  tff(c_108, plain, (![A_6, B_48]: ('#skF_1'(k1_tarski(A_6), B_48)=A_6 | r1_tarski(k1_tarski(A_6), B_48))), inference(resolution, [status(thm)], [c_98, c_8])).
% 3.47/1.56  tff(c_223, plain, (![A_73, B_74, C_75]: (k2_relset_1(A_73, B_74, C_75)=k2_relat_1(C_75) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_73, B_74))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.47/1.56  tff(c_231, plain, (k2_relset_1(k1_tarski('#skF_4'), '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_54, c_223])).
% 3.47/1.56  tff(c_317, plain, (![A_95, B_96, C_97]: (m1_subset_1(k2_relset_1(A_95, B_96, C_97), k1_zfmisc_1(B_96)) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.47/1.56  tff(c_337, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_231, c_317])).
% 3.47/1.56  tff(c_343, plain, (m1_subset_1(k2_relat_1('#skF_6'), k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_337])).
% 3.47/1.56  tff(c_22, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.56  tff(c_351, plain, (r1_tarski(k2_relat_1('#skF_6'), '#skF_5')), inference(resolution, [status(thm)], [c_343, c_22])).
% 3.47/1.56  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.56  tff(c_121, plain, (![C_52, B_53, A_54]: (r2_hidden(C_52, B_53) | ~r2_hidden(C_52, A_54) | ~r1_tarski(A_54, B_53))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.56  tff(c_185, plain, (![A_65, B_66, B_67]: (r2_hidden('#skF_1'(A_65, B_66), B_67) | ~r1_tarski(A_65, B_67) | r1_tarski(A_65, B_66))), inference(resolution, [status(thm)], [c_6, c_121])).
% 3.47/1.56  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.56  tff(c_989, plain, (![A_161, B_162, B_163, B_164]: (r2_hidden('#skF_1'(A_161, B_162), B_163) | ~r1_tarski(B_164, B_163) | ~r1_tarski(A_161, B_164) | r1_tarski(A_161, B_162))), inference(resolution, [status(thm)], [c_185, c_2])).
% 3.47/1.56  tff(c_1045, plain, (![A_168, B_169]: (r2_hidden('#skF_1'(A_168, B_169), '#skF_5') | ~r1_tarski(A_168, k2_relat_1('#skF_6')) | r1_tarski(A_168, B_169))), inference(resolution, [status(thm)], [c_351, c_989])).
% 3.47/1.56  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.47/1.56  tff(c_1066, plain, (![A_170]: (~r1_tarski(A_170, k2_relat_1('#skF_6')) | r1_tarski(A_170, '#skF_5'))), inference(resolution, [status(thm)], [c_1045, c_4])).
% 3.47/1.56  tff(c_1159, plain, (![A_173]: (r1_tarski(k1_tarski(A_173), '#skF_5') | '#skF_1'(k1_tarski(A_173), k2_relat_1('#skF_6'))=A_173)), inference(resolution, [status(thm)], [c_108, c_1066])).
% 3.47/1.56  tff(c_1278, plain, (![A_183]: (~r2_hidden(A_183, k2_relat_1('#skF_6')) | r1_tarski(k1_tarski(A_183), k2_relat_1('#skF_6')) | r1_tarski(k1_tarski(A_183), '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1159, c_4])).
% 3.47/1.56  tff(c_1065, plain, (![A_168]: (~r1_tarski(A_168, k2_relat_1('#skF_6')) | r1_tarski(A_168, '#skF_5'))), inference(resolution, [status(thm)], [c_1045, c_4])).
% 3.47/1.56  tff(c_1301, plain, (![A_184]: (~r2_hidden(A_184, k2_relat_1('#skF_6')) | r1_tarski(k1_tarski(A_184), '#skF_5'))), inference(resolution, [status(thm)], [c_1278, c_1065])).
% 3.47/1.56  tff(c_1309, plain, (![A_19]: (r1_tarski(k1_tarski(k1_funct_1('#skF_6', A_19)), '#skF_5') | ~r2_hidden(A_19, k1_relat_1('#skF_6')) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_30, c_1301])).
% 3.47/1.56  tff(c_1334, plain, (![A_185]: (r1_tarski(k1_tarski(k1_funct_1('#skF_6', A_185)), '#skF_5') | ~r2_hidden(A_185, k1_relat_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_58, c_1309])).
% 3.47/1.56  tff(c_127, plain, (![C_10, B_53]: (r2_hidden(C_10, B_53) | ~r1_tarski(k1_tarski(C_10), B_53))), inference(resolution, [status(thm)], [c_10, c_121])).
% 3.47/1.56  tff(c_1349, plain, (![A_186]: (r2_hidden(k1_funct_1('#skF_6', A_186), '#skF_5') | ~r2_hidden(A_186, k1_relat_1('#skF_6')))), inference(resolution, [status(thm)], [c_1334, c_127])).
% 3.47/1.56  tff(c_50, plain, (~r2_hidden(k1_funct_1('#skF_6', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.47/1.56  tff(c_1356, plain, (~r2_hidden('#skF_4', k1_relat_1('#skF_6'))), inference(resolution, [status(thm)], [c_1349, c_50])).
% 3.47/1.56  tff(c_1362, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_742, c_1356])).
% 3.47/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.56  
% 3.47/1.56  Inference rules
% 3.47/1.56  ----------------------
% 3.47/1.56  #Ref     : 0
% 3.47/1.56  #Sup     : 288
% 3.47/1.56  #Fact    : 0
% 3.47/1.56  #Define  : 0
% 3.47/1.56  #Split   : 4
% 3.47/1.56  #Chain   : 0
% 3.47/1.56  #Close   : 0
% 3.47/1.56  
% 3.47/1.56  Ordering : KBO
% 3.47/1.56  
% 3.47/1.56  Simplification rules
% 3.47/1.56  ----------------------
% 3.47/1.56  #Subsume      : 39
% 3.47/1.56  #Demod        : 86
% 3.47/1.56  #Tautology    : 98
% 3.47/1.56  #SimpNegUnit  : 6
% 3.47/1.56  #BackRed      : 5
% 3.47/1.56  
% 3.47/1.56  #Partial instantiations: 0
% 3.47/1.56  #Strategies tried      : 1
% 3.47/1.56  
% 3.47/1.56  Timing (in seconds)
% 3.47/1.56  ----------------------
% 3.47/1.56  Preprocessing        : 0.33
% 3.47/1.56  Parsing              : 0.17
% 3.47/1.56  CNF conversion       : 0.02
% 3.47/1.56  Main loop            : 0.46
% 3.47/1.56  Inferencing          : 0.17
% 3.47/1.56  Reduction            : 0.14
% 3.47/1.56  Demodulation         : 0.09
% 3.47/1.56  BG Simplification    : 0.03
% 3.47/1.56  Subsumption          : 0.10
% 3.47/1.56  Abstraction          : 0.03
% 3.47/1.56  MUC search           : 0.00
% 3.47/1.56  Cooper               : 0.00
% 3.47/1.56  Total                : 0.83
% 3.47/1.56  Index Insertion      : 0.00
% 3.47/1.56  Index Deletion       : 0.00
% 3.47/1.56  Index Matching       : 0.00
% 3.47/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
