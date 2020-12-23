%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:47 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 232 expanded)
%              Number of leaves         :   41 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 457 expanded)
%              Number of equality atoms :   64 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_119,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,k1_tarski(A),B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r1_tarski(k7_relset_1(k1_tarski(A),B,D,C),k1_tarski(k1_funct_1(D,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_2)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_107,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_128,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_140,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_128])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k9_relat_1(B_21,A_20),k2_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_44,plain,(
    ! [A_22] :
      ( k1_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_150,plain,
    ( k1_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_44])).

tff(c_173,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_647,plain,(
    ! [B_137,A_138] :
      ( k1_tarski(k1_funct_1(B_137,A_138)) = k2_relat_1(B_137)
      | k1_tarski(A_138) != k1_relat_1(B_137)
      | ~ v1_funct_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_545,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k7_relset_1(A_116,B_117,C_118,D_119) = k9_relat_1(C_118,D_119)
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_556,plain,(
    ! [D_119] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4',D_119) = k9_relat_1('#skF_4',D_119) ),
    inference(resolution,[status(thm)],[c_60,c_545])).

tff(c_56,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_601,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_56])).

tff(c_653,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_601])).

tff(c_665,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4'))
    | k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_64,c_653])).

tff(c_667,plain,(
    k1_tarski('#skF_1') != k1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_665])).

tff(c_298,plain,(
    ! [C_81,A_82,B_83] :
      ( v4_relat_1(C_81,A_82)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_310,plain,(
    v4_relat_1('#skF_4',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_298])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_677,plain,(
    ! [B_141,C_142,A_143] :
      ( k2_tarski(B_141,C_142) = A_143
      | k1_tarski(C_142) = A_143
      | k1_tarski(B_141) = A_143
      | k1_xboole_0 = A_143
      | ~ r1_tarski(A_143,k2_tarski(B_141,C_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_694,plain,(
    ! [A_3,A_143] :
      ( k2_tarski(A_3,A_3) = A_143
      | k1_tarski(A_3) = A_143
      | k1_tarski(A_3) = A_143
      | k1_xboole_0 = A_143
      | ~ r1_tarski(A_143,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_677])).

tff(c_1158,plain,(
    ! [A_209,A_210] :
      ( k1_tarski(A_209) = A_210
      | k1_tarski(A_209) = A_210
      | k1_tarski(A_209) = A_210
      | k1_xboole_0 = A_210
      | ~ r1_tarski(A_210,k1_tarski(A_209)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_694])).

tff(c_1179,plain,(
    ! [A_211,B_212] :
      ( k1_tarski(A_211) = k1_relat_1(B_212)
      | k1_relat_1(B_212) = k1_xboole_0
      | ~ v4_relat_1(B_212,k1_tarski(A_211))
      | ~ v1_relat_1(B_212) ) ),
    inference(resolution,[status(thm)],[c_34,c_1158])).

tff(c_1205,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_310,c_1179])).

tff(c_1223,plain,
    ( k1_tarski('#skF_1') = k1_relat_1('#skF_4')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1205])).

tff(c_1225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_667,c_1223])).

tff(c_1226,plain,(
    ~ r1_tarski(k9_relat_1('#skF_4','#skF_3'),k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_665])).

tff(c_1265,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_1226])).

tff(c_1269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1265])).

tff(c_1270,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_38,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1279,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_1270,c_38])).

tff(c_42,plain,(
    ! [A_22] :
      ( k2_relat_1(A_22) != k1_xboole_0
      | k1_xboole_0 = A_22
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_149,plain,
    ( k2_relat_1('#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_140,c_42])).

tff(c_165,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_149])).

tff(c_1273,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1270,c_165])).

tff(c_1328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1279,c_1273])).

tff(c_1329,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_24,plain,(
    ! [A_12] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_102,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ m1_subset_1(A_48,k1_zfmisc_1(B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_110,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(resolution,[status(thm)],[c_24,c_102])).

tff(c_1332,plain,(
    ! [A_12] : r1_tarski('#skF_4',A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_110])).

tff(c_1330,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_149])).

tff(c_1344,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_1330])).

tff(c_1440,plain,(
    ! [B_228,A_229] :
      ( r1_tarski(k9_relat_1(B_228,A_229),k2_relat_1(B_228))
      | ~ v1_relat_1(B_228) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1445,plain,(
    ! [A_229] :
      ( r1_tarski(k9_relat_1('#skF_4',A_229),'#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1344,c_1440])).

tff(c_1449,plain,(
    ! [A_230] : r1_tarski(k9_relat_1('#skF_4',A_230),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_1445])).

tff(c_1371,plain,(
    ! [A_218] : r1_tarski('#skF_4',A_218) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_110])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1374,plain,(
    ! [A_218] :
      ( A_218 = '#skF_4'
      | ~ r1_tarski(A_218,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1371,c_2])).

tff(c_1455,plain,(
    ! [A_230] : k9_relat_1('#skF_4',A_230) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1449,c_1374])).

tff(c_1335,plain,(
    ! [A_12] : m1_subset_1('#skF_4',k1_zfmisc_1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1329,c_24])).

tff(c_1639,plain,(
    ! [A_272,B_273,C_274,D_275] :
      ( k7_relset_1(A_272,B_273,C_274,D_275) = k9_relat_1(C_274,D_275)
      | ~ m1_subset_1(C_274,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1642,plain,(
    ! [A_272,B_273,D_275] : k7_relset_1(A_272,B_273,'#skF_4',D_275) = k9_relat_1('#skF_4',D_275) ),
    inference(resolution,[status(thm)],[c_1335,c_1639])).

tff(c_1647,plain,(
    ! [A_272,B_273,D_275] : k7_relset_1(A_272,B_273,'#skF_4',D_275) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1455,c_1642])).

tff(c_1649,plain,(
    ~ r1_tarski('#skF_4',k1_tarski(k1_funct_1('#skF_4','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1647,c_56])).

tff(c_1652,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1332,c_1649])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:07:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.50/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.56  
% 3.50/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.56  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.50/1.56  
% 3.50/1.56  %Foreground sorts:
% 3.50/1.56  
% 3.50/1.56  
% 3.50/1.56  %Background operators:
% 3.50/1.56  
% 3.50/1.56  
% 3.50/1.56  %Foreground operators:
% 3.50/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.50/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.50/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.50/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.50/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.50/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.50/1.56  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.50/1.56  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.50/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.50/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.50/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.50/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.50/1.56  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.50/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.50/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.50/1.56  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.50/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.50/1.56  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.50/1.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.50/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.50/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.50/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.50/1.56  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.50/1.56  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.50/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.50/1.56  
% 3.50/1.58  tff(f_119, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, k1_tarski(A), B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r1_tarski(k7_relset_1(k1_tarski(A), B, D, C), k1_tarski(k1_funct_1(D, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_funct_2)).
% 3.50/1.58  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.50/1.58  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 3.50/1.58  tff(f_85, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 3.50/1.58  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_funct_1)).
% 3.50/1.58  tff(f_107, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.50/1.58  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.50/1.58  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 3.50/1.58  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.50/1.58  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.50/1.58  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 3.50/1.58  tff(f_54, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.50/1.58  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.50/1.58  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.50/1.58  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.58  tff(c_128, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.50/1.58  tff(c_140, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_128])).
% 3.50/1.58  tff(c_36, plain, (![B_21, A_20]: (r1_tarski(k9_relat_1(B_21, A_20), k2_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.50/1.58  tff(c_44, plain, (![A_22]: (k1_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.50/1.58  tff(c_150, plain, (k1_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_140, c_44])).
% 3.50/1.58  tff(c_173, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_150])).
% 3.50/1.58  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.58  tff(c_647, plain, (![B_137, A_138]: (k1_tarski(k1_funct_1(B_137, A_138))=k2_relat_1(B_137) | k1_tarski(A_138)!=k1_relat_1(B_137) | ~v1_funct_1(B_137) | ~v1_relat_1(B_137))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.50/1.58  tff(c_545, plain, (![A_116, B_117, C_118, D_119]: (k7_relset_1(A_116, B_117, C_118, D_119)=k9_relat_1(C_118, D_119) | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.50/1.58  tff(c_556, plain, (![D_119]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', D_119)=k9_relat_1('#skF_4', D_119))), inference(resolution, [status(thm)], [c_60, c_545])).
% 3.50/1.58  tff(c_56, plain, (~r1_tarski(k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_119])).
% 3.50/1.58  tff(c_601, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_556, c_56])).
% 3.50/1.58  tff(c_653, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_647, c_601])).
% 3.50/1.58  tff(c_665, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4')) | k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_140, c_64, c_653])).
% 3.50/1.58  tff(c_667, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_665])).
% 3.50/1.58  tff(c_298, plain, (![C_81, A_82, B_83]: (v4_relat_1(C_81, A_82) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.50/1.58  tff(c_310, plain, (v4_relat_1('#skF_4', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_60, c_298])).
% 3.50/1.58  tff(c_34, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.50/1.58  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.50/1.58  tff(c_677, plain, (![B_141, C_142, A_143]: (k2_tarski(B_141, C_142)=A_143 | k1_tarski(C_142)=A_143 | k1_tarski(B_141)=A_143 | k1_xboole_0=A_143 | ~r1_tarski(A_143, k2_tarski(B_141, C_142)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.50/1.58  tff(c_694, plain, (![A_3, A_143]: (k2_tarski(A_3, A_3)=A_143 | k1_tarski(A_3)=A_143 | k1_tarski(A_3)=A_143 | k1_xboole_0=A_143 | ~r1_tarski(A_143, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_677])).
% 3.50/1.58  tff(c_1158, plain, (![A_209, A_210]: (k1_tarski(A_209)=A_210 | k1_tarski(A_209)=A_210 | k1_tarski(A_209)=A_210 | k1_xboole_0=A_210 | ~r1_tarski(A_210, k1_tarski(A_209)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_694])).
% 3.50/1.58  tff(c_1179, plain, (![A_211, B_212]: (k1_tarski(A_211)=k1_relat_1(B_212) | k1_relat_1(B_212)=k1_xboole_0 | ~v4_relat_1(B_212, k1_tarski(A_211)) | ~v1_relat_1(B_212))), inference(resolution, [status(thm)], [c_34, c_1158])).
% 3.50/1.58  tff(c_1205, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_310, c_1179])).
% 3.50/1.58  tff(c_1223, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_4') | k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1205])).
% 3.50/1.58  tff(c_1225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_667, c_1223])).
% 3.50/1.58  tff(c_1226, plain, (~r1_tarski(k9_relat_1('#skF_4', '#skF_3'), k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_665])).
% 3.50/1.58  tff(c_1265, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_1226])).
% 3.50/1.58  tff(c_1269, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_140, c_1265])).
% 3.50/1.58  tff(c_1270, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_150])).
% 3.50/1.58  tff(c_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.50/1.58  tff(c_1279, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_1270, c_38])).
% 3.50/1.58  tff(c_42, plain, (![A_22]: (k2_relat_1(A_22)!=k1_xboole_0 | k1_xboole_0=A_22 | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.50/1.58  tff(c_149, plain, (k2_relat_1('#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_140, c_42])).
% 3.50/1.58  tff(c_165, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_149])).
% 3.50/1.58  tff(c_1273, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1270, c_165])).
% 3.50/1.58  tff(c_1328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1279, c_1273])).
% 3.50/1.58  tff(c_1329, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_149])).
% 3.50/1.58  tff(c_24, plain, (![A_12]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.50/1.58  tff(c_102, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~m1_subset_1(A_48, k1_zfmisc_1(B_49)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.50/1.58  tff(c_110, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(resolution, [status(thm)], [c_24, c_102])).
% 3.50/1.58  tff(c_1332, plain, (![A_12]: (r1_tarski('#skF_4', A_12))), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_110])).
% 3.50/1.58  tff(c_1330, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_149])).
% 3.50/1.58  tff(c_1344, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_1330])).
% 3.50/1.58  tff(c_1440, plain, (![B_228, A_229]: (r1_tarski(k9_relat_1(B_228, A_229), k2_relat_1(B_228)) | ~v1_relat_1(B_228))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.50/1.58  tff(c_1445, plain, (![A_229]: (r1_tarski(k9_relat_1('#skF_4', A_229), '#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1344, c_1440])).
% 3.50/1.58  tff(c_1449, plain, (![A_230]: (r1_tarski(k9_relat_1('#skF_4', A_230), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_140, c_1445])).
% 3.50/1.58  tff(c_1371, plain, (![A_218]: (r1_tarski('#skF_4', A_218))), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_110])).
% 3.50/1.58  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.50/1.58  tff(c_1374, plain, (![A_218]: (A_218='#skF_4' | ~r1_tarski(A_218, '#skF_4'))), inference(resolution, [status(thm)], [c_1371, c_2])).
% 3.50/1.58  tff(c_1455, plain, (![A_230]: (k9_relat_1('#skF_4', A_230)='#skF_4')), inference(resolution, [status(thm)], [c_1449, c_1374])).
% 3.50/1.58  tff(c_1335, plain, (![A_12]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_1329, c_24])).
% 3.50/1.58  tff(c_1639, plain, (![A_272, B_273, C_274, D_275]: (k7_relset_1(A_272, B_273, C_274, D_275)=k9_relat_1(C_274, D_275) | ~m1_subset_1(C_274, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.50/1.58  tff(c_1642, plain, (![A_272, B_273, D_275]: (k7_relset_1(A_272, B_273, '#skF_4', D_275)=k9_relat_1('#skF_4', D_275))), inference(resolution, [status(thm)], [c_1335, c_1639])).
% 3.50/1.58  tff(c_1647, plain, (![A_272, B_273, D_275]: (k7_relset_1(A_272, B_273, '#skF_4', D_275)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1455, c_1642])).
% 3.50/1.58  tff(c_1649, plain, (~r1_tarski('#skF_4', k1_tarski(k1_funct_1('#skF_4', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1647, c_56])).
% 3.50/1.58  tff(c_1652, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1332, c_1649])).
% 3.50/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.50/1.58  
% 3.50/1.58  Inference rules
% 3.50/1.58  ----------------------
% 3.50/1.58  #Ref     : 0
% 3.50/1.58  #Sup     : 318
% 3.50/1.58  #Fact    : 0
% 3.50/1.58  #Define  : 0
% 3.50/1.58  #Split   : 5
% 3.50/1.58  #Chain   : 0
% 3.50/1.58  #Close   : 0
% 3.50/1.58  
% 3.50/1.58  Ordering : KBO
% 3.50/1.58  
% 3.50/1.58  Simplification rules
% 3.50/1.58  ----------------------
% 3.50/1.58  #Subsume      : 17
% 3.50/1.58  #Demod        : 340
% 3.50/1.58  #Tautology    : 180
% 3.50/1.58  #SimpNegUnit  : 1
% 3.50/1.58  #BackRed      : 31
% 3.50/1.58  
% 3.50/1.58  #Partial instantiations: 0
% 3.50/1.58  #Strategies tried      : 1
% 3.50/1.58  
% 3.50/1.58  Timing (in seconds)
% 3.50/1.58  ----------------------
% 3.50/1.58  Preprocessing        : 0.33
% 3.50/1.58  Parsing              : 0.18
% 3.50/1.58  CNF conversion       : 0.02
% 3.50/1.58  Main loop            : 0.48
% 3.50/1.58  Inferencing          : 0.17
% 3.50/1.58  Reduction            : 0.16
% 3.50/1.58  Demodulation         : 0.12
% 3.50/1.58  BG Simplification    : 0.02
% 3.50/1.58  Subsumption          : 0.09
% 3.50/1.58  Abstraction          : 0.02
% 3.50/1.58  MUC search           : 0.00
% 3.50/1.58  Cooper               : 0.00
% 3.50/1.58  Total                : 0.85
% 3.50/1.58  Index Insertion      : 0.00
% 3.50/1.58  Index Deletion       : 0.00
% 3.50/1.58  Index Matching       : 0.00
% 3.50/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
