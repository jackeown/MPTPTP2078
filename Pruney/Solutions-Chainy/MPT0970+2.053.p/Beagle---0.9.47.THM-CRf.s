%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:26 EST 2020

% Result     : Theorem 6.27s
% Output     : CNFRefutation 6.73s
% Verified   : 
% Statistics : Number of formulae       :  238 (2555 expanded)
%              Number of leaves         :   40 ( 892 expanded)
%              Depth                    :   24
%              Number of atoms          :  523 (7712 expanded)
%              Number of equality atoms :  126 (2112 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_120,negated_conjecture,(
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

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
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

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_7'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_155,plain,(
    ! [A_106,B_107,C_108] :
      ( k2_relset_1(A_106,B_107,C_108) = k2_relat_1(C_108)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_106,B_107))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_159,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') = k2_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_155])).

tff(c_58,plain,(
    k2_relset_1('#skF_6','#skF_7','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_160,plain,(
    k2_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_58])).

tff(c_16,plain,(
    ! [A_12,B_13] : v1_relat_1(k2_zfmisc_1(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_87,plain,(
    ! [B_81,A_82] :
      ( v1_relat_1(B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_82))
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_90,plain,
    ( v1_relat_1('#skF_8')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_60,c_87])).

tff(c_93,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_90])).

tff(c_119,plain,(
    ! [C_92,B_93,A_94] :
      ( v5_relat_1(C_92,B_93)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_94,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_123,plain,(
    v5_relat_1('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_119])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v5_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_124,plain,(
    ! [C_95,B_96,A_97] :
      ( r2_hidden(C_95,B_96)
      | ~ r2_hidden(C_95,A_97)
      | ~ r1_tarski(A_97,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5004,plain,(
    ! [A_534,B_535,B_536] :
      ( r2_hidden('#skF_1'(A_534,B_535),B_536)
      | ~ r1_tarski(A_534,B_536)
      | r1_tarski(A_534,B_535) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1556,plain,(
    ! [A_269,B_270] :
      ( r2_hidden('#skF_3'(A_269,B_270),k1_relat_1(A_269))
      | r2_hidden('#skF_4'(A_269,B_270),B_270)
      | k2_relat_1(A_269) = B_270
      | ~ v1_funct_1(A_269)
      | ~ v1_relat_1(A_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95,plain,(
    ! [A_85,B_86] :
      ( r2_hidden('#skF_1'(A_85,B_86),A_85)
      | r1_tarski(A_85,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_103,plain,(
    ! [A_85] : r1_tarski(A_85,A_85) ),
    inference(resolution,[status(thm)],[c_95,c_4])).

tff(c_267,plain,(
    ! [A_128,B_129,C_130] :
      ( k1_relset_1(A_128,B_129,C_130) = k1_relat_1(C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_128,B_129))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_271,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_267])).

tff(c_1279,plain,(
    ! [B_251,A_252,C_253] :
      ( k1_xboole_0 = B_251
      | k1_relset_1(A_252,B_251,C_253) = A_252
      | ~ v1_funct_2(C_253,A_252,B_251)
      | ~ m1_subset_1(C_253,k1_zfmisc_1(k2_zfmisc_1(A_252,B_251))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1282,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_1279])).

tff(c_1285,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_271,c_1282])).

tff(c_1286,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1285])).

tff(c_68,plain,(
    ! [D_71] :
      ( r2_hidden('#skF_9'(D_71),'#skF_6')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_130,plain,(
    ! [D_71,B_96] :
      ( r2_hidden('#skF_9'(D_71),B_96)
      | ~ r1_tarski('#skF_6',B_96)
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_124])).

tff(c_66,plain,(
    ! [D_71] :
      ( k1_funct_1('#skF_8','#skF_9'(D_71)) = D_71
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_297,plain,(
    ! [A_140,D_141] :
      ( r2_hidden(k1_funct_1(A_140,D_141),k2_relat_1(A_140))
      | ~ r2_hidden(D_141,k1_relat_1(A_140))
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_305,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_297])).

tff(c_310,plain,(
    ! [D_142] :
      ( r2_hidden(D_142,k2_relat_1('#skF_8'))
      | ~ r2_hidden('#skF_9'(D_142),k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_142,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_305])).

tff(c_315,plain,(
    ! [D_71] :
      ( r2_hidden(D_71,k2_relat_1('#skF_8'))
      | ~ r1_tarski('#skF_6',k1_relat_1('#skF_8'))
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_130,c_310])).

tff(c_316,plain,(
    ~ r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_1289,plain,(
    ~ r1_tarski('#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1286,c_316])).

tff(c_1294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_1289])).

tff(c_1295,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1285])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_192,plain,(
    ! [A_114,B_115,B_116] :
      ( r2_hidden('#skF_1'(A_114,B_115),B_116)
      | ~ r1_tarski(A_114,B_116)
      | r1_tarski(A_114,B_115) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_36,plain,(
    ! [B_55,A_54] :
      ( ~ r1_tarski(B_55,A_54)
      | ~ r2_hidden(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_205,plain,(
    ! [B_117,A_118,B_119] :
      ( ~ r1_tarski(B_117,'#skF_1'(A_118,B_119))
      | ~ r1_tarski(A_118,B_117)
      | r1_tarski(A_118,B_119) ) ),
    inference(resolution,[status(thm)],[c_192,c_36])).

tff(c_222,plain,(
    ! [A_121,B_122] :
      ( ~ r1_tarski(A_121,k1_xboole_0)
      | r1_tarski(A_121,B_122) ) ),
    inference(resolution,[status(thm)],[c_8,c_205])).

tff(c_237,plain,(
    ! [B_123,B_124] :
      ( r1_tarski(k2_relat_1(B_123),B_124)
      | ~ v5_relat_1(B_123,k1_xboole_0)
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_14,c_222])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( v5_relat_1(B_11,A_10)
      | ~ r1_tarski(k2_relat_1(B_11),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_262,plain,(
    ! [B_123,B_124] :
      ( v5_relat_1(B_123,B_124)
      | ~ v5_relat_1(B_123,k1_xboole_0)
      | ~ v1_relat_1(B_123) ) ),
    inference(resolution,[status(thm)],[c_237,c_12])).

tff(c_1364,plain,(
    ! [B_260,B_261] :
      ( v5_relat_1(B_260,B_261)
      | ~ v5_relat_1(B_260,'#skF_7')
      | ~ v1_relat_1(B_260) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_262])).

tff(c_1366,plain,(
    ! [B_261] :
      ( v5_relat_1('#skF_8',B_261)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_123,c_1364])).

tff(c_1373,plain,(
    ! [B_262] : v5_relat_1('#skF_8',B_262) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1366])).

tff(c_317,plain,(
    ! [A_143,D_144] :
      ( ~ r1_tarski(k2_relat_1(A_143),k1_funct_1(A_143,D_144))
      | ~ r2_hidden(D_144,k1_relat_1(A_143))
      | ~ v1_funct_1(A_143)
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_297,c_36])).

tff(c_330,plain,(
    ! [D_144,B_11] :
      ( ~ r2_hidden(D_144,k1_relat_1(B_11))
      | ~ v1_funct_1(B_11)
      | ~ v5_relat_1(B_11,k1_funct_1(B_11,D_144))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_317])).

tff(c_1384,plain,(
    ! [D_144] :
      ( ~ r2_hidden(D_144,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1373,c_330])).

tff(c_1401,plain,(
    ! [D_144] : ~ r2_hidden(D_144,k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_1384])).

tff(c_1560,plain,(
    ! [B_270] :
      ( r2_hidden('#skF_4'('#skF_8',B_270),B_270)
      | k2_relat_1('#skF_8') = B_270
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1556,c_1401])).

tff(c_1608,plain,(
    ! [B_273] :
      ( r2_hidden('#skF_4'('#skF_8',B_273),B_273)
      | k2_relat_1('#skF_8') = B_273 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_1560])).

tff(c_1624,plain,(
    k2_relat_1('#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_1608,c_1401])).

tff(c_1667,plain,(
    k1_relat_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_160])).

tff(c_1314,plain,(
    ! [A_6] : r1_tarski('#skF_7',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1295,c_8])).

tff(c_1626,plain,(
    ! [B_273] :
      ( ~ r1_tarski(B_273,'#skF_4'('#skF_8',B_273))
      | k2_relat_1('#skF_8') = B_273 ) ),
    inference(resolution,[status(thm)],[c_1608,c_36])).

tff(c_1730,plain,(
    ! [B_276] :
      ( ~ r1_tarski(B_276,'#skF_4'('#skF_8',B_276))
      | k1_relat_1('#skF_8') = B_276 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1624,c_1626])).

tff(c_1738,plain,(
    k1_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1314,c_1730])).

tff(c_1748,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1667,c_1738])).

tff(c_1750,plain,(
    r1_tarski('#skF_6',k1_relat_1('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_129,plain,(
    ! [A_1,B_2,B_96] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_96)
      | ~ r1_tarski(A_1,B_96)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_2155,plain,(
    ! [B_319,A_320,C_321] :
      ( k1_xboole_0 = B_319
      | k1_relset_1(A_320,B_319,C_321) = A_320
      | ~ v1_funct_2(C_321,A_320,B_319)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_320,B_319))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2158,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_2155])).

tff(c_2161,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_271,c_2158])).

tff(c_2162,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2161])).

tff(c_3157,plain,(
    ! [A_406,B_407,D_408] :
      ( r2_hidden('#skF_3'(A_406,B_407),k1_relat_1(A_406))
      | k1_funct_1(A_406,D_408) != '#skF_4'(A_406,B_407)
      | ~ r2_hidden(D_408,k1_relat_1(A_406))
      | k2_relat_1(A_406) = B_407
      | ~ v1_funct_1(A_406)
      | ~ v1_relat_1(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3163,plain,(
    ! [B_407,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_407),k1_relat_1('#skF_8'))
      | D_71 != '#skF_4'('#skF_8',B_407)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_407
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_3157])).

tff(c_3165,plain,(
    ! [B_407,D_71] :
      ( r2_hidden('#skF_3'('#skF_8',B_407),'#skF_6')
      | D_71 != '#skF_4'('#skF_8',B_407)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_407
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_2162,c_2162,c_3163])).

tff(c_3614,plain,(
    ! [B_462] :
      ( r2_hidden('#skF_3'('#skF_8',B_462),'#skF_6')
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_462)),'#skF_6')
      | k2_relat_1('#skF_8') = B_462
      | ~ r2_hidden('#skF_4'('#skF_8',B_462),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3165])).

tff(c_3617,plain,(
    ! [B_462] :
      ( r2_hidden('#skF_3'('#skF_8',B_462),'#skF_6')
      | k2_relat_1('#skF_8') = B_462
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_462),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_130,c_3614])).

tff(c_3623,plain,(
    ! [B_462] :
      ( r2_hidden('#skF_3'('#skF_8',B_462),'#skF_6')
      | k2_relat_1('#skF_8') = B_462
      | ~ r2_hidden('#skF_4'('#skF_8',B_462),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_3617])).

tff(c_32,plain,(
    ! [A_14,B_36] :
      ( k1_funct_1(A_14,'#skF_3'(A_14,B_36)) = '#skF_2'(A_14,B_36)
      | r2_hidden('#skF_4'(A_14,B_36),B_36)
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3268,plain,(
    ! [A_423,B_424,D_425] :
      ( k1_funct_1(A_423,'#skF_3'(A_423,B_424)) = '#skF_2'(A_423,B_424)
      | k1_funct_1(A_423,D_425) != '#skF_4'(A_423,B_424)
      | ~ r2_hidden(D_425,k1_relat_1(A_423))
      | k2_relat_1(A_423) = B_424
      | ~ v1_funct_1(A_423)
      | ~ v1_relat_1(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3274,plain,(
    ! [B_424,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_424)) = '#skF_2'('#skF_8',B_424)
      | D_71 != '#skF_4'('#skF_8',B_424)
      | ~ r2_hidden('#skF_9'(D_71),k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = B_424
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_3268])).

tff(c_3276,plain,(
    ! [B_424,D_71] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_424)) = '#skF_2'('#skF_8',B_424)
      | D_71 != '#skF_4'('#skF_8',B_424)
      | ~ r2_hidden('#skF_9'(D_71),'#skF_6')
      | k2_relat_1('#skF_8') = B_424
      | ~ r2_hidden(D_71,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_2162,c_3274])).

tff(c_3770,plain,(
    ! [B_476] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_476)) = '#skF_2'('#skF_8',B_476)
      | ~ r2_hidden('#skF_9'('#skF_4'('#skF_8',B_476)),'#skF_6')
      | k2_relat_1('#skF_8') = B_476
      | ~ r2_hidden('#skF_4'('#skF_8',B_476),'#skF_7') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_3276])).

tff(c_3773,plain,(
    ! [B_476] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_476)) = '#skF_2'('#skF_8',B_476)
      | k2_relat_1('#skF_8') = B_476
      | ~ r1_tarski('#skF_6','#skF_6')
      | ~ r2_hidden('#skF_4'('#skF_8',B_476),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_130,c_3770])).

tff(c_3781,plain,(
    ! [B_477] :
      ( k1_funct_1('#skF_8','#skF_3'('#skF_8',B_477)) = '#skF_2'('#skF_8',B_477)
      | k2_relat_1('#skF_8') = B_477
      | ~ r2_hidden('#skF_4'('#skF_8',B_477),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_3773])).

tff(c_3797,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_3781])).

tff(c_3813,plain,
    ( k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_3797])).

tff(c_3814,plain,(
    k1_funct_1('#skF_8','#skF_3'('#skF_8','#skF_7')) = '#skF_2'('#skF_8','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_3813])).

tff(c_307,plain,(
    ! [A_140,D_141] :
      ( ~ r1_tarski(k2_relat_1(A_140),k1_funct_1(A_140,D_141))
      | ~ r2_hidden(D_141,k1_relat_1(A_140))
      | ~ v1_funct_1(A_140)
      | ~ v1_relat_1(A_140) ) ),
    inference(resolution,[status(thm)],[c_297,c_36])).

tff(c_3831,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_2'('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3814,c_307])).

tff(c_3847,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_2'('#skF_8','#skF_7'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_2162,c_3831])).

tff(c_3852,plain,(
    ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_3847])).

tff(c_3875,plain,
    ( k2_relat_1('#skF_8') = '#skF_7'
    | ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_3623,c_3852])).

tff(c_3894,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_3875])).

tff(c_2718,plain,(
    ! [A_380,B_381] :
      ( r2_hidden('#skF_3'(A_380,B_381),k1_relat_1(A_380))
      | r2_hidden('#skF_4'(A_380,B_381),B_381)
      | k2_relat_1(A_380) = B_381
      | ~ v1_funct_1(A_380)
      | ~ v1_relat_1(A_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2743,plain,(
    ! [B_381] :
      ( r2_hidden('#skF_3'('#skF_8',B_381),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_381),B_381)
      | k2_relat_1('#skF_8') = B_381
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2162,c_2718])).

tff(c_2752,plain,(
    ! [B_381] :
      ( r2_hidden('#skF_3'('#skF_8',B_381),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_381),B_381)
      | k2_relat_1('#skF_8') = B_381 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_2743])).

tff(c_3887,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_2752,c_3852])).

tff(c_3907,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_3887])).

tff(c_3938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3894,c_3907])).

tff(c_3940,plain,(
    r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_3847])).

tff(c_18,plain,(
    ! [A_14,D_53] :
      ( r2_hidden(k1_funct_1(A_14,D_53),k2_relat_1(A_14))
      | ~ r2_hidden(D_53,k1_relat_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3834,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),k1_relat_1('#skF_8'))
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3814,c_18])).

tff(c_3849,plain,
    ( r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8'))
    | ~ r2_hidden('#skF_3'('#skF_8','#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_2162,c_3834])).

tff(c_4030,plain,(
    r2_hidden('#skF_2'('#skF_8','#skF_7'),k2_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3940,c_3849])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4044,plain,(
    ! [B_484] :
      ( r2_hidden('#skF_2'('#skF_8','#skF_7'),B_484)
      | ~ r1_tarski(k2_relat_1('#skF_8'),B_484) ) ),
    inference(resolution,[status(thm)],[c_4030,c_2])).

tff(c_30,plain,(
    ! [A_14,B_36] :
      ( ~ r2_hidden('#skF_2'(A_14,B_36),B_36)
      | r2_hidden('#skF_4'(A_14,B_36),B_36)
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4054,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_4044,c_30])).

tff(c_4078,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | k2_relat_1('#skF_8') = '#skF_7'
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_4054])).

tff(c_4079,plain,
    ( r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7')
    | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_4078])).

tff(c_4085,plain,(
    ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4079])).

tff(c_4091,plain,
    ( ~ v5_relat_1('#skF_8','#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_14,c_4085])).

tff(c_4098,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_123,c_4091])).

tff(c_4100,plain,(
    r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4079])).

tff(c_24,plain,(
    ! [A_14,B_36,D_49] :
      ( ~ r2_hidden('#skF_2'(A_14,B_36),B_36)
      | k1_funct_1(A_14,D_49) != '#skF_4'(A_14,B_36)
      | ~ r2_hidden(D_49,k1_relat_1(A_14))
      | k2_relat_1(A_14) = B_36
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4050,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,k1_relat_1('#skF_8'))
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_4044,c_24])).

tff(c_4074,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | k2_relat_1('#skF_8') = '#skF_7'
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_2162,c_4050])).

tff(c_4075,plain,(
    ! [D_49] :
      ( k1_funct_1('#skF_8',D_49) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_49,'#skF_6')
      | ~ r1_tarski(k2_relat_1('#skF_8'),'#skF_7') ) ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_4074])).

tff(c_4307,plain,(
    ! [D_491] :
      ( k1_funct_1('#skF_8',D_491) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_491,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4100,c_4075])).

tff(c_4535,plain,(
    ! [D_496] :
      ( k1_funct_1('#skF_8','#skF_9'(D_496)) != '#skF_4'('#skF_8','#skF_7')
      | ~ r2_hidden(D_496,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_4307])).

tff(c_4558,plain,(
    ~ r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4535])).

tff(c_4099,plain,(
    r2_hidden('#skF_4'('#skF_8','#skF_7'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4079])).

tff(c_4560,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4558,c_4099])).

tff(c_4561,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2161])).

tff(c_232,plain,(
    ! [B_11,B_122] :
      ( r1_tarski(k2_relat_1(B_11),B_122)
      | ~ v5_relat_1(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_222])).

tff(c_1756,plain,(
    ! [D_277] :
      ( r2_hidden(D_277,k2_relat_1('#skF_8'))
      | ~ r2_hidden(D_277,'#skF_7') ) ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_1769,plain,(
    ! [D_278] :
      ( ~ r1_tarski(k2_relat_1('#skF_8'),D_278)
      | ~ r2_hidden(D_278,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1756,c_36])).

tff(c_1773,plain,(
    ! [B_122] :
      ( ~ r2_hidden(B_122,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_232,c_1769])).

tff(c_1784,plain,(
    ! [B_122] :
      ( ~ r2_hidden(B_122,'#skF_7')
      | ~ v5_relat_1('#skF_8',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_1773])).

tff(c_1802,plain,(
    ~ v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1784])).

tff(c_4577,plain,(
    ~ v5_relat_1('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4561,c_1802])).

tff(c_4590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_4577])).

tff(c_4592,plain,(
    v5_relat_1('#skF_8',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1784])).

tff(c_4605,plain,(
    ! [B_124] :
      ( v5_relat_1('#skF_8',B_124)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4592,c_262])).

tff(c_4633,plain,(
    ! [B_503] : v5_relat_1('#skF_8',B_503) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_4605])).

tff(c_107,plain,(
    ! [A_90,B_91] :
      ( ~ r1_tarski(A_90,'#skF_1'(A_90,B_91))
      | r1_tarski(A_90,B_91) ) ),
    inference(resolution,[status(thm)],[c_95,c_36])).

tff(c_116,plain,(
    ! [B_11,B_91] :
      ( r1_tarski(k2_relat_1(B_11),B_91)
      | ~ v5_relat_1(B_11,'#skF_1'(k2_relat_1(B_11),B_91))
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_107])).

tff(c_4637,plain,(
    ! [B_91] :
      ( r1_tarski(k2_relat_1('#skF_8'),B_91)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4633,c_116])).

tff(c_4643,plain,(
    ! [B_91] : r1_tarski(k2_relat_1('#skF_8'),B_91) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_4637])).

tff(c_4827,plain,(
    ! [A_522,D_523] :
      ( ~ r1_tarski(k2_relat_1(A_522),k1_funct_1(A_522,D_523))
      | ~ r2_hidden(D_523,k1_relat_1(A_522))
      | ~ v1_funct_1(A_522)
      | ~ v1_relat_1(A_522) ) ),
    inference(resolution,[status(thm)],[c_297,c_36])).

tff(c_4835,plain,(
    ! [D_523] :
      ( ~ r2_hidden(D_523,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4643,c_4827])).

tff(c_4850,plain,(
    ! [D_524] : ~ r2_hidden(D_524,k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_4835])).

tff(c_4939,plain,(
    ! [A_529,B_530] :
      ( ~ r1_tarski(A_529,k1_relat_1('#skF_8'))
      | r1_tarski(A_529,B_530) ) ),
    inference(resolution,[status(thm)],[c_129,c_4850])).

tff(c_4973,plain,(
    ! [B_530] : r1_tarski('#skF_6',B_530) ),
    inference(resolution,[status(thm)],[c_1750,c_4939])).

tff(c_147,plain,(
    ! [D_104,B_105] :
      ( r2_hidden('#skF_9'(D_104),B_105)
      | ~ r1_tarski('#skF_6',B_105)
      | ~ r2_hidden(D_104,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_68,c_124])).

tff(c_165,plain,(
    ! [B_109,D_110] :
      ( ~ r1_tarski(B_109,'#skF_9'(D_110))
      | ~ r1_tarski('#skF_6',B_109)
      | ~ r2_hidden(D_110,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_147,c_36])).

tff(c_180,plain,(
    ! [D_110] :
      ( ~ r1_tarski('#skF_6',k1_xboole_0)
      | ~ r2_hidden(D_110,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_8,c_165])).

tff(c_191,plain,(
    ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_4985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4973,c_191])).

tff(c_4986,plain,(
    ! [D_110] : ~ r2_hidden(D_110,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_5022,plain,(
    ! [A_537,B_538] :
      ( ~ r1_tarski(A_537,'#skF_7')
      | r1_tarski(A_537,B_538) ) ),
    inference(resolution,[status(thm)],[c_5004,c_4986])).

tff(c_5042,plain,(
    ! [B_539,B_540] :
      ( r1_tarski(k2_relat_1(B_539),B_540)
      | ~ v5_relat_1(B_539,'#skF_7')
      | ~ v1_relat_1(B_539) ) ),
    inference(resolution,[status(thm)],[c_14,c_5022])).

tff(c_5056,plain,(
    ! [B_541,B_542] :
      ( v5_relat_1(B_541,B_542)
      | ~ v5_relat_1(B_541,'#skF_7')
      | ~ v1_relat_1(B_541) ) ),
    inference(resolution,[status(thm)],[c_5042,c_12])).

tff(c_5058,plain,(
    ! [B_542] :
      ( v5_relat_1('#skF_8',B_542)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_123,c_5056])).

tff(c_5061,plain,(
    ! [B_542] : v5_relat_1('#skF_8',B_542) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_5058])).

tff(c_5096,plain,(
    ! [A_547,B_548,C_549] :
      ( k1_relset_1(A_547,B_548,C_549) = k1_relat_1(C_549)
      | ~ m1_subset_1(C_549,k1_zfmisc_1(k2_zfmisc_1(A_547,B_548))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5100,plain,(
    k1_relset_1('#skF_6','#skF_7','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_5096])).

tff(c_6192,plain,(
    ! [B_655,A_656,C_657] :
      ( k1_xboole_0 = B_655
      | k1_relset_1(A_656,B_655,C_657) = A_656
      | ~ v1_funct_2(C_657,A_656,B_655)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(k2_zfmisc_1(A_656,B_655))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6195,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relset_1('#skF_6','#skF_7','#skF_8') = '#skF_6'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_60,c_6192])).

tff(c_6198,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_relat_1('#skF_8') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_5100,c_6195])).

tff(c_6199,plain,(
    k1_relat_1('#skF_8') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6198])).

tff(c_5070,plain,(
    ! [B_544,A_545,B_546] :
      ( ~ r1_tarski(B_544,'#skF_1'(A_545,B_546))
      | ~ r1_tarski(A_545,B_544)
      | r1_tarski(A_545,B_546) ) ),
    inference(resolution,[status(thm)],[c_5004,c_36])).

tff(c_5105,plain,(
    ! [A_550,B_551] :
      ( ~ r1_tarski(A_550,k1_xboole_0)
      | r1_tarski(A_550,B_551) ) ),
    inference(resolution,[status(thm)],[c_8,c_5070])).

tff(c_5127,plain,(
    ! [B_11,B_551] :
      ( r1_tarski(k2_relat_1(B_11),B_551)
      | ~ v5_relat_1(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_14,c_5105])).

tff(c_5474,plain,(
    ! [A_581,D_582] :
      ( r2_hidden(k1_funct_1(A_581,D_582),k2_relat_1(A_581))
      | ~ r2_hidden(D_582,k1_relat_1(A_581))
      | ~ v1_funct_1(A_581)
      | ~ v1_relat_1(A_581) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5482,plain,(
    ! [A_583,D_584] :
      ( ~ r1_tarski(k2_relat_1(A_583),k1_funct_1(A_583,D_584))
      | ~ r2_hidden(D_584,k1_relat_1(A_583))
      | ~ v1_funct_1(A_583)
      | ~ v1_relat_1(A_583) ) ),
    inference(resolution,[status(thm)],[c_5474,c_36])).

tff(c_5507,plain,(
    ! [D_584,B_11] :
      ( ~ r2_hidden(D_584,k1_relat_1(B_11))
      | ~ v1_funct_1(B_11)
      | ~ v5_relat_1(B_11,k1_xboole_0)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_5127,c_5482])).

tff(c_6235,plain,(
    ! [D_584] :
      ( ~ r2_hidden(D_584,'#skF_6')
      | ~ v1_funct_1('#skF_8')
      | ~ v5_relat_1('#skF_8',k1_xboole_0)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6199,c_5507])).

tff(c_6262,plain,(
    ! [D_584] : ~ r2_hidden(D_584,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_5061,c_64,c_6235])).

tff(c_6278,plain,(
    ! [A_659,B_660] :
      ( r2_hidden('#skF_3'(A_659,B_660),k1_relat_1(A_659))
      | r2_hidden('#skF_4'(A_659,B_660),B_660)
      | k2_relat_1(A_659) = B_660
      | ~ v1_funct_1(A_659)
      | ~ v1_relat_1(A_659) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6330,plain,(
    ! [B_660] :
      ( r2_hidden('#skF_3'('#skF_8',B_660),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_660),B_660)
      | k2_relat_1('#skF_8') = B_660
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6199,c_6278])).

tff(c_6345,plain,(
    ! [B_660] :
      ( r2_hidden('#skF_3'('#skF_8',B_660),'#skF_6')
      | r2_hidden('#skF_4'('#skF_8',B_660),B_660)
      | k2_relat_1('#skF_8') = B_660 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_6330])).

tff(c_6351,plain,(
    ! [B_661] :
      ( r2_hidden('#skF_4'('#skF_8',B_661),B_661)
      | k2_relat_1('#skF_8') = B_661 ) ),
    inference(negUnitSimplification,[status(thm)],[c_6262,c_6345])).

tff(c_6387,plain,(
    k2_relat_1('#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_6351,c_4986])).

tff(c_6405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_6387])).

tff(c_6406,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_6198])).

tff(c_48,plain,(
    ! [C_67,A_65] :
      ( k1_xboole_0 = C_67
      | ~ v1_funct_2(C_67,A_65,k1_xboole_0)
      | k1_xboole_0 = A_65
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_6430,plain,(
    ! [C_663,A_664] :
      ( C_663 = '#skF_7'
      | ~ v1_funct_2(C_663,A_664,'#skF_7')
      | A_664 = '#skF_7'
      | ~ m1_subset_1(C_663,k1_zfmisc_1(k2_zfmisc_1(A_664,'#skF_7'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6406,c_6406,c_6406,c_6406,c_48])).

tff(c_6433,plain,
    ( '#skF_7' = '#skF_8'
    | ~ v1_funct_2('#skF_8','#skF_6','#skF_7')
    | '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_60,c_6430])).

tff(c_6436,plain,
    ( '#skF_7' = '#skF_8'
    | '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_6433])).

tff(c_6437,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_6436])).

tff(c_6510,plain,(
    k2_relat_1('#skF_8') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6437,c_160])).

tff(c_6438,plain,(
    ! [A_665,B_666] :
      ( r2_hidden('#skF_3'(A_665,B_666),k1_relat_1(A_665))
      | r2_hidden('#skF_4'(A_665,B_666),B_666)
      | k2_relat_1(A_665) = B_666
      | ~ v1_funct_1(A_665)
      | ~ v1_relat_1(A_665) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5255,plain,(
    ! [B_565,B_566] :
      ( r1_tarski(k2_relat_1(B_565),B_566)
      | ~ v5_relat_1(B_565,'#skF_1'(k2_relat_1(B_565),B_566))
      | ~ v1_relat_1(B_565) ) ),
    inference(resolution,[status(thm)],[c_14,c_107])).

tff(c_5259,plain,(
    ! [B_566] :
      ( r1_tarski(k2_relat_1('#skF_8'),B_566)
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5061,c_5255])).

tff(c_5262,plain,(
    ! [B_566] : r1_tarski(k2_relat_1('#skF_8'),B_566) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_5259])).

tff(c_5486,plain,(
    ! [D_584] :
      ( ~ r2_hidden(D_584,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_5262,c_5482])).

tff(c_5505,plain,(
    ! [D_584] : ~ r2_hidden(D_584,k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_5486])).

tff(c_6448,plain,(
    ! [B_666] :
      ( r2_hidden('#skF_4'('#skF_8',B_666),B_666)
      | k2_relat_1('#skF_8') = B_666
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_6438,c_5505])).

tff(c_6621,plain,(
    ! [B_670] :
      ( r2_hidden('#skF_4'('#skF_8',B_670),B_670)
      | k2_relat_1('#skF_8') = B_670 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_6448])).

tff(c_6509,plain,(
    ! [D_110] : ~ r2_hidden(D_110,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6437,c_4986])).

tff(c_6625,plain,(
    k2_relat_1('#skF_8') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_6621,c_6509])).

tff(c_6650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6510,c_6625])).

tff(c_6651,plain,(
    '#skF_7' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_6436])).

tff(c_6669,plain,(
    k2_relat_1('#skF_8') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6651,c_160])).

tff(c_6733,plain,(
    ! [A_673,B_674] :
      ( r2_hidden('#skF_3'(A_673,B_674),k1_relat_1(A_673))
      | r2_hidden('#skF_4'(A_673,B_674),B_674)
      | k2_relat_1(A_673) = B_674
      | ~ v1_funct_1(A_673)
      | ~ v1_relat_1(A_673) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6740,plain,(
    ! [B_674] :
      ( r2_hidden('#skF_4'('#skF_8',B_674),B_674)
      | k2_relat_1('#skF_8') = B_674
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(resolution,[status(thm)],[c_6733,c_5505])).

tff(c_6855,plain,(
    ! [B_679] :
      ( r2_hidden('#skF_4'('#skF_8',B_679),B_679)
      | k2_relat_1('#skF_8') = B_679 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_64,c_6740])).

tff(c_6668,plain,(
    ! [D_110] : ~ r2_hidden(D_110,'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6651,c_4986])).

tff(c_6859,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6855,c_6668])).

tff(c_6884,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6669,c_6859])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:42:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.27/2.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.28  
% 6.27/2.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.27/2.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_7 > #skF_3 > #skF_6 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 6.27/2.28  
% 6.27/2.28  %Foreground sorts:
% 6.27/2.28  
% 6.27/2.28  
% 6.27/2.28  %Background operators:
% 6.27/2.28  
% 6.27/2.28  
% 6.27/2.28  %Foreground operators:
% 6.27/2.28  tff('#skF_9', type, '#skF_9': $i > $i).
% 6.27/2.28  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.27/2.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.27/2.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.27/2.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.27/2.28  tff('#skF_7', type, '#skF_7': $i).
% 6.27/2.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.27/2.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.27/2.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.27/2.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.27/2.28  tff('#skF_6', type, '#skF_6': $i).
% 6.27/2.28  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.27/2.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.27/2.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.27/2.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.27/2.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 6.27/2.28  tff('#skF_8', type, '#skF_8': $i).
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.27/2.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.27/2.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.27/2.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.27/2.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.27/2.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.27/2.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.27/2.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.27/2.28  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.27/2.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.27/2.28  
% 6.73/2.31  tff(f_120, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_2)).
% 6.73/2.31  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.73/2.31  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.73/2.31  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.73/2.31  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.73/2.31  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 6.73/2.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 6.73/2.31  tff(f_64, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 6.73/2.31  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.73/2.31  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.73/2.31  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.73/2.31  tff(f_69, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 6.73/2.31  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.73/2.31  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_7')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.73/2.31  tff(c_155, plain, (![A_106, B_107, C_108]: (k2_relset_1(A_106, B_107, C_108)=k2_relat_1(C_108) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_106, B_107))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.73/2.31  tff(c_159, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')=k2_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_155])).
% 6.73/2.31  tff(c_58, plain, (k2_relset_1('#skF_6', '#skF_7', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.73/2.31  tff(c_160, plain, (k2_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_58])).
% 6.73/2.31  tff(c_16, plain, (![A_12, B_13]: (v1_relat_1(k2_zfmisc_1(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.73/2.31  tff(c_87, plain, (![B_81, A_82]: (v1_relat_1(B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_82)) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.73/2.31  tff(c_90, plain, (v1_relat_1('#skF_8') | ~v1_relat_1(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_60, c_87])).
% 6.73/2.31  tff(c_93, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_90])).
% 6.73/2.31  tff(c_119, plain, (![C_92, B_93, A_94]: (v5_relat_1(C_92, B_93) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_94, B_93))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.73/2.31  tff(c_123, plain, (v5_relat_1('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_119])).
% 6.73/2.31  tff(c_14, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(B_11), A_10) | ~v5_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.73/2.31  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.73/2.31  tff(c_124, plain, (![C_95, B_96, A_97]: (r2_hidden(C_95, B_96) | ~r2_hidden(C_95, A_97) | ~r1_tarski(A_97, B_96))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.73/2.31  tff(c_5004, plain, (![A_534, B_535, B_536]: (r2_hidden('#skF_1'(A_534, B_535), B_536) | ~r1_tarski(A_534, B_536) | r1_tarski(A_534, B_535))), inference(resolution, [status(thm)], [c_6, c_124])).
% 6.73/2.31  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.73/2.31  tff(c_1556, plain, (![A_269, B_270]: (r2_hidden('#skF_3'(A_269, B_270), k1_relat_1(A_269)) | r2_hidden('#skF_4'(A_269, B_270), B_270) | k2_relat_1(A_269)=B_270 | ~v1_funct_1(A_269) | ~v1_relat_1(A_269))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_95, plain, (![A_85, B_86]: (r2_hidden('#skF_1'(A_85, B_86), A_85) | r1_tarski(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.73/2.31  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.73/2.31  tff(c_103, plain, (![A_85]: (r1_tarski(A_85, A_85))), inference(resolution, [status(thm)], [c_95, c_4])).
% 6.73/2.31  tff(c_267, plain, (![A_128, B_129, C_130]: (k1_relset_1(A_128, B_129, C_130)=k1_relat_1(C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(k2_zfmisc_1(A_128, B_129))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.73/2.31  tff(c_271, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_267])).
% 6.73/2.31  tff(c_1279, plain, (![B_251, A_252, C_253]: (k1_xboole_0=B_251 | k1_relset_1(A_252, B_251, C_253)=A_252 | ~v1_funct_2(C_253, A_252, B_251) | ~m1_subset_1(C_253, k1_zfmisc_1(k2_zfmisc_1(A_252, B_251))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.73/2.31  tff(c_1282, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_1279])).
% 6.73/2.31  tff(c_1285, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_271, c_1282])).
% 6.73/2.31  tff(c_1286, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_1285])).
% 6.73/2.31  tff(c_68, plain, (![D_71]: (r2_hidden('#skF_9'(D_71), '#skF_6') | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.73/2.31  tff(c_130, plain, (![D_71, B_96]: (r2_hidden('#skF_9'(D_71), B_96) | ~r1_tarski('#skF_6', B_96) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_124])).
% 6.73/2.31  tff(c_66, plain, (![D_71]: (k1_funct_1('#skF_8', '#skF_9'(D_71))=D_71 | ~r2_hidden(D_71, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.73/2.31  tff(c_297, plain, (![A_140, D_141]: (r2_hidden(k1_funct_1(A_140, D_141), k2_relat_1(A_140)) | ~r2_hidden(D_141, k1_relat_1(A_140)) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_305, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_297])).
% 6.73/2.31  tff(c_310, plain, (![D_142]: (r2_hidden(D_142, k2_relat_1('#skF_8')) | ~r2_hidden('#skF_9'(D_142), k1_relat_1('#skF_8')) | ~r2_hidden(D_142, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_305])).
% 6.73/2.31  tff(c_315, plain, (![D_71]: (r2_hidden(D_71, k2_relat_1('#skF_8')) | ~r1_tarski('#skF_6', k1_relat_1('#skF_8')) | ~r2_hidden(D_71, '#skF_7'))), inference(resolution, [status(thm)], [c_130, c_310])).
% 6.73/2.31  tff(c_316, plain, (~r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitLeft, [status(thm)], [c_315])).
% 6.73/2.31  tff(c_1289, plain, (~r1_tarski('#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1286, c_316])).
% 6.73/2.31  tff(c_1294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_1289])).
% 6.73/2.31  tff(c_1295, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_1285])).
% 6.73/2.31  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.73/2.31  tff(c_192, plain, (![A_114, B_115, B_116]: (r2_hidden('#skF_1'(A_114, B_115), B_116) | ~r1_tarski(A_114, B_116) | r1_tarski(A_114, B_115))), inference(resolution, [status(thm)], [c_6, c_124])).
% 6.73/2.31  tff(c_36, plain, (![B_55, A_54]: (~r1_tarski(B_55, A_54) | ~r2_hidden(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.73/2.31  tff(c_205, plain, (![B_117, A_118, B_119]: (~r1_tarski(B_117, '#skF_1'(A_118, B_119)) | ~r1_tarski(A_118, B_117) | r1_tarski(A_118, B_119))), inference(resolution, [status(thm)], [c_192, c_36])).
% 6.73/2.31  tff(c_222, plain, (![A_121, B_122]: (~r1_tarski(A_121, k1_xboole_0) | r1_tarski(A_121, B_122))), inference(resolution, [status(thm)], [c_8, c_205])).
% 6.73/2.31  tff(c_237, plain, (![B_123, B_124]: (r1_tarski(k2_relat_1(B_123), B_124) | ~v5_relat_1(B_123, k1_xboole_0) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_14, c_222])).
% 6.73/2.31  tff(c_12, plain, (![B_11, A_10]: (v5_relat_1(B_11, A_10) | ~r1_tarski(k2_relat_1(B_11), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.73/2.31  tff(c_262, plain, (![B_123, B_124]: (v5_relat_1(B_123, B_124) | ~v5_relat_1(B_123, k1_xboole_0) | ~v1_relat_1(B_123))), inference(resolution, [status(thm)], [c_237, c_12])).
% 6.73/2.31  tff(c_1364, plain, (![B_260, B_261]: (v5_relat_1(B_260, B_261) | ~v5_relat_1(B_260, '#skF_7') | ~v1_relat_1(B_260))), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_262])).
% 6.73/2.31  tff(c_1366, plain, (![B_261]: (v5_relat_1('#skF_8', B_261) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_123, c_1364])).
% 6.73/2.31  tff(c_1373, plain, (![B_262]: (v5_relat_1('#skF_8', B_262))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1366])).
% 6.73/2.31  tff(c_317, plain, (![A_143, D_144]: (~r1_tarski(k2_relat_1(A_143), k1_funct_1(A_143, D_144)) | ~r2_hidden(D_144, k1_relat_1(A_143)) | ~v1_funct_1(A_143) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_297, c_36])).
% 6.73/2.31  tff(c_330, plain, (![D_144, B_11]: (~r2_hidden(D_144, k1_relat_1(B_11)) | ~v1_funct_1(B_11) | ~v5_relat_1(B_11, k1_funct_1(B_11, D_144)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_317])).
% 6.73/2.31  tff(c_1384, plain, (![D_144]: (~r2_hidden(D_144, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1373, c_330])).
% 6.73/2.31  tff(c_1401, plain, (![D_144]: (~r2_hidden(D_144, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_1384])).
% 6.73/2.31  tff(c_1560, plain, (![B_270]: (r2_hidden('#skF_4'('#skF_8', B_270), B_270) | k2_relat_1('#skF_8')=B_270 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_1556, c_1401])).
% 6.73/2.31  tff(c_1608, plain, (![B_273]: (r2_hidden('#skF_4'('#skF_8', B_273), B_273) | k2_relat_1('#skF_8')=B_273)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_1560])).
% 6.73/2.31  tff(c_1624, plain, (k2_relat_1('#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_1608, c_1401])).
% 6.73/2.31  tff(c_1667, plain, (k1_relat_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_160])).
% 6.73/2.31  tff(c_1314, plain, (![A_6]: (r1_tarski('#skF_7', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1295, c_8])).
% 6.73/2.31  tff(c_1626, plain, (![B_273]: (~r1_tarski(B_273, '#skF_4'('#skF_8', B_273)) | k2_relat_1('#skF_8')=B_273)), inference(resolution, [status(thm)], [c_1608, c_36])).
% 6.73/2.31  tff(c_1730, plain, (![B_276]: (~r1_tarski(B_276, '#skF_4'('#skF_8', B_276)) | k1_relat_1('#skF_8')=B_276)), inference(demodulation, [status(thm), theory('equality')], [c_1624, c_1626])).
% 6.73/2.31  tff(c_1738, plain, (k1_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_1314, c_1730])).
% 6.73/2.31  tff(c_1748, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1667, c_1738])).
% 6.73/2.31  tff(c_1750, plain, (r1_tarski('#skF_6', k1_relat_1('#skF_8'))), inference(splitRight, [status(thm)], [c_315])).
% 6.73/2.31  tff(c_129, plain, (![A_1, B_2, B_96]: (r2_hidden('#skF_1'(A_1, B_2), B_96) | ~r1_tarski(A_1, B_96) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_124])).
% 6.73/2.31  tff(c_2155, plain, (![B_319, A_320, C_321]: (k1_xboole_0=B_319 | k1_relset_1(A_320, B_319, C_321)=A_320 | ~v1_funct_2(C_321, A_320, B_319) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_320, B_319))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.73/2.31  tff(c_2158, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_2155])).
% 6.73/2.31  tff(c_2161, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_271, c_2158])).
% 6.73/2.31  tff(c_2162, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_2161])).
% 6.73/2.31  tff(c_3157, plain, (![A_406, B_407, D_408]: (r2_hidden('#skF_3'(A_406, B_407), k1_relat_1(A_406)) | k1_funct_1(A_406, D_408)!='#skF_4'(A_406, B_407) | ~r2_hidden(D_408, k1_relat_1(A_406)) | k2_relat_1(A_406)=B_407 | ~v1_funct_1(A_406) | ~v1_relat_1(A_406))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_3163, plain, (![B_407, D_71]: (r2_hidden('#skF_3'('#skF_8', B_407), k1_relat_1('#skF_8')) | D_71!='#skF_4'('#skF_8', B_407) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_407 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_3157])).
% 6.73/2.31  tff(c_3165, plain, (![B_407, D_71]: (r2_hidden('#skF_3'('#skF_8', B_407), '#skF_6') | D_71!='#skF_4'('#skF_8', B_407) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_407 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_2162, c_2162, c_3163])).
% 6.73/2.31  tff(c_3614, plain, (![B_462]: (r2_hidden('#skF_3'('#skF_8', B_462), '#skF_6') | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_462)), '#skF_6') | k2_relat_1('#skF_8')=B_462 | ~r2_hidden('#skF_4'('#skF_8', B_462), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_3165])).
% 6.73/2.31  tff(c_3617, plain, (![B_462]: (r2_hidden('#skF_3'('#skF_8', B_462), '#skF_6') | k2_relat_1('#skF_8')=B_462 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_462), '#skF_7'))), inference(resolution, [status(thm)], [c_130, c_3614])).
% 6.73/2.31  tff(c_3623, plain, (![B_462]: (r2_hidden('#skF_3'('#skF_8', B_462), '#skF_6') | k2_relat_1('#skF_8')=B_462 | ~r2_hidden('#skF_4'('#skF_8', B_462), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_3617])).
% 6.73/2.31  tff(c_32, plain, (![A_14, B_36]: (k1_funct_1(A_14, '#skF_3'(A_14, B_36))='#skF_2'(A_14, B_36) | r2_hidden('#skF_4'(A_14, B_36), B_36) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_3268, plain, (![A_423, B_424, D_425]: (k1_funct_1(A_423, '#skF_3'(A_423, B_424))='#skF_2'(A_423, B_424) | k1_funct_1(A_423, D_425)!='#skF_4'(A_423, B_424) | ~r2_hidden(D_425, k1_relat_1(A_423)) | k2_relat_1(A_423)=B_424 | ~v1_funct_1(A_423) | ~v1_relat_1(A_423))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_3274, plain, (![B_424, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_424))='#skF_2'('#skF_8', B_424) | D_71!='#skF_4'('#skF_8', B_424) | ~r2_hidden('#skF_9'(D_71), k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')=B_424 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_71, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_66, c_3268])).
% 6.73/2.31  tff(c_3276, plain, (![B_424, D_71]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_424))='#skF_2'('#skF_8', B_424) | D_71!='#skF_4'('#skF_8', B_424) | ~r2_hidden('#skF_9'(D_71), '#skF_6') | k2_relat_1('#skF_8')=B_424 | ~r2_hidden(D_71, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_2162, c_3274])).
% 6.73/2.31  tff(c_3770, plain, (![B_476]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_476))='#skF_2'('#skF_8', B_476) | ~r2_hidden('#skF_9'('#skF_4'('#skF_8', B_476)), '#skF_6') | k2_relat_1('#skF_8')=B_476 | ~r2_hidden('#skF_4'('#skF_8', B_476), '#skF_7'))), inference(reflexivity, [status(thm), theory('equality')], [c_3276])).
% 6.73/2.31  tff(c_3773, plain, (![B_476]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_476))='#skF_2'('#skF_8', B_476) | k2_relat_1('#skF_8')=B_476 | ~r1_tarski('#skF_6', '#skF_6') | ~r2_hidden('#skF_4'('#skF_8', B_476), '#skF_7'))), inference(resolution, [status(thm)], [c_130, c_3770])).
% 6.73/2.31  tff(c_3781, plain, (![B_477]: (k1_funct_1('#skF_8', '#skF_3'('#skF_8', B_477))='#skF_2'('#skF_8', B_477) | k2_relat_1('#skF_8')=B_477 | ~r2_hidden('#skF_4'('#skF_8', B_477), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_3773])).
% 6.73/2.31  tff(c_3797, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_32, c_3781])).
% 6.73/2.31  tff(c_3813, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_3797])).
% 6.73/2.31  tff(c_3814, plain, (k1_funct_1('#skF_8', '#skF_3'('#skF_8', '#skF_7'))='#skF_2'('#skF_8', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_160, c_3813])).
% 6.73/2.31  tff(c_307, plain, (![A_140, D_141]: (~r1_tarski(k2_relat_1(A_140), k1_funct_1(A_140, D_141)) | ~r2_hidden(D_141, k1_relat_1(A_140)) | ~v1_funct_1(A_140) | ~v1_relat_1(A_140))), inference(resolution, [status(thm)], [c_297, c_36])).
% 6.73/2.31  tff(c_3831, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_2'('#skF_8', '#skF_7')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3814, c_307])).
% 6.73/2.31  tff(c_3847, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_2'('#skF_8', '#skF_7')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_2162, c_3831])).
% 6.73/2.31  tff(c_3852, plain, (~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_3847])).
% 6.73/2.31  tff(c_3875, plain, (k2_relat_1('#skF_8')='#skF_7' | ~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(resolution, [status(thm)], [c_3623, c_3852])).
% 6.73/2.31  tff(c_3894, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_160, c_3875])).
% 6.73/2.31  tff(c_2718, plain, (![A_380, B_381]: (r2_hidden('#skF_3'(A_380, B_381), k1_relat_1(A_380)) | r2_hidden('#skF_4'(A_380, B_381), B_381) | k2_relat_1(A_380)=B_381 | ~v1_funct_1(A_380) | ~v1_relat_1(A_380))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_2743, plain, (![B_381]: (r2_hidden('#skF_3'('#skF_8', B_381), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_381), B_381) | k2_relat_1('#skF_8')=B_381 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2162, c_2718])).
% 6.73/2.31  tff(c_2752, plain, (![B_381]: (r2_hidden('#skF_3'('#skF_8', B_381), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_381), B_381) | k2_relat_1('#skF_8')=B_381)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_2743])).
% 6.73/2.31  tff(c_3887, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_2752, c_3852])).
% 6.73/2.31  tff(c_3907, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_160, c_3887])).
% 6.73/2.31  tff(c_3938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3894, c_3907])).
% 6.73/2.31  tff(c_3940, plain, (r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_3847])).
% 6.73/2.31  tff(c_18, plain, (![A_14, D_53]: (r2_hidden(k1_funct_1(A_14, D_53), k2_relat_1(A_14)) | ~r2_hidden(D_53, k1_relat_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_3834, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3814, c_18])).
% 6.73/2.31  tff(c_3849, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8')) | ~r2_hidden('#skF_3'('#skF_8', '#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_2162, c_3834])).
% 6.73/2.31  tff(c_4030, plain, (r2_hidden('#skF_2'('#skF_8', '#skF_7'), k2_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_3940, c_3849])).
% 6.73/2.31  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.73/2.31  tff(c_4044, plain, (![B_484]: (r2_hidden('#skF_2'('#skF_8', '#skF_7'), B_484) | ~r1_tarski(k2_relat_1('#skF_8'), B_484))), inference(resolution, [status(thm)], [c_4030, c_2])).
% 6.73/2.31  tff(c_30, plain, (![A_14, B_36]: (~r2_hidden('#skF_2'(A_14, B_36), B_36) | r2_hidden('#skF_4'(A_14, B_36), B_36) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_4054, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_4044, c_30])).
% 6.73/2.31  tff(c_4078, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_4054])).
% 6.73/2.31  tff(c_4079, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_160, c_4078])).
% 6.73/2.31  tff(c_4085, plain, (~r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_4079])).
% 6.73/2.31  tff(c_4091, plain, (~v5_relat_1('#skF_8', '#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_14, c_4085])).
% 6.73/2.31  tff(c_4098, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_123, c_4091])).
% 6.73/2.31  tff(c_4100, plain, (r1_tarski(k2_relat_1('#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_4079])).
% 6.73/2.31  tff(c_24, plain, (![A_14, B_36, D_49]: (~r2_hidden('#skF_2'(A_14, B_36), B_36) | k1_funct_1(A_14, D_49)!='#skF_4'(A_14, B_36) | ~r2_hidden(D_49, k1_relat_1(A_14)) | k2_relat_1(A_14)=B_36 | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_4050, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, k1_relat_1('#skF_8')) | k2_relat_1('#skF_8')='#skF_7' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(resolution, [status(thm)], [c_4044, c_24])).
% 6.73/2.31  tff(c_4074, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | k2_relat_1('#skF_8')='#skF_7' | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_2162, c_4050])).
% 6.73/2.31  tff(c_4075, plain, (![D_49]: (k1_funct_1('#skF_8', D_49)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_49, '#skF_6') | ~r1_tarski(k2_relat_1('#skF_8'), '#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_160, c_4074])).
% 6.73/2.31  tff(c_4307, plain, (![D_491]: (k1_funct_1('#skF_8', D_491)!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_491, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4100, c_4075])).
% 6.73/2.31  tff(c_4535, plain, (![D_496]: (k1_funct_1('#skF_8', '#skF_9'(D_496))!='#skF_4'('#skF_8', '#skF_7') | ~r2_hidden(D_496, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_4307])).
% 6.73/2.31  tff(c_4558, plain, (~r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_66, c_4535])).
% 6.73/2.31  tff(c_4099, plain, (r2_hidden('#skF_4'('#skF_8', '#skF_7'), '#skF_7')), inference(splitRight, [status(thm)], [c_4079])).
% 6.73/2.31  tff(c_4560, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4558, c_4099])).
% 6.73/2.31  tff(c_4561, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_2161])).
% 6.73/2.31  tff(c_232, plain, (![B_11, B_122]: (r1_tarski(k2_relat_1(B_11), B_122) | ~v5_relat_1(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_222])).
% 6.73/2.31  tff(c_1756, plain, (![D_277]: (r2_hidden(D_277, k2_relat_1('#skF_8')) | ~r2_hidden(D_277, '#skF_7'))), inference(splitRight, [status(thm)], [c_315])).
% 6.73/2.31  tff(c_1769, plain, (![D_278]: (~r1_tarski(k2_relat_1('#skF_8'), D_278) | ~r2_hidden(D_278, '#skF_7'))), inference(resolution, [status(thm)], [c_1756, c_36])).
% 6.73/2.31  tff(c_1773, plain, (![B_122]: (~r2_hidden(B_122, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_232, c_1769])).
% 6.73/2.31  tff(c_1784, plain, (![B_122]: (~r2_hidden(B_122, '#skF_7') | ~v5_relat_1('#skF_8', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_1773])).
% 6.73/2.31  tff(c_1802, plain, (~v5_relat_1('#skF_8', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1784])).
% 6.73/2.31  tff(c_4577, plain, (~v5_relat_1('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4561, c_1802])).
% 6.73/2.31  tff(c_4590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_4577])).
% 6.73/2.31  tff(c_4592, plain, (v5_relat_1('#skF_8', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1784])).
% 6.73/2.31  tff(c_4605, plain, (![B_124]: (v5_relat_1('#skF_8', B_124) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_4592, c_262])).
% 6.73/2.31  tff(c_4633, plain, (![B_503]: (v5_relat_1('#skF_8', B_503))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_4605])).
% 6.73/2.31  tff(c_107, plain, (![A_90, B_91]: (~r1_tarski(A_90, '#skF_1'(A_90, B_91)) | r1_tarski(A_90, B_91))), inference(resolution, [status(thm)], [c_95, c_36])).
% 6.73/2.31  tff(c_116, plain, (![B_11, B_91]: (r1_tarski(k2_relat_1(B_11), B_91) | ~v5_relat_1(B_11, '#skF_1'(k2_relat_1(B_11), B_91)) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_107])).
% 6.73/2.31  tff(c_4637, plain, (![B_91]: (r1_tarski(k2_relat_1('#skF_8'), B_91) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_4633, c_116])).
% 6.73/2.31  tff(c_4643, plain, (![B_91]: (r1_tarski(k2_relat_1('#skF_8'), B_91))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_4637])).
% 6.73/2.31  tff(c_4827, plain, (![A_522, D_523]: (~r1_tarski(k2_relat_1(A_522), k1_funct_1(A_522, D_523)) | ~r2_hidden(D_523, k1_relat_1(A_522)) | ~v1_funct_1(A_522) | ~v1_relat_1(A_522))), inference(resolution, [status(thm)], [c_297, c_36])).
% 6.73/2.31  tff(c_4835, plain, (![D_523]: (~r2_hidden(D_523, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_4643, c_4827])).
% 6.73/2.31  tff(c_4850, plain, (![D_524]: (~r2_hidden(D_524, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_4835])).
% 6.73/2.31  tff(c_4939, plain, (![A_529, B_530]: (~r1_tarski(A_529, k1_relat_1('#skF_8')) | r1_tarski(A_529, B_530))), inference(resolution, [status(thm)], [c_129, c_4850])).
% 6.73/2.31  tff(c_4973, plain, (![B_530]: (r1_tarski('#skF_6', B_530))), inference(resolution, [status(thm)], [c_1750, c_4939])).
% 6.73/2.31  tff(c_147, plain, (![D_104, B_105]: (r2_hidden('#skF_9'(D_104), B_105) | ~r1_tarski('#skF_6', B_105) | ~r2_hidden(D_104, '#skF_7'))), inference(resolution, [status(thm)], [c_68, c_124])).
% 6.73/2.31  tff(c_165, plain, (![B_109, D_110]: (~r1_tarski(B_109, '#skF_9'(D_110)) | ~r1_tarski('#skF_6', B_109) | ~r2_hidden(D_110, '#skF_7'))), inference(resolution, [status(thm)], [c_147, c_36])).
% 6.73/2.31  tff(c_180, plain, (![D_110]: (~r1_tarski('#skF_6', k1_xboole_0) | ~r2_hidden(D_110, '#skF_7'))), inference(resolution, [status(thm)], [c_8, c_165])).
% 6.73/2.31  tff(c_191, plain, (~r1_tarski('#skF_6', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_180])).
% 6.73/2.31  tff(c_4985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4973, c_191])).
% 6.73/2.31  tff(c_4986, plain, (![D_110]: (~r2_hidden(D_110, '#skF_7'))), inference(splitRight, [status(thm)], [c_180])).
% 6.73/2.31  tff(c_5022, plain, (![A_537, B_538]: (~r1_tarski(A_537, '#skF_7') | r1_tarski(A_537, B_538))), inference(resolution, [status(thm)], [c_5004, c_4986])).
% 6.73/2.31  tff(c_5042, plain, (![B_539, B_540]: (r1_tarski(k2_relat_1(B_539), B_540) | ~v5_relat_1(B_539, '#skF_7') | ~v1_relat_1(B_539))), inference(resolution, [status(thm)], [c_14, c_5022])).
% 6.73/2.31  tff(c_5056, plain, (![B_541, B_542]: (v5_relat_1(B_541, B_542) | ~v5_relat_1(B_541, '#skF_7') | ~v1_relat_1(B_541))), inference(resolution, [status(thm)], [c_5042, c_12])).
% 6.73/2.31  tff(c_5058, plain, (![B_542]: (v5_relat_1('#skF_8', B_542) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_123, c_5056])).
% 6.73/2.31  tff(c_5061, plain, (![B_542]: (v5_relat_1('#skF_8', B_542))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_5058])).
% 6.73/2.31  tff(c_5096, plain, (![A_547, B_548, C_549]: (k1_relset_1(A_547, B_548, C_549)=k1_relat_1(C_549) | ~m1_subset_1(C_549, k1_zfmisc_1(k2_zfmisc_1(A_547, B_548))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.73/2.31  tff(c_5100, plain, (k1_relset_1('#skF_6', '#skF_7', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_5096])).
% 6.73/2.31  tff(c_6192, plain, (![B_655, A_656, C_657]: (k1_xboole_0=B_655 | k1_relset_1(A_656, B_655, C_657)=A_656 | ~v1_funct_2(C_657, A_656, B_655) | ~m1_subset_1(C_657, k1_zfmisc_1(k2_zfmisc_1(A_656, B_655))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.73/2.31  tff(c_6195, plain, (k1_xboole_0='#skF_7' | k1_relset_1('#skF_6', '#skF_7', '#skF_8')='#skF_6' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_60, c_6192])).
% 6.73/2.31  tff(c_6198, plain, (k1_xboole_0='#skF_7' | k1_relat_1('#skF_8')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_5100, c_6195])).
% 6.73/2.31  tff(c_6199, plain, (k1_relat_1('#skF_8')='#skF_6'), inference(splitLeft, [status(thm)], [c_6198])).
% 6.73/2.31  tff(c_5070, plain, (![B_544, A_545, B_546]: (~r1_tarski(B_544, '#skF_1'(A_545, B_546)) | ~r1_tarski(A_545, B_544) | r1_tarski(A_545, B_546))), inference(resolution, [status(thm)], [c_5004, c_36])).
% 6.73/2.31  tff(c_5105, plain, (![A_550, B_551]: (~r1_tarski(A_550, k1_xboole_0) | r1_tarski(A_550, B_551))), inference(resolution, [status(thm)], [c_8, c_5070])).
% 6.73/2.31  tff(c_5127, plain, (![B_11, B_551]: (r1_tarski(k2_relat_1(B_11), B_551) | ~v5_relat_1(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_14, c_5105])).
% 6.73/2.31  tff(c_5474, plain, (![A_581, D_582]: (r2_hidden(k1_funct_1(A_581, D_582), k2_relat_1(A_581)) | ~r2_hidden(D_582, k1_relat_1(A_581)) | ~v1_funct_1(A_581) | ~v1_relat_1(A_581))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_5482, plain, (![A_583, D_584]: (~r1_tarski(k2_relat_1(A_583), k1_funct_1(A_583, D_584)) | ~r2_hidden(D_584, k1_relat_1(A_583)) | ~v1_funct_1(A_583) | ~v1_relat_1(A_583))), inference(resolution, [status(thm)], [c_5474, c_36])).
% 6.73/2.31  tff(c_5507, plain, (![D_584, B_11]: (~r2_hidden(D_584, k1_relat_1(B_11)) | ~v1_funct_1(B_11) | ~v5_relat_1(B_11, k1_xboole_0) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_5127, c_5482])).
% 6.73/2.31  tff(c_6235, plain, (![D_584]: (~r2_hidden(D_584, '#skF_6') | ~v1_funct_1('#skF_8') | ~v5_relat_1('#skF_8', k1_xboole_0) | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6199, c_5507])).
% 6.73/2.31  tff(c_6262, plain, (![D_584]: (~r2_hidden(D_584, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_5061, c_64, c_6235])).
% 6.73/2.31  tff(c_6278, plain, (![A_659, B_660]: (r2_hidden('#skF_3'(A_659, B_660), k1_relat_1(A_659)) | r2_hidden('#skF_4'(A_659, B_660), B_660) | k2_relat_1(A_659)=B_660 | ~v1_funct_1(A_659) | ~v1_relat_1(A_659))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_6330, plain, (![B_660]: (r2_hidden('#skF_3'('#skF_8', B_660), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_660), B_660) | k2_relat_1('#skF_8')=B_660 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6199, c_6278])).
% 6.73/2.31  tff(c_6345, plain, (![B_660]: (r2_hidden('#skF_3'('#skF_8', B_660), '#skF_6') | r2_hidden('#skF_4'('#skF_8', B_660), B_660) | k2_relat_1('#skF_8')=B_660)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_6330])).
% 6.73/2.31  tff(c_6351, plain, (![B_661]: (r2_hidden('#skF_4'('#skF_8', B_661), B_661) | k2_relat_1('#skF_8')=B_661)), inference(negUnitSimplification, [status(thm)], [c_6262, c_6345])).
% 6.73/2.31  tff(c_6387, plain, (k2_relat_1('#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_6351, c_4986])).
% 6.73/2.31  tff(c_6405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_6387])).
% 6.73/2.31  tff(c_6406, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_6198])).
% 6.73/2.31  tff(c_48, plain, (![C_67, A_65]: (k1_xboole_0=C_67 | ~v1_funct_2(C_67, A_65, k1_xboole_0) | k1_xboole_0=A_65 | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 6.73/2.31  tff(c_6430, plain, (![C_663, A_664]: (C_663='#skF_7' | ~v1_funct_2(C_663, A_664, '#skF_7') | A_664='#skF_7' | ~m1_subset_1(C_663, k1_zfmisc_1(k2_zfmisc_1(A_664, '#skF_7'))))), inference(demodulation, [status(thm), theory('equality')], [c_6406, c_6406, c_6406, c_6406, c_48])).
% 6.73/2.31  tff(c_6433, plain, ('#skF_7'='#skF_8' | ~v1_funct_2('#skF_8', '#skF_6', '#skF_7') | '#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_60, c_6430])).
% 6.73/2.31  tff(c_6436, plain, ('#skF_7'='#skF_8' | '#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_6433])).
% 6.73/2.31  tff(c_6437, plain, ('#skF_7'='#skF_6'), inference(splitLeft, [status(thm)], [c_6436])).
% 6.73/2.31  tff(c_6510, plain, (k2_relat_1('#skF_8')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_6437, c_160])).
% 6.73/2.31  tff(c_6438, plain, (![A_665, B_666]: (r2_hidden('#skF_3'(A_665, B_666), k1_relat_1(A_665)) | r2_hidden('#skF_4'(A_665, B_666), B_666) | k2_relat_1(A_665)=B_666 | ~v1_funct_1(A_665) | ~v1_relat_1(A_665))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_5255, plain, (![B_565, B_566]: (r1_tarski(k2_relat_1(B_565), B_566) | ~v5_relat_1(B_565, '#skF_1'(k2_relat_1(B_565), B_566)) | ~v1_relat_1(B_565))), inference(resolution, [status(thm)], [c_14, c_107])).
% 6.73/2.31  tff(c_5259, plain, (![B_566]: (r1_tarski(k2_relat_1('#skF_8'), B_566) | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_5061, c_5255])).
% 6.73/2.31  tff(c_5262, plain, (![B_566]: (r1_tarski(k2_relat_1('#skF_8'), B_566))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_5259])).
% 6.73/2.31  tff(c_5486, plain, (![D_584]: (~r2_hidden(D_584, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_5262, c_5482])).
% 6.73/2.31  tff(c_5505, plain, (![D_584]: (~r2_hidden(D_584, k1_relat_1('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_5486])).
% 6.73/2.31  tff(c_6448, plain, (![B_666]: (r2_hidden('#skF_4'('#skF_8', B_666), B_666) | k2_relat_1('#skF_8')=B_666 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6438, c_5505])).
% 6.73/2.31  tff(c_6621, plain, (![B_670]: (r2_hidden('#skF_4'('#skF_8', B_670), B_670) | k2_relat_1('#skF_8')=B_670)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_6448])).
% 6.73/2.31  tff(c_6509, plain, (![D_110]: (~r2_hidden(D_110, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6437, c_4986])).
% 6.73/2.31  tff(c_6625, plain, (k2_relat_1('#skF_8')='#skF_6'), inference(resolution, [status(thm)], [c_6621, c_6509])).
% 6.73/2.31  tff(c_6650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6510, c_6625])).
% 6.73/2.31  tff(c_6651, plain, ('#skF_7'='#skF_8'), inference(splitRight, [status(thm)], [c_6436])).
% 6.73/2.31  tff(c_6669, plain, (k2_relat_1('#skF_8')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6651, c_160])).
% 6.73/2.31  tff(c_6733, plain, (![A_673, B_674]: (r2_hidden('#skF_3'(A_673, B_674), k1_relat_1(A_673)) | r2_hidden('#skF_4'(A_673, B_674), B_674) | k2_relat_1(A_673)=B_674 | ~v1_funct_1(A_673) | ~v1_relat_1(A_673))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.73/2.31  tff(c_6740, plain, (![B_674]: (r2_hidden('#skF_4'('#skF_8', B_674), B_674) | k2_relat_1('#skF_8')=B_674 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(resolution, [status(thm)], [c_6733, c_5505])).
% 6.73/2.31  tff(c_6855, plain, (![B_679]: (r2_hidden('#skF_4'('#skF_8', B_679), B_679) | k2_relat_1('#skF_8')=B_679)), inference(demodulation, [status(thm), theory('equality')], [c_93, c_64, c_6740])).
% 6.73/2.31  tff(c_6668, plain, (![D_110]: (~r2_hidden(D_110, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_6651, c_4986])).
% 6.73/2.31  tff(c_6859, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(resolution, [status(thm)], [c_6855, c_6668])).
% 6.73/2.31  tff(c_6884, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6669, c_6859])).
% 6.73/2.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.31  
% 6.73/2.31  Inference rules
% 6.73/2.31  ----------------------
% 6.73/2.31  #Ref     : 2
% 6.73/2.31  #Sup     : 1355
% 6.73/2.31  #Fact    : 0
% 6.73/2.31  #Define  : 0
% 6.73/2.31  #Split   : 27
% 6.73/2.31  #Chain   : 0
% 6.73/2.31  #Close   : 0
% 6.73/2.31  
% 6.73/2.31  Ordering : KBO
% 6.73/2.31  
% 6.73/2.31  Simplification rules
% 6.73/2.31  ----------------------
% 6.73/2.31  #Subsume      : 574
% 6.73/2.31  #Demod        : 866
% 6.73/2.31  #Tautology    : 330
% 6.73/2.31  #SimpNegUnit  : 37
% 6.73/2.31  #BackRed      : 177
% 6.73/2.31  
% 6.73/2.31  #Partial instantiations: 0
% 6.73/2.31  #Strategies tried      : 1
% 6.73/2.31  
% 6.73/2.31  Timing (in seconds)
% 6.73/2.31  ----------------------
% 6.73/2.31  Preprocessing        : 0.33
% 6.73/2.31  Parsing              : 0.17
% 6.73/2.31  CNF conversion       : 0.03
% 6.73/2.31  Main loop            : 1.16
% 6.73/2.32  Inferencing          : 0.42
% 6.73/2.32  Reduction            : 0.35
% 6.73/2.32  Demodulation         : 0.23
% 6.73/2.32  BG Simplification    : 0.04
% 6.73/2.32  Subsumption          : 0.26
% 6.73/2.32  Abstraction          : 0.05
% 6.73/2.32  MUC search           : 0.00
% 6.73/2.32  Cooper               : 0.00
% 6.73/2.32  Total                : 1.56
% 6.73/2.32  Index Insertion      : 0.00
% 6.73/2.32  Index Deletion       : 0.00
% 6.73/2.32  Index Matching       : 0.00
% 6.73/2.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
