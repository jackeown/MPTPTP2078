%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:58 EST 2020

% Result     : Theorem 5.11s
% Output     : CNFRefutation 5.11s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 183 expanded)
%              Number of leaves         :   47 (  83 expanded)
%              Depth                    :   12
%              Number of atoms          :  157 ( 411 expanded)
%              Number of equality atoms :   33 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_146,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,B,C)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
       => ~ ( r2_hidden(A,k2_relset_1(B,C,D))
            & ! [E] :
                ( m1_subset_1(E,B)
               => A != k1_funct_1(D,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t190_funct_2)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_130,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_80,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_535,plain,(
    ! [A_169,B_170,C_171,D_172] :
      ( k7_relset_1(A_169,B_170,C_171,D_172) = k9_relat_1(C_171,D_172)
      | ~ m1_subset_1(C_171,k1_zfmisc_1(k2_zfmisc_1(A_169,B_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_550,plain,(
    ! [D_172] : k7_relset_1('#skF_7','#skF_8','#skF_9',D_172) = k9_relat_1('#skF_9',D_172) ),
    inference(resolution,[status(thm)],[c_80,c_535])).

tff(c_631,plain,(
    ! [A_178,B_179,C_180] :
      ( k7_relset_1(A_178,B_179,C_180,A_178) = k2_relset_1(A_178,B_179,C_180)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_642,plain,(
    k7_relset_1('#skF_7','#skF_8','#skF_9','#skF_7') = k2_relset_1('#skF_7','#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_631])).

tff(c_647,plain,(
    k2_relset_1('#skF_7','#skF_8','#skF_9') = k9_relat_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_642])).

tff(c_78,plain,(
    r2_hidden('#skF_6',k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ~ v1_xboole_0(k2_relset_1('#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_78,c_2])).

tff(c_650,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_90])).

tff(c_54,plain,(
    ! [A_68,B_69,C_70] :
      ( m1_subset_1(k2_relset_1(A_68,B_69,C_70),k1_zfmisc_1(B_69))
      | ~ m1_subset_1(C_70,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_655,plain,
    ( m1_subset_1(k9_relat_1('#skF_9','#skF_7'),k1_zfmisc_1('#skF_8'))
    | ~ m1_subset_1('#skF_9',k1_zfmisc_1(k2_zfmisc_1('#skF_7','#skF_8'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_647,c_54])).

tff(c_659,plain,(
    m1_subset_1(k9_relat_1('#skF_9','#skF_7'),k1_zfmisc_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_655])).

tff(c_8,plain,(
    ! [B_8,A_6] :
      ( v1_xboole_0(B_8)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_676,plain,
    ( v1_xboole_0(k9_relat_1('#skF_9','#skF_7'))
    | ~ v1_xboole_0('#skF_8') ),
    inference(resolution,[status(thm)],[c_659,c_8])).

tff(c_683,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_650,c_676])).

tff(c_151,plain,(
    ! [C_104,A_105,B_106] :
      ( v1_relat_1(C_104)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_160,plain,(
    v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_151])).

tff(c_84,plain,(
    v1_funct_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_24,plain,(
    ! [A_18,B_41,D_56] :
      ( k1_funct_1(A_18,'#skF_5'(A_18,B_41,k9_relat_1(A_18,B_41),D_56)) = D_56
      | ~ r2_hidden(D_56,k9_relat_1(A_18,B_41))
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_234,plain,(
    ! [C_123,A_124,B_125] :
      ( v4_relat_1(C_123,A_124)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_243,plain,(
    v4_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_80,c_234])).

tff(c_82,plain,(
    v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_268,plain,(
    ! [A_133,B_134,C_135] :
      ( k1_relset_1(A_133,B_134,C_135) = k1_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_277,plain,(
    k1_relset_1('#skF_7','#skF_8','#skF_9') = k1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_80,c_268])).

tff(c_834,plain,(
    ! [B_192,A_193,C_194] :
      ( k1_xboole_0 = B_192
      | k1_relset_1(A_193,B_192,C_194) = A_193
      | ~ v1_funct_2(C_194,A_193,B_192)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_193,B_192))) ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_849,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relset_1('#skF_7','#skF_8','#skF_9') = '#skF_7'
    | ~ v1_funct_2('#skF_9','#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_80,c_834])).

tff(c_855,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_relat_1('#skF_9') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_277,c_849])).

tff(c_856,plain,(
    k1_relat_1('#skF_9') = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_855])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_865,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_7',A_16)
      | ~ v4_relat_1('#skF_9',A_16)
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_20])).

tff(c_942,plain,(
    ! [A_200] :
      ( r1_tarski('#skF_7',A_200)
      | ~ v4_relat_1('#skF_9',A_200) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_865])).

tff(c_950,plain,(
    r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_243,c_942])).

tff(c_1185,plain,(
    ! [A_230,B_231,D_232] :
      ( r2_hidden('#skF_5'(A_230,B_231,k9_relat_1(A_230,B_231),D_232),k1_relat_1(A_230))
      | ~ r2_hidden(D_232,k9_relat_1(A_230,B_231))
      | ~ v1_funct_1(A_230)
      | ~ v1_relat_1(A_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1196,plain,(
    ! [B_231,D_232] :
      ( r2_hidden('#skF_5'('#skF_9',B_231,k9_relat_1('#skF_9',B_231),D_232),'#skF_7')
      | ~ r2_hidden(D_232,k9_relat_1('#skF_9',B_231))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_1185])).

tff(c_1236,plain,(
    ! [B_238,D_239] :
      ( r2_hidden('#skF_5'('#skF_9',B_238,k9_relat_1('#skF_9',B_238),D_239),'#skF_7')
      | ~ r2_hidden(D_239,k9_relat_1('#skF_9',B_238)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_84,c_1196])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_244,plain,(
    ! [A_126,C_127,B_128] :
      ( m1_subset_1(A_126,C_127)
      | ~ m1_subset_1(B_128,k1_zfmisc_1(C_127))
      | ~ r2_hidden(A_126,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_249,plain,(
    ! [A_126,B_12,A_11] :
      ( m1_subset_1(A_126,B_12)
      | ~ r2_hidden(A_126,A_11)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_244])).

tff(c_2118,plain,(
    ! [B_331,D_332,B_333] :
      ( m1_subset_1('#skF_5'('#skF_9',B_331,k9_relat_1('#skF_9',B_331),D_332),B_333)
      | ~ r1_tarski('#skF_7',B_333)
      | ~ r2_hidden(D_332,k9_relat_1('#skF_9',B_331)) ) ),
    inference(resolution,[status(thm)],[c_1236,c_249])).

tff(c_76,plain,(
    ! [E_85] :
      ( k1_funct_1('#skF_9',E_85) != '#skF_6'
      | ~ m1_subset_1(E_85,'#skF_7') ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_2193,plain,(
    ! [B_331,D_332] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_331,k9_relat_1('#skF_9',B_331),D_332)) != '#skF_6'
      | ~ r1_tarski('#skF_7','#skF_7')
      | ~ r2_hidden(D_332,k9_relat_1('#skF_9',B_331)) ) ),
    inference(resolution,[status(thm)],[c_2118,c_76])).

tff(c_2411,plain,(
    ! [B_351,D_352] :
      ( k1_funct_1('#skF_9','#skF_5'('#skF_9',B_351,k9_relat_1('#skF_9',B_351),D_352)) != '#skF_6'
      | ~ r2_hidden(D_352,k9_relat_1('#skF_9',B_351)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_2193])).

tff(c_2415,plain,(
    ! [D_56,B_41] :
      ( D_56 != '#skF_6'
      | ~ r2_hidden(D_56,k9_relat_1('#skF_9',B_41))
      | ~ r2_hidden(D_56,k9_relat_1('#skF_9',B_41))
      | ~ v1_funct_1('#skF_9')
      | ~ v1_relat_1('#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_2411])).

tff(c_2462,plain,(
    ! [B_41] : ~ r2_hidden('#skF_6',k9_relat_1('#skF_9',B_41)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_84,c_2415])).

tff(c_651,plain,(
    r2_hidden('#skF_6',k9_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_78])).

tff(c_2464,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2462,c_651])).

tff(c_2465,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_855])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [B_90,A_91] :
      ( ~ r1_tarski(B_90,A_91)
      | ~ r2_hidden(A_91,B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_106,plain,(
    ! [A_93] :
      ( ~ r1_tarski(A_93,'#skF_1'(A_93))
      | v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_4,c_96])).

tff(c_111,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_2496,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2465,c_111])).

tff(c_2499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_683,c_2496])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:54:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.11/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/2.02  
% 5.11/2.02  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/2.02  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_5 > #skF_3
% 5.11/2.02  
% 5.11/2.02  %Foreground sorts:
% 5.11/2.02  
% 5.11/2.02  
% 5.11/2.02  %Background operators:
% 5.11/2.02  
% 5.11/2.02  
% 5.11/2.02  %Foreground operators:
% 5.11/2.02  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.11/2.02  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.11/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.11/2.02  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.11/2.02  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 5.11/2.02  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.11/2.02  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.11/2.02  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.11/2.02  tff('#skF_7', type, '#skF_7': $i).
% 5.11/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.11/2.02  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 5.11/2.02  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.11/2.02  tff('#skF_6', type, '#skF_6': $i).
% 5.11/2.02  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.11/2.02  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.11/2.02  tff('#skF_9', type, '#skF_9': $i).
% 5.11/2.02  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.11/2.02  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.11/2.02  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.11/2.02  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.11/2.02  tff('#skF_8', type, '#skF_8': $i).
% 5.11/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.11/2.02  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 5.11/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.11/2.02  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.11/2.02  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 5.11/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.11/2.02  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.11/2.02  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.11/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.11/2.02  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.11/2.02  
% 5.11/2.04  tff(f_146, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ~(r2_hidden(A, k2_relset_1(B, C, D)) & (![E]: (m1_subset_1(E, B) => ~(A = k1_funct_1(D, E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t190_funct_2)).
% 5.11/2.04  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 5.11/2.04  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_relset_1)).
% 5.11/2.04  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.11/2.04  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.11/2.04  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 5.11/2.04  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.11/2.04  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_funct_1)).
% 5.11/2.04  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.11/2.04  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.11/2.04  tff(f_130, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.11/2.04  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 5.11/2.04  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.11/2.04  tff(f_56, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.11/2.04  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.11/2.04  tff(f_84, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.11/2.04  tff(c_80, plain, (m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.11/2.04  tff(c_535, plain, (![A_169, B_170, C_171, D_172]: (k7_relset_1(A_169, B_170, C_171, D_172)=k9_relat_1(C_171, D_172) | ~m1_subset_1(C_171, k1_zfmisc_1(k2_zfmisc_1(A_169, B_170))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.11/2.04  tff(c_550, plain, (![D_172]: (k7_relset_1('#skF_7', '#skF_8', '#skF_9', D_172)=k9_relat_1('#skF_9', D_172))), inference(resolution, [status(thm)], [c_80, c_535])).
% 5.11/2.04  tff(c_631, plain, (![A_178, B_179, C_180]: (k7_relset_1(A_178, B_179, C_180, A_178)=k2_relset_1(A_178, B_179, C_180) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.11/2.04  tff(c_642, plain, (k7_relset_1('#skF_7', '#skF_8', '#skF_9', '#skF_7')=k2_relset_1('#skF_7', '#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_80, c_631])).
% 5.11/2.04  tff(c_647, plain, (k2_relset_1('#skF_7', '#skF_8', '#skF_9')=k9_relat_1('#skF_9', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_550, c_642])).
% 5.11/2.04  tff(c_78, plain, (r2_hidden('#skF_6', k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.11/2.04  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.11/2.04  tff(c_90, plain, (~v1_xboole_0(k2_relset_1('#skF_7', '#skF_8', '#skF_9'))), inference(resolution, [status(thm)], [c_78, c_2])).
% 5.11/2.04  tff(c_650, plain, (~v1_xboole_0(k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_90])).
% 5.11/2.04  tff(c_54, plain, (![A_68, B_69, C_70]: (m1_subset_1(k2_relset_1(A_68, B_69, C_70), k1_zfmisc_1(B_69)) | ~m1_subset_1(C_70, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.11/2.04  tff(c_655, plain, (m1_subset_1(k9_relat_1('#skF_9', '#skF_7'), k1_zfmisc_1('#skF_8')) | ~m1_subset_1('#skF_9', k1_zfmisc_1(k2_zfmisc_1('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_647, c_54])).
% 5.11/2.04  tff(c_659, plain, (m1_subset_1(k9_relat_1('#skF_9', '#skF_7'), k1_zfmisc_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_655])).
% 5.11/2.04  tff(c_8, plain, (![B_8, A_6]: (v1_xboole_0(B_8) | ~m1_subset_1(B_8, k1_zfmisc_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.11/2.04  tff(c_676, plain, (v1_xboole_0(k9_relat_1('#skF_9', '#skF_7')) | ~v1_xboole_0('#skF_8')), inference(resolution, [status(thm)], [c_659, c_8])).
% 5.11/2.04  tff(c_683, plain, (~v1_xboole_0('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_650, c_676])).
% 5.11/2.04  tff(c_151, plain, (![C_104, A_105, B_106]: (v1_relat_1(C_104) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.11/2.04  tff(c_160, plain, (v1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_151])).
% 5.11/2.04  tff(c_84, plain, (v1_funct_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.11/2.04  tff(c_24, plain, (![A_18, B_41, D_56]: (k1_funct_1(A_18, '#skF_5'(A_18, B_41, k9_relat_1(A_18, B_41), D_56))=D_56 | ~r2_hidden(D_56, k9_relat_1(A_18, B_41)) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.11/2.04  tff(c_234, plain, (![C_123, A_124, B_125]: (v4_relat_1(C_123, A_124) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.11/2.04  tff(c_243, plain, (v4_relat_1('#skF_9', '#skF_7')), inference(resolution, [status(thm)], [c_80, c_234])).
% 5.11/2.04  tff(c_82, plain, (v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.11/2.04  tff(c_268, plain, (![A_133, B_134, C_135]: (k1_relset_1(A_133, B_134, C_135)=k1_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 5.11/2.04  tff(c_277, plain, (k1_relset_1('#skF_7', '#skF_8', '#skF_9')=k1_relat_1('#skF_9')), inference(resolution, [status(thm)], [c_80, c_268])).
% 5.11/2.04  tff(c_834, plain, (![B_192, A_193, C_194]: (k1_xboole_0=B_192 | k1_relset_1(A_193, B_192, C_194)=A_193 | ~v1_funct_2(C_194, A_193, B_192) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_193, B_192))))), inference(cnfTransformation, [status(thm)], [f_130])).
% 5.11/2.04  tff(c_849, plain, (k1_xboole_0='#skF_8' | k1_relset_1('#skF_7', '#skF_8', '#skF_9')='#skF_7' | ~v1_funct_2('#skF_9', '#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_80, c_834])).
% 5.11/2.04  tff(c_855, plain, (k1_xboole_0='#skF_8' | k1_relat_1('#skF_9')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_82, c_277, c_849])).
% 5.11/2.04  tff(c_856, plain, (k1_relat_1('#skF_9')='#skF_7'), inference(splitLeft, [status(thm)], [c_855])).
% 5.11/2.04  tff(c_20, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.11/2.04  tff(c_865, plain, (![A_16]: (r1_tarski('#skF_7', A_16) | ~v4_relat_1('#skF_9', A_16) | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_856, c_20])).
% 5.11/2.04  tff(c_942, plain, (![A_200]: (r1_tarski('#skF_7', A_200) | ~v4_relat_1('#skF_9', A_200))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_865])).
% 5.11/2.04  tff(c_950, plain, (r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_243, c_942])).
% 5.11/2.04  tff(c_1185, plain, (![A_230, B_231, D_232]: (r2_hidden('#skF_5'(A_230, B_231, k9_relat_1(A_230, B_231), D_232), k1_relat_1(A_230)) | ~r2_hidden(D_232, k9_relat_1(A_230, B_231)) | ~v1_funct_1(A_230) | ~v1_relat_1(A_230))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.11/2.04  tff(c_1196, plain, (![B_231, D_232]: (r2_hidden('#skF_5'('#skF_9', B_231, k9_relat_1('#skF_9', B_231), D_232), '#skF_7') | ~r2_hidden(D_232, k9_relat_1('#skF_9', B_231)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_856, c_1185])).
% 5.11/2.04  tff(c_1236, plain, (![B_238, D_239]: (r2_hidden('#skF_5'('#skF_9', B_238, k9_relat_1('#skF_9', B_238), D_239), '#skF_7') | ~r2_hidden(D_239, k9_relat_1('#skF_9', B_238)))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_84, c_1196])).
% 5.11/2.04  tff(c_14, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.11/2.04  tff(c_244, plain, (![A_126, C_127, B_128]: (m1_subset_1(A_126, C_127) | ~m1_subset_1(B_128, k1_zfmisc_1(C_127)) | ~r2_hidden(A_126, B_128))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.11/2.04  tff(c_249, plain, (![A_126, B_12, A_11]: (m1_subset_1(A_126, B_12) | ~r2_hidden(A_126, A_11) | ~r1_tarski(A_11, B_12))), inference(resolution, [status(thm)], [c_14, c_244])).
% 5.11/2.04  tff(c_2118, plain, (![B_331, D_332, B_333]: (m1_subset_1('#skF_5'('#skF_9', B_331, k9_relat_1('#skF_9', B_331), D_332), B_333) | ~r1_tarski('#skF_7', B_333) | ~r2_hidden(D_332, k9_relat_1('#skF_9', B_331)))), inference(resolution, [status(thm)], [c_1236, c_249])).
% 5.11/2.04  tff(c_76, plain, (![E_85]: (k1_funct_1('#skF_9', E_85)!='#skF_6' | ~m1_subset_1(E_85, '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 5.11/2.04  tff(c_2193, plain, (![B_331, D_332]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_331, k9_relat_1('#skF_9', B_331), D_332))!='#skF_6' | ~r1_tarski('#skF_7', '#skF_7') | ~r2_hidden(D_332, k9_relat_1('#skF_9', B_331)))), inference(resolution, [status(thm)], [c_2118, c_76])).
% 5.11/2.04  tff(c_2411, plain, (![B_351, D_352]: (k1_funct_1('#skF_9', '#skF_5'('#skF_9', B_351, k9_relat_1('#skF_9', B_351), D_352))!='#skF_6' | ~r2_hidden(D_352, k9_relat_1('#skF_9', B_351)))), inference(demodulation, [status(thm), theory('equality')], [c_950, c_2193])).
% 5.11/2.04  tff(c_2415, plain, (![D_56, B_41]: (D_56!='#skF_6' | ~r2_hidden(D_56, k9_relat_1('#skF_9', B_41)) | ~r2_hidden(D_56, k9_relat_1('#skF_9', B_41)) | ~v1_funct_1('#skF_9') | ~v1_relat_1('#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_2411])).
% 5.11/2.04  tff(c_2462, plain, (![B_41]: (~r2_hidden('#skF_6', k9_relat_1('#skF_9', B_41)))), inference(demodulation, [status(thm), theory('equality')], [c_160, c_84, c_2415])).
% 5.11/2.04  tff(c_651, plain, (r2_hidden('#skF_6', k9_relat_1('#skF_9', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_78])).
% 5.11/2.04  tff(c_2464, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2462, c_651])).
% 5.11/2.04  tff(c_2465, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_855])).
% 5.11/2.04  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.11/2.04  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.11/2.04  tff(c_96, plain, (![B_90, A_91]: (~r1_tarski(B_90, A_91) | ~r2_hidden(A_91, B_90))), inference(cnfTransformation, [status(thm)], [f_84])).
% 5.11/2.04  tff(c_106, plain, (![A_93]: (~r1_tarski(A_93, '#skF_1'(A_93)) | v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_4, c_96])).
% 5.11/2.04  tff(c_111, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_106])).
% 5.11/2.04  tff(c_2496, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2465, c_111])).
% 5.11/2.04  tff(c_2499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_683, c_2496])).
% 5.11/2.04  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.11/2.04  
% 5.11/2.04  Inference rules
% 5.11/2.04  ----------------------
% 5.11/2.04  #Ref     : 0
% 5.11/2.04  #Sup     : 464
% 5.11/2.04  #Fact    : 0
% 5.11/2.04  #Define  : 0
% 5.11/2.04  #Split   : 8
% 5.11/2.04  #Chain   : 0
% 5.11/2.04  #Close   : 0
% 5.11/2.04  
% 5.11/2.04  Ordering : KBO
% 5.11/2.04  
% 5.11/2.04  Simplification rules
% 5.11/2.04  ----------------------
% 5.11/2.04  #Subsume      : 36
% 5.11/2.04  #Demod        : 211
% 5.11/2.04  #Tautology    : 64
% 5.11/2.04  #SimpNegUnit  : 20
% 5.11/2.04  #BackRed      : 39
% 5.11/2.04  
% 5.11/2.04  #Partial instantiations: 0
% 5.11/2.04  #Strategies tried      : 1
% 5.11/2.04  
% 5.11/2.04  Timing (in seconds)
% 5.11/2.04  ----------------------
% 5.11/2.04  Preprocessing        : 0.38
% 5.11/2.04  Parsing              : 0.18
% 5.11/2.04  CNF conversion       : 0.03
% 5.11/2.04  Main loop            : 0.83
% 5.11/2.04  Inferencing          : 0.29
% 5.11/2.04  Reduction            : 0.27
% 5.11/2.04  Demodulation         : 0.18
% 5.11/2.04  BG Simplification    : 0.04
% 5.11/2.04  Subsumption          : 0.16
% 5.11/2.04  Abstraction          : 0.04
% 5.11/2.04  MUC search           : 0.00
% 5.11/2.04  Cooper               : 0.00
% 5.11/2.04  Total                : 1.25
% 5.11/2.04  Index Insertion      : 0.00
% 5.11/2.04  Index Deletion       : 0.00
% 5.11/2.04  Index Matching       : 0.00
% 5.11/2.04  BG Taut test         : 0.00
%------------------------------------------------------------------------------
