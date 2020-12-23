%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:24 EST 2020

% Result     : Theorem 3.27s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 257 expanded)
%              Number of leaves         :   39 ( 106 expanded)
%              Depth                    :   11
%              Number of atoms          :  198 ( 692 expanded)
%              Number of equality atoms :   47 ( 149 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_121,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_102,axiom,(
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

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_579,plain,(
    ! [A_200,B_201,C_202,D_203] :
      ( k7_relset_1(A_200,B_201,C_202,D_203) = k9_relat_1(C_202,D_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_589,plain,(
    ! [D_204] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_204) = k9_relat_1('#skF_8',D_204) ),
    inference(resolution,[status(thm)],[c_60,c_579])).

tff(c_38,plain,(
    ! [A_57,B_58,C_59,D_60] :
      ( m1_subset_1(k7_relset_1(A_57,B_58,C_59,D_60),k1_zfmisc_1(B_58))
      | ~ m1_subset_1(C_59,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_595,plain,(
    ! [D_204] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_204),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_38])).

tff(c_607,plain,(
    ! [D_205] : m1_subset_1(k9_relat_1('#skF_8',D_205),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_595])).

tff(c_8,plain,(
    ! [C_9,B_8,A_7] :
      ( ~ v1_xboole_0(C_9)
      | ~ m1_subset_1(B_8,k1_zfmisc_1(C_9))
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_613,plain,(
    ! [A_7,D_205] :
      ( ~ v1_xboole_0('#skF_6')
      | ~ r2_hidden(A_7,k9_relat_1('#skF_8',D_205)) ) ),
    inference(resolution,[status(thm)],[c_607,c_8])).

tff(c_614,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_76,plain,(
    ! [C_81,A_82,B_83] :
      ( v1_relat_1(C_81)
      | ~ m1_subset_1(C_81,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_76])).

tff(c_64,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_12,plain,(
    ! [A_10,B_33,D_48] :
      ( k1_funct_1(A_10,'#skF_4'(A_10,B_33,k9_relat_1(A_10,B_33),D_48)) = D_48
      | ~ r2_hidden(D_48,k9_relat_1(A_10,B_33))
      | ~ v1_funct_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_62,plain,(
    v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_551,plain,(
    ! [A_192,B_193,C_194] :
      ( k1_relset_1(A_192,B_193,C_194) = k1_relat_1(C_194)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_555,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_551])).

tff(c_678,plain,(
    ! [B_234,A_235,C_236] :
      ( k1_xboole_0 = B_234
      | k1_relset_1(A_235,B_234,C_236) = A_235
      | ~ v1_funct_2(C_236,A_235,B_234)
      | ~ m1_subset_1(C_236,k1_zfmisc_1(k2_zfmisc_1(A_235,B_234))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_685,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_678])).

tff(c_689,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_555,c_685])).

tff(c_690,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_689])).

tff(c_809,plain,(
    ! [A_251,B_252,D_253] :
      ( r2_hidden('#skF_4'(A_251,B_252,k9_relat_1(A_251,B_252),D_253),k1_relat_1(A_251))
      | ~ r2_hidden(D_253,k9_relat_1(A_251,B_252))
      | ~ v1_funct_1(A_251)
      | ~ v1_relat_1(A_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_817,plain,(
    ! [B_252,D_253] :
      ( r2_hidden('#skF_4'('#skF_8',B_252,k9_relat_1('#skF_8',B_252),D_253),'#skF_5')
      | ~ r2_hidden(D_253,k9_relat_1('#skF_8',B_252))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_690,c_809])).

tff(c_821,plain,(
    ! [B_252,D_253] :
      ( r2_hidden('#skF_4'('#skF_8',B_252,k9_relat_1('#skF_8',B_252),D_253),'#skF_5')
      | ~ r2_hidden(D_253,k9_relat_1('#skF_8',B_252)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_817])).

tff(c_700,plain,(
    ! [A_237,B_238,D_239] :
      ( r2_hidden('#skF_4'(A_237,B_238,k9_relat_1(A_237,B_238),D_239),B_238)
      | ~ r2_hidden(D_239,k9_relat_1(A_237,B_238))
      | ~ v1_funct_1(A_237)
      | ~ v1_relat_1(A_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    ! [F_75] :
      ( k1_funct_1('#skF_8',F_75) != '#skF_9'
      | ~ r2_hidden(F_75,'#skF_7')
      | ~ r2_hidden(F_75,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_835,plain,(
    ! [A_258,D_259] :
      ( k1_funct_1('#skF_8','#skF_4'(A_258,'#skF_7',k9_relat_1(A_258,'#skF_7'),D_259)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_258,'#skF_7',k9_relat_1(A_258,'#skF_7'),D_259),'#skF_5')
      | ~ r2_hidden(D_259,k9_relat_1(A_258,'#skF_7'))
      | ~ v1_funct_1(A_258)
      | ~ v1_relat_1(A_258) ) ),
    inference(resolution,[status(thm)],[c_700,c_56])).

tff(c_839,plain,(
    ! [D_253] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_253)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_253,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_821,c_835])).

tff(c_847,plain,(
    ! [D_260] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_260)) != '#skF_9'
      | ~ r2_hidden(D_260,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_839])).

tff(c_851,plain,(
    ! [D_48] :
      ( D_48 != '#skF_9'
      | ~ r2_hidden(D_48,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_48,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_847])).

tff(c_854,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_851])).

tff(c_586,plain,(
    ! [D_203] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_203) = k9_relat_1('#skF_8',D_203) ),
    inference(resolution,[status(thm)],[c_60,c_579])).

tff(c_58,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_588,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_586,c_58])).

tff(c_856,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_854,c_588])).

tff(c_857,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_689])).

tff(c_111,plain,(
    ! [A_96,B_97,C_98] :
      ( k1_relset_1(A_96,B_97,C_98) = k1_relat_1(C_98)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_115,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_8') = k1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_60,c_111])).

tff(c_239,plain,(
    ! [B_139,A_140,C_141] :
      ( k1_xboole_0 = B_139
      | k1_relset_1(A_140,B_139,C_141) = A_140
      | ~ v1_funct_2(C_141,A_140,B_139)
      | ~ m1_subset_1(C_141,k1_zfmisc_1(k2_zfmisc_1(A_140,B_139))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_246,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_8') = '#skF_5'
    | ~ v1_funct_2('#skF_8','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_239])).

tff(c_250,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_8') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_115,c_246])).

tff(c_251,plain,(
    k1_relat_1('#skF_8') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_444,plain,(
    ! [A_171,B_172,D_173] :
      ( r2_hidden('#skF_4'(A_171,B_172,k9_relat_1(A_171,B_172),D_173),k1_relat_1(A_171))
      | ~ r2_hidden(D_173,k9_relat_1(A_171,B_172))
      | ~ v1_funct_1(A_171)
      | ~ v1_relat_1(A_171) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_455,plain,(
    ! [B_172,D_173] :
      ( r2_hidden('#skF_4'('#skF_8',B_172,k9_relat_1('#skF_8',B_172),D_173),'#skF_5')
      | ~ r2_hidden(D_173,k9_relat_1('#skF_8',B_172))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_444])).

tff(c_461,plain,(
    ! [B_174,D_175] :
      ( r2_hidden('#skF_4'('#skF_8',B_174,k9_relat_1('#skF_8',B_174),D_175),'#skF_5')
      | ~ r2_hidden(D_175,k9_relat_1('#skF_8',B_174)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_455])).

tff(c_289,plain,(
    ! [A_147,B_148,D_149] :
      ( r2_hidden('#skF_4'(A_147,B_148,k9_relat_1(A_147,B_148),D_149),B_148)
      | ~ r2_hidden(D_149,k9_relat_1(A_147,B_148))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_318,plain,(
    ! [A_147,D_149] :
      ( k1_funct_1('#skF_8','#skF_4'(A_147,'#skF_7',k9_relat_1(A_147,'#skF_7'),D_149)) != '#skF_9'
      | ~ r2_hidden('#skF_4'(A_147,'#skF_7',k9_relat_1(A_147,'#skF_7'),D_149),'#skF_5')
      | ~ r2_hidden(D_149,k9_relat_1(A_147,'#skF_7'))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(resolution,[status(thm)],[c_289,c_56])).

tff(c_465,plain,(
    ! [D_175] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_175)) != '#skF_9'
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(D_175,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_461,c_318])).

tff(c_497,plain,(
    ! [D_181] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_8','#skF_7',k9_relat_1('#skF_8','#skF_7'),D_181)) != '#skF_9'
      | ~ r2_hidden(D_181,k9_relat_1('#skF_8','#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_465])).

tff(c_501,plain,(
    ! [D_48] :
      ( D_48 != '#skF_9'
      | ~ r2_hidden(D_48,k9_relat_1('#skF_8','#skF_7'))
      | ~ r2_hidden(D_48,k9_relat_1('#skF_8','#skF_7'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_497])).

tff(c_504,plain,(
    ~ r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_64,c_501])).

tff(c_140,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k7_relset_1(A_105,B_106,C_107,D_108) = k9_relat_1(C_107,D_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_147,plain,(
    ! [D_108] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_108) = k9_relat_1('#skF_8',D_108) ),
    inference(resolution,[status(thm)],[c_60,c_140])).

tff(c_149,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_58])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_504,c_149])).

tff(c_507,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_71,plain,(
    ! [A_79,B_80] :
      ( r2_hidden(A_79,B_80)
      | v1_xboole_0(B_80)
      | ~ m1_subset_1(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [B_53,A_52] :
      ( ~ r1_tarski(B_53,A_52)
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    ! [B_85,A_86] :
      ( ~ r1_tarski(B_85,A_86)
      | v1_xboole_0(B_85)
      | ~ m1_subset_1(A_86,B_85) ) ),
    inference(resolution,[status(thm)],[c_71,c_34])).

tff(c_91,plain,(
    ! [A_1] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ m1_subset_1(A_1,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_92,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_515,plain,(
    ! [A_1] : ~ m1_subset_1(A_1,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_507,c_92])).

tff(c_150,plain,(
    ! [D_109] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_109) = k9_relat_1('#skF_8',D_109) ),
    inference(resolution,[status(thm)],[c_60,c_140])).

tff(c_156,plain,(
    ! [D_109] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_109),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_38])).

tff(c_168,plain,(
    ! [D_110] : m1_subset_1(k9_relat_1('#skF_8',D_110),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_156])).

tff(c_6,plain,(
    ! [A_4,C_6,B_5] :
      ( m1_subset_1(A_4,C_6)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(C_6))
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_182,plain,(
    ! [A_113,D_114] :
      ( m1_subset_1(A_113,'#skF_6')
      | ~ r2_hidden(A_113,k9_relat_1('#skF_8',D_114)) ) ),
    inference(resolution,[status(thm)],[c_168,c_6])).

tff(c_190,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_149,c_182])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_515,c_190])).

tff(c_532,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_865,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_857,c_532])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_614,c_865])).

tff(c_869,plain,(
    ! [A_7,D_205] : ~ r2_hidden(A_7,k9_relat_1('#skF_8',D_205)) ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_872,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_588])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:41:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.27/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.52  
% 3.27/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.27/1.52  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3
% 3.27/1.52  
% 3.27/1.52  %Foreground sorts:
% 3.27/1.52  
% 3.27/1.52  
% 3.27/1.52  %Background operators:
% 3.27/1.52  
% 3.27/1.52  
% 3.27/1.52  %Foreground operators:
% 3.27/1.52  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.27/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.27/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.27/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.27/1.52  tff('#skF_7', type, '#skF_7': $i).
% 3.27/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.27/1.52  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_5', type, '#skF_5': $i).
% 3.27/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.27/1.52  tff('#skF_6', type, '#skF_6': $i).
% 3.27/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.27/1.52  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_9', type, '#skF_9': $i).
% 3.27/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.27/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.27/1.52  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.27/1.52  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.27/1.52  tff('#skF_8', type, '#skF_8': $i).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.27/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.27/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.27/1.52  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.27/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.27/1.52  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.27/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.27/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.27/1.52  
% 3.34/1.54  tff(f_121, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t115_funct_2)).
% 3.34/1.54  tff(f_84, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.34/1.54  tff(f_76, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 3.34/1.54  tff(f_46, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 3.34/1.54  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.34/1.54  tff(f_63, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: ((C = k9_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((r2_hidden(E, k1_relat_1(A)) & r2_hidden(E, B)) & (D = k1_funct_1(A, E)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 3.34/1.54  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.34/1.54  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 3.34/1.54  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.34/1.54  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.34/1.54  tff(f_68, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.34/1.54  tff(f_39, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 3.34/1.54  tff(c_60, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.34/1.54  tff(c_579, plain, (![A_200, B_201, C_202, D_203]: (k7_relset_1(A_200, B_201, C_202, D_203)=k9_relat_1(C_202, D_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.34/1.54  tff(c_589, plain, (![D_204]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_204)=k9_relat_1('#skF_8', D_204))), inference(resolution, [status(thm)], [c_60, c_579])).
% 3.34/1.54  tff(c_38, plain, (![A_57, B_58, C_59, D_60]: (m1_subset_1(k7_relset_1(A_57, B_58, C_59, D_60), k1_zfmisc_1(B_58)) | ~m1_subset_1(C_59, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.34/1.54  tff(c_595, plain, (![D_204]: (m1_subset_1(k9_relat_1('#skF_8', D_204), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_589, c_38])).
% 3.34/1.54  tff(c_607, plain, (![D_205]: (m1_subset_1(k9_relat_1('#skF_8', D_205), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_595])).
% 3.34/1.54  tff(c_8, plain, (![C_9, B_8, A_7]: (~v1_xboole_0(C_9) | ~m1_subset_1(B_8, k1_zfmisc_1(C_9)) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.34/1.54  tff(c_613, plain, (![A_7, D_205]: (~v1_xboole_0('#skF_6') | ~r2_hidden(A_7, k9_relat_1('#skF_8', D_205)))), inference(resolution, [status(thm)], [c_607, c_8])).
% 3.34/1.54  tff(c_614, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_613])).
% 3.34/1.54  tff(c_76, plain, (![C_81, A_82, B_83]: (v1_relat_1(C_81) | ~m1_subset_1(C_81, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.34/1.54  tff(c_80, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_76])).
% 3.34/1.54  tff(c_64, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.34/1.54  tff(c_12, plain, (![A_10, B_33, D_48]: (k1_funct_1(A_10, '#skF_4'(A_10, B_33, k9_relat_1(A_10, B_33), D_48))=D_48 | ~r2_hidden(D_48, k9_relat_1(A_10, B_33)) | ~v1_funct_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.54  tff(c_62, plain, (v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.34/1.54  tff(c_551, plain, (![A_192, B_193, C_194]: (k1_relset_1(A_192, B_193, C_194)=k1_relat_1(C_194) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.54  tff(c_555, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_551])).
% 3.34/1.54  tff(c_678, plain, (![B_234, A_235, C_236]: (k1_xboole_0=B_234 | k1_relset_1(A_235, B_234, C_236)=A_235 | ~v1_funct_2(C_236, A_235, B_234) | ~m1_subset_1(C_236, k1_zfmisc_1(k2_zfmisc_1(A_235, B_234))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.34/1.54  tff(c_685, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_678])).
% 3.34/1.54  tff(c_689, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_555, c_685])).
% 3.34/1.54  tff(c_690, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_689])).
% 3.34/1.54  tff(c_809, plain, (![A_251, B_252, D_253]: (r2_hidden('#skF_4'(A_251, B_252, k9_relat_1(A_251, B_252), D_253), k1_relat_1(A_251)) | ~r2_hidden(D_253, k9_relat_1(A_251, B_252)) | ~v1_funct_1(A_251) | ~v1_relat_1(A_251))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.54  tff(c_817, plain, (![B_252, D_253]: (r2_hidden('#skF_4'('#skF_8', B_252, k9_relat_1('#skF_8', B_252), D_253), '#skF_5') | ~r2_hidden(D_253, k9_relat_1('#skF_8', B_252)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_690, c_809])).
% 3.34/1.54  tff(c_821, plain, (![B_252, D_253]: (r2_hidden('#skF_4'('#skF_8', B_252, k9_relat_1('#skF_8', B_252), D_253), '#skF_5') | ~r2_hidden(D_253, k9_relat_1('#skF_8', B_252)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_817])).
% 3.34/1.54  tff(c_700, plain, (![A_237, B_238, D_239]: (r2_hidden('#skF_4'(A_237, B_238, k9_relat_1(A_237, B_238), D_239), B_238) | ~r2_hidden(D_239, k9_relat_1(A_237, B_238)) | ~v1_funct_1(A_237) | ~v1_relat_1(A_237))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.54  tff(c_56, plain, (![F_75]: (k1_funct_1('#skF_8', F_75)!='#skF_9' | ~r2_hidden(F_75, '#skF_7') | ~r2_hidden(F_75, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.34/1.54  tff(c_835, plain, (![A_258, D_259]: (k1_funct_1('#skF_8', '#skF_4'(A_258, '#skF_7', k9_relat_1(A_258, '#skF_7'), D_259))!='#skF_9' | ~r2_hidden('#skF_4'(A_258, '#skF_7', k9_relat_1(A_258, '#skF_7'), D_259), '#skF_5') | ~r2_hidden(D_259, k9_relat_1(A_258, '#skF_7')) | ~v1_funct_1(A_258) | ~v1_relat_1(A_258))), inference(resolution, [status(thm)], [c_700, c_56])).
% 3.34/1.54  tff(c_839, plain, (![D_253]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_253))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_253, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_821, c_835])).
% 3.34/1.54  tff(c_847, plain, (![D_260]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_260))!='#skF_9' | ~r2_hidden(D_260, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_839])).
% 3.34/1.54  tff(c_851, plain, (![D_48]: (D_48!='#skF_9' | ~r2_hidden(D_48, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_48, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_847])).
% 3.34/1.54  tff(c_854, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_851])).
% 3.34/1.54  tff(c_586, plain, (![D_203]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_203)=k9_relat_1('#skF_8', D_203))), inference(resolution, [status(thm)], [c_60, c_579])).
% 3.34/1.54  tff(c_58, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.34/1.54  tff(c_588, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_586, c_58])).
% 3.34/1.54  tff(c_856, plain, $false, inference(negUnitSimplification, [status(thm)], [c_854, c_588])).
% 3.34/1.54  tff(c_857, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_689])).
% 3.34/1.54  tff(c_111, plain, (![A_96, B_97, C_98]: (k1_relset_1(A_96, B_97, C_98)=k1_relat_1(C_98) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.34/1.54  tff(c_115, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_8')=k1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_60, c_111])).
% 3.34/1.54  tff(c_239, plain, (![B_139, A_140, C_141]: (k1_xboole_0=B_139 | k1_relset_1(A_140, B_139, C_141)=A_140 | ~v1_funct_2(C_141, A_140, B_139) | ~m1_subset_1(C_141, k1_zfmisc_1(k2_zfmisc_1(A_140, B_139))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.34/1.54  tff(c_246, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_8')='#skF_5' | ~v1_funct_2('#skF_8', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_60, c_239])).
% 3.34/1.54  tff(c_250, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_8')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_115, c_246])).
% 3.34/1.54  tff(c_251, plain, (k1_relat_1('#skF_8')='#skF_5'), inference(splitLeft, [status(thm)], [c_250])).
% 3.34/1.54  tff(c_444, plain, (![A_171, B_172, D_173]: (r2_hidden('#skF_4'(A_171, B_172, k9_relat_1(A_171, B_172), D_173), k1_relat_1(A_171)) | ~r2_hidden(D_173, k9_relat_1(A_171, B_172)) | ~v1_funct_1(A_171) | ~v1_relat_1(A_171))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.54  tff(c_455, plain, (![B_172, D_173]: (r2_hidden('#skF_4'('#skF_8', B_172, k9_relat_1('#skF_8', B_172), D_173), '#skF_5') | ~r2_hidden(D_173, k9_relat_1('#skF_8', B_172)) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_444])).
% 3.34/1.54  tff(c_461, plain, (![B_174, D_175]: (r2_hidden('#skF_4'('#skF_8', B_174, k9_relat_1('#skF_8', B_174), D_175), '#skF_5') | ~r2_hidden(D_175, k9_relat_1('#skF_8', B_174)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_455])).
% 3.34/1.54  tff(c_289, plain, (![A_147, B_148, D_149]: (r2_hidden('#skF_4'(A_147, B_148, k9_relat_1(A_147, B_148), D_149), B_148) | ~r2_hidden(D_149, k9_relat_1(A_147, B_148)) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.34/1.54  tff(c_318, plain, (![A_147, D_149]: (k1_funct_1('#skF_8', '#skF_4'(A_147, '#skF_7', k9_relat_1(A_147, '#skF_7'), D_149))!='#skF_9' | ~r2_hidden('#skF_4'(A_147, '#skF_7', k9_relat_1(A_147, '#skF_7'), D_149), '#skF_5') | ~r2_hidden(D_149, k9_relat_1(A_147, '#skF_7')) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(resolution, [status(thm)], [c_289, c_56])).
% 3.34/1.54  tff(c_465, plain, (![D_175]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_175))!='#skF_9' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(D_175, k9_relat_1('#skF_8', '#skF_7')))), inference(resolution, [status(thm)], [c_461, c_318])).
% 3.34/1.54  tff(c_497, plain, (![D_181]: (k1_funct_1('#skF_8', '#skF_4'('#skF_8', '#skF_7', k9_relat_1('#skF_8', '#skF_7'), D_181))!='#skF_9' | ~r2_hidden(D_181, k9_relat_1('#skF_8', '#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_465])).
% 3.34/1.54  tff(c_501, plain, (![D_48]: (D_48!='#skF_9' | ~r2_hidden(D_48, k9_relat_1('#skF_8', '#skF_7')) | ~r2_hidden(D_48, k9_relat_1('#skF_8', '#skF_7')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_497])).
% 3.34/1.54  tff(c_504, plain, (~r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_64, c_501])).
% 3.34/1.54  tff(c_140, plain, (![A_105, B_106, C_107, D_108]: (k7_relset_1(A_105, B_106, C_107, D_108)=k9_relat_1(C_107, D_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_105, B_106))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.34/1.54  tff(c_147, plain, (![D_108]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_108)=k9_relat_1('#skF_8', D_108))), inference(resolution, [status(thm)], [c_60, c_140])).
% 3.34/1.54  tff(c_149, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_58])).
% 3.34/1.54  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_504, c_149])).
% 3.34/1.54  tff(c_507, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_250])).
% 3.34/1.54  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.54  tff(c_71, plain, (![A_79, B_80]: (r2_hidden(A_79, B_80) | v1_xboole_0(B_80) | ~m1_subset_1(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.54  tff(c_34, plain, (![B_53, A_52]: (~r1_tarski(B_53, A_52) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.34/1.54  tff(c_87, plain, (![B_85, A_86]: (~r1_tarski(B_85, A_86) | v1_xboole_0(B_85) | ~m1_subset_1(A_86, B_85))), inference(resolution, [status(thm)], [c_71, c_34])).
% 3.34/1.54  tff(c_91, plain, (![A_1]: (v1_xboole_0(k1_xboole_0) | ~m1_subset_1(A_1, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_87])).
% 3.34/1.54  tff(c_92, plain, (![A_1]: (~m1_subset_1(A_1, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_91])).
% 3.34/1.54  tff(c_515, plain, (![A_1]: (~m1_subset_1(A_1, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_507, c_92])).
% 3.34/1.54  tff(c_150, plain, (![D_109]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_109)=k9_relat_1('#skF_8', D_109))), inference(resolution, [status(thm)], [c_60, c_140])).
% 3.34/1.54  tff(c_156, plain, (![D_109]: (m1_subset_1(k9_relat_1('#skF_8', D_109), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_150, c_38])).
% 3.34/1.54  tff(c_168, plain, (![D_110]: (m1_subset_1(k9_relat_1('#skF_8', D_110), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_156])).
% 3.34/1.54  tff(c_6, plain, (![A_4, C_6, B_5]: (m1_subset_1(A_4, C_6) | ~m1_subset_1(B_5, k1_zfmisc_1(C_6)) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.34/1.54  tff(c_182, plain, (![A_113, D_114]: (m1_subset_1(A_113, '#skF_6') | ~r2_hidden(A_113, k9_relat_1('#skF_8', D_114)))), inference(resolution, [status(thm)], [c_168, c_6])).
% 3.34/1.54  tff(c_190, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_149, c_182])).
% 3.34/1.54  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_515, c_190])).
% 3.34/1.54  tff(c_532, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_91])).
% 3.34/1.54  tff(c_865, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_857, c_532])).
% 3.34/1.54  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_614, c_865])).
% 3.34/1.54  tff(c_869, plain, (![A_7, D_205]: (~r2_hidden(A_7, k9_relat_1('#skF_8', D_205)))), inference(splitRight, [status(thm)], [c_613])).
% 3.34/1.54  tff(c_872, plain, $false, inference(negUnitSimplification, [status(thm)], [c_869, c_588])).
% 3.34/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.54  
% 3.34/1.54  Inference rules
% 3.34/1.54  ----------------------
% 3.34/1.54  #Ref     : 0
% 3.34/1.54  #Sup     : 162
% 3.34/1.54  #Fact    : 0
% 3.34/1.54  #Define  : 0
% 3.34/1.54  #Split   : 23
% 3.34/1.54  #Chain   : 0
% 3.34/1.54  #Close   : 0
% 3.34/1.54  
% 3.34/1.54  Ordering : KBO
% 3.34/1.54  
% 3.34/1.54  Simplification rules
% 3.34/1.54  ----------------------
% 3.34/1.54  #Subsume      : 15
% 3.34/1.54  #Demod        : 89
% 3.34/1.54  #Tautology    : 24
% 3.34/1.54  #SimpNegUnit  : 14
% 3.34/1.54  #BackRed      : 28
% 3.34/1.54  
% 3.34/1.54  #Partial instantiations: 0
% 3.34/1.54  #Strategies tried      : 1
% 3.34/1.54  
% 3.34/1.54  Timing (in seconds)
% 3.34/1.54  ----------------------
% 3.34/1.54  Preprocessing        : 0.33
% 3.34/1.54  Parsing              : 0.16
% 3.34/1.54  CNF conversion       : 0.03
% 3.34/1.54  Main loop            : 0.40
% 3.34/1.54  Inferencing          : 0.15
% 3.34/1.54  Reduction            : 0.12
% 3.34/1.54  Demodulation         : 0.08
% 3.34/1.54  BG Simplification    : 0.03
% 3.34/1.54  Subsumption          : 0.08
% 3.34/1.54  Abstraction          : 0.02
% 3.34/1.54  MUC search           : 0.00
% 3.34/1.54  Cooper               : 0.00
% 3.34/1.54  Total                : 0.77
% 3.34/1.54  Index Insertion      : 0.00
% 3.34/1.54  Index Deletion       : 0.00
% 3.34/1.54  Index Matching       : 0.00
% 3.34/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
