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
% DateTime   : Thu Dec  3 10:16:30 EST 2020

% Result     : Theorem 7.21s
% Output     : CNFRefutation 7.49s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 507 expanded)
%              Number of leaves         :   37 ( 186 expanded)
%              Depth                    :   13
%              Number of atoms          :  268 (1359 expanded)
%              Number of equality atoms :   21 ( 173 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_138,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_93,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_119,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ~ v1_xboole_0(B)
         => ! [C] :
              ( ~ v1_xboole_0(C)
             => ! [D] :
                  ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
                 => ! [E] :
                      ( m1_subset_1(E,A)
                     => ( r2_hidden(E,k7_relset_1(C,A,D,B))
                      <=> ? [F] :
                            ( m1_subset_1(F,C)
                            & r2_hidden(k4_tarski(F,E),D)
                            & r2_hidden(F,B) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_40,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ? [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
          & ~ v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_4338,plain,(
    ! [C_660,A_661,B_662] :
      ( v1_relat_1(C_660)
      | ~ m1_subset_1(C_660,k1_zfmisc_1(k2_zfmisc_1(A_661,B_662))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4347,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_4338])).

tff(c_52,plain,(
    v1_funct_1('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_81,plain,(
    ! [C_144,A_145,B_146] :
      ( v1_relat_1(C_144)
      | ~ m1_subset_1(C_144,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_90,plain,(
    v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_48,c_81])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden('#skF_3'(A_159,B_160,C_161),B_160)
      | ~ r2_hidden(A_159,k9_relat_1(C_161,B_160))
      | ~ v1_relat_1(C_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_153,plain,(
    ! [B_162,A_163,C_164] :
      ( ~ v1_xboole_0(B_162)
      | ~ r2_hidden(A_163,k9_relat_1(C_164,B_162))
      | ~ v1_relat_1(C_164) ) ),
    inference(resolution,[status(thm)],[c_138,c_2])).

tff(c_163,plain,(
    ! [B_162,C_164] :
      ( ~ v1_xboole_0(B_162)
      | ~ v1_relat_1(C_164)
      | v1_xboole_0(k9_relat_1(C_164,B_162)) ) ),
    inference(resolution,[status(thm)],[c_4,c_153])).

tff(c_236,plain,(
    ! [A_199,B_200,C_201,D_202] :
      ( k7_relset_1(A_199,B_200,C_201,D_202) = k9_relat_1(C_201,D_202)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_251,plain,(
    ! [D_202] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_202) = k9_relat_1('#skF_8',D_202) ),
    inference(resolution,[status(thm)],[c_48,c_236])).

tff(c_46,plain,(
    r2_hidden('#skF_9',k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_64,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_5','#skF_6','#skF_8','#skF_7')) ),
    inference(resolution,[status(thm)],[c_46,c_2])).

tff(c_252,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_64])).

tff(c_273,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_163,c_252])).

tff(c_279,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_273])).

tff(c_253,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_46])).

tff(c_254,plain,(
    ! [D_203] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_203) = k9_relat_1('#skF_8',D_203) ),
    inference(resolution,[status(thm)],[c_48,c_236])).

tff(c_32,plain,(
    ! [A_29,B_30,C_31,D_32] :
      ( m1_subset_1(k7_relset_1(A_29,B_30,C_31,D_32),k1_zfmisc_1(B_30))
      | ~ m1_subset_1(C_31,k1_zfmisc_1(k2_zfmisc_1(A_29,B_30))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_260,plain,(
    ! [D_203] :
      ( m1_subset_1(k9_relat_1('#skF_8',D_203),k1_zfmisc_1('#skF_6'))
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_32])).

tff(c_345,plain,(
    ! [D_207] : m1_subset_1(k9_relat_1('#skF_8',D_207),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_260])).

tff(c_12,plain,(
    ! [A_10,C_12,B_11] :
      ( m1_subset_1(A_10,C_12)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(C_12))
      | ~ r2_hidden(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_355,plain,(
    ! [A_208,D_209] :
      ( m1_subset_1(A_208,'#skF_6')
      | ~ r2_hidden(A_208,k9_relat_1('#skF_8',D_209)) ) ),
    inference(resolution,[status(thm)],[c_345,c_12])).

tff(c_371,plain,(
    m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_253,c_355])).

tff(c_10,plain,(
    ! [B_9,A_7] :
      ( v1_xboole_0(B_9)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_352,plain,(
    ! [D_207] :
      ( v1_xboole_0(k9_relat_1('#skF_8',D_207))
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_345,c_10])).

tff(c_353,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_91,plain,(
    ! [C_147,A_148,B_149] :
      ( v1_xboole_0(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149)))
      | ~ v1_xboole_0(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_100,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_48,c_91])).

tff(c_101,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_651,plain,(
    ! [D_256,C_253,B_255,A_254,E_257] :
      ( r2_hidden('#skF_4'(C_253,A_254,B_255,D_256,E_257),B_255)
      | ~ r2_hidden(E_257,k7_relset_1(C_253,A_254,D_256,B_255))
      | ~ m1_subset_1(E_257,A_254)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(C_253,A_254)))
      | v1_xboole_0(C_253)
      | v1_xboole_0(B_255)
      | v1_xboole_0(A_254) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_662,plain,(
    ! [B_255,E_257] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6',B_255,'#skF_8',E_257),B_255)
      | ~ r2_hidden(E_257,k7_relset_1('#skF_5','#skF_6','#skF_8',B_255))
      | ~ m1_subset_1(E_257,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_255)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_48,c_651])).

tff(c_667,plain,(
    ! [B_255,E_257] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6',B_255,'#skF_8',E_257),B_255)
      | ~ r2_hidden(E_257,k9_relat_1('#skF_8',B_255))
      | ~ m1_subset_1(E_257,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(B_255)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_662])).

tff(c_1307,plain,(
    ! [B_373,E_374] :
      ( r2_hidden('#skF_4'('#skF_5','#skF_6',B_373,'#skF_8',E_374),B_373)
      | ~ r2_hidden(E_374,k9_relat_1('#skF_8',B_373))
      | ~ m1_subset_1(E_374,'#skF_6')
      | v1_xboole_0(B_373) ) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_101,c_667])).

tff(c_44,plain,(
    ! [F_135] :
      ( k1_funct_1('#skF_8',F_135) != '#skF_9'
      | ~ r2_hidden(F_135,'#skF_7')
      | ~ m1_subset_1(F_135,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_1407,plain,(
    ! [E_374] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8',E_374)) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8',E_374),'#skF_5')
      | ~ r2_hidden(E_374,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_374,'#skF_6')
      | v1_xboole_0('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1307,c_44])).

tff(c_1525,plain,(
    ! [E_386] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8',E_386)) != '#skF_9'
      | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8',E_386),'#skF_5')
      | ~ r2_hidden(E_386,k9_relat_1('#skF_8','#skF_7'))
      | ~ m1_subset_1(E_386,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_1407])).

tff(c_1540,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6') ),
    inference(resolution,[status(thm)],[c_253,c_1525])).

tff(c_1560,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != '#skF_9'
    | ~ m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_1540])).

tff(c_1567,plain,(
    ~ m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1560])).

tff(c_753,plain,(
    ! [A_285,C_284,B_286,D_287,E_288] :
      ( m1_subset_1('#skF_4'(C_284,A_285,B_286,D_287,E_288),C_284)
      | ~ r2_hidden(E_288,k7_relset_1(C_284,A_285,D_287,B_286))
      | ~ m1_subset_1(E_288,A_285)
      | ~ m1_subset_1(D_287,k1_zfmisc_1(k2_zfmisc_1(C_284,A_285)))
      | v1_xboole_0(C_284)
      | v1_xboole_0(B_286)
      | v1_xboole_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_761,plain,(
    ! [D_202,E_288] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',D_202,'#skF_8',E_288),'#skF_5')
      | ~ r2_hidden(E_288,k9_relat_1('#skF_8',D_202))
      | ~ m1_subset_1(E_288,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_202)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_753])).

tff(c_771,plain,(
    ! [D_202,E_288] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',D_202,'#skF_8',E_288),'#skF_5')
      | ~ r2_hidden(E_288,k9_relat_1('#skF_8',D_202))
      | ~ m1_subset_1(E_288,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_202)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_761])).

tff(c_1568,plain,(
    ! [D_389,E_390] :
      ( m1_subset_1('#skF_4'('#skF_5','#skF_6',D_389,'#skF_8',E_390),'#skF_5')
      | ~ r2_hidden(E_390,k9_relat_1('#skF_8',D_389))
      | ~ m1_subset_1(E_390,'#skF_6')
      | v1_xboole_0(D_389) ) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_101,c_771])).

tff(c_1587,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5')
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_253,c_1568])).

tff(c_1609,plain,
    ( m1_subset_1('#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9'),'#skF_5')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_1587])).

tff(c_1611,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_1567,c_1609])).

tff(c_1612,plain,(
    k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) != '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1560])).

tff(c_886,plain,(
    ! [D_307,E_308,B_306,C_304,A_305] :
      ( r2_hidden(k4_tarski('#skF_4'(C_304,A_305,B_306,D_307,E_308),E_308),D_307)
      | ~ r2_hidden(E_308,k7_relset_1(C_304,A_305,D_307,B_306))
      | ~ m1_subset_1(E_308,A_305)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(C_304,A_305)))
      | v1_xboole_0(C_304)
      | v1_xboole_0(B_306)
      | v1_xboole_0(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_24,plain,(
    ! [C_21,A_19,B_20] :
      ( k1_funct_1(C_21,A_19) = B_20
      | ~ r2_hidden(k4_tarski(A_19,B_20),C_21)
      | ~ v1_funct_1(C_21)
      | ~ v1_relat_1(C_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4116,plain,(
    ! [B_631,C_630,E_632,A_633,D_629] :
      ( k1_funct_1(D_629,'#skF_4'(C_630,A_633,B_631,D_629,E_632)) = E_632
      | ~ v1_funct_1(D_629)
      | ~ v1_relat_1(D_629)
      | ~ r2_hidden(E_632,k7_relset_1(C_630,A_633,D_629,B_631))
      | ~ m1_subset_1(E_632,A_633)
      | ~ m1_subset_1(D_629,k1_zfmisc_1(k2_zfmisc_1(C_630,A_633)))
      | v1_xboole_0(C_630)
      | v1_xboole_0(B_631)
      | v1_xboole_0(A_633) ) ),
    inference(resolution,[status(thm)],[c_886,c_24])).

tff(c_4137,plain,(
    ! [D_202,E_632] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6',D_202,'#skF_8',E_632)) = E_632
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8')
      | ~ r2_hidden(E_632,k9_relat_1('#skF_8',D_202))
      | ~ m1_subset_1(E_632,'#skF_6')
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6')))
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_202)
      | v1_xboole_0('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_4116])).

tff(c_4153,plain,(
    ! [D_202,E_632] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6',D_202,'#skF_8',E_632)) = E_632
      | ~ r2_hidden(E_632,k9_relat_1('#skF_8',D_202))
      | ~ m1_subset_1(E_632,'#skF_6')
      | v1_xboole_0('#skF_5')
      | v1_xboole_0(D_202)
      | v1_xboole_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_90,c_52,c_4137])).

tff(c_4157,plain,(
    ! [D_634,E_635] :
      ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6',D_634,'#skF_8',E_635)) = E_635
      | ~ r2_hidden(E_635,k9_relat_1('#skF_8',D_634))
      | ~ m1_subset_1(E_635,'#skF_6')
      | v1_xboole_0(D_634) ) ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_101,c_4153])).

tff(c_4203,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | ~ m1_subset_1('#skF_9','#skF_6')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_253,c_4157])).

tff(c_4249,plain,
    ( k1_funct_1('#skF_8','#skF_4'('#skF_5','#skF_6','#skF_7','#skF_8','#skF_9')) = '#skF_9'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_371,c_4203])).

tff(c_4251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_279,c_1612,c_4249])).

tff(c_4252,plain,(
    ! [D_207] : v1_xboole_0(k9_relat_1('#skF_8',D_207)) ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_4256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4252,c_252])).

tff(c_4258,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_8,plain,(
    ! [A_5] :
      ( m1_subset_1('#skF_2'(A_5),k1_zfmisc_1(A_5))
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4323,plain,(
    ! [A_656,B_657] :
      ( v1_xboole_0('#skF_2'(k2_zfmisc_1(A_656,B_657)))
      | ~ v1_xboole_0(A_656)
      | v1_xboole_0(k2_zfmisc_1(A_656,B_657)) ) ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_6,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0('#skF_2'(A_5))
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4328,plain,(
    ! [A_658,B_659] :
      ( ~ v1_xboole_0(A_658)
      | v1_xboole_0(k2_zfmisc_1(A_658,B_659)) ) ),
    inference(resolution,[status(thm)],[c_4323,c_6])).

tff(c_71,plain,(
    ! [B_142,A_143] :
      ( v1_xboole_0(B_142)
      | ~ m1_subset_1(B_142,k1_zfmisc_1(A_143))
      | ~ v1_xboole_0(A_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_79,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_48,c_71])).

tff(c_80,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_4331,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4328,c_80])).

tff(c_4335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4258,c_4331])).

tff(c_4336,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_4580,plain,(
    ! [A_723,C_724] :
      ( r2_hidden(k4_tarski(A_723,k1_funct_1(C_724,A_723)),C_724)
      | ~ r2_hidden(A_723,k1_relat_1(C_724))
      | ~ v1_funct_1(C_724)
      | ~ v1_relat_1(C_724) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_4629,plain,(
    ! [C_725,A_726] :
      ( ~ v1_xboole_0(C_725)
      | ~ r2_hidden(A_726,k1_relat_1(C_725))
      | ~ v1_funct_1(C_725)
      | ~ v1_relat_1(C_725) ) ),
    inference(resolution,[status(thm)],[c_4580,c_2])).

tff(c_4649,plain,(
    ! [C_727] :
      ( ~ v1_xboole_0(C_727)
      | ~ v1_funct_1(C_727)
      | ~ v1_relat_1(C_727)
      | v1_xboole_0(k1_relat_1(C_727)) ) ),
    inference(resolution,[status(thm)],[c_4,c_4629])).

tff(c_4460,plain,(
    ! [A_704,B_705,C_706,D_707] :
      ( k7_relset_1(A_704,B_705,C_706,D_707) = k9_relat_1(C_706,D_707)
      | ~ m1_subset_1(C_706,k1_zfmisc_1(k2_zfmisc_1(A_704,B_705))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_4475,plain,(
    ! [D_707] : k7_relset_1('#skF_5','#skF_6','#skF_8',D_707) = k9_relat_1('#skF_8',D_707) ),
    inference(resolution,[status(thm)],[c_48,c_4460])).

tff(c_4477,plain,(
    r2_hidden('#skF_9',k9_relat_1('#skF_8','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4475,c_46])).

tff(c_4517,plain,(
    ! [A_710,B_711,C_712] :
      ( r2_hidden('#skF_3'(A_710,B_711,C_712),k1_relat_1(C_712))
      | ~ r2_hidden(A_710,k9_relat_1(C_712,B_711))
      | ~ v1_relat_1(C_712) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_4537,plain,(
    ! [C_715,A_716,B_717] :
      ( ~ v1_xboole_0(k1_relat_1(C_715))
      | ~ r2_hidden(A_716,k9_relat_1(C_715,B_717))
      | ~ v1_relat_1(C_715) ) ),
    inference(resolution,[status(thm)],[c_4517,c_2])).

tff(c_4540,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_8'))
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4477,c_4537])).

tff(c_4551,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4347,c_4540])).

tff(c_4652,plain,
    ( ~ v1_xboole_0('#skF_8')
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(resolution,[status(thm)],[c_4649,c_4551])).

tff(c_4656,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4347,c_52,c_4336,c_4652])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:08:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.21/2.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.64  
% 7.21/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.64  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 7.21/2.64  
% 7.21/2.64  %Foreground sorts:
% 7.21/2.64  
% 7.21/2.64  
% 7.21/2.64  %Background operators:
% 7.21/2.64  
% 7.21/2.64  
% 7.21/2.64  %Foreground operators:
% 7.21/2.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.21/2.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.21/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.21/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.21/2.64  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.21/2.64  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.21/2.64  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 7.21/2.64  tff('#skF_7', type, '#skF_7': $i).
% 7.21/2.64  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.21/2.64  tff('#skF_5', type, '#skF_5': $i).
% 7.21/2.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.21/2.64  tff('#skF_6', type, '#skF_6': $i).
% 7.21/2.64  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.21/2.64  tff('#skF_9', type, '#skF_9': $i).
% 7.21/2.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.21/2.64  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.21/2.64  tff('#skF_8', type, '#skF_8': $i).
% 7.21/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.21/2.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.21/2.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.21/2.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.21/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.21/2.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.21/2.64  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.21/2.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.21/2.64  
% 7.39/2.67  tff(f_138, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 7.39/2.67  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.39/2.67  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.39/2.67  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 7.39/2.67  tff(f_93, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.39/2.67  tff(f_89, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 7.39/2.67  tff(f_53, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.39/2.67  tff(f_47, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 7.39/2.67  tff(f_85, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.39/2.67  tff(f_119, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 7.39/2.67  tff(f_74, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 7.39/2.67  tff(f_40, axiom, (![A]: (~v1_xboole_0(A) => (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_subset_1)).
% 7.39/2.67  tff(c_48, plain, (m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.39/2.67  tff(c_4338, plain, (![C_660, A_661, B_662]: (v1_relat_1(C_660) | ~m1_subset_1(C_660, k1_zfmisc_1(k2_zfmisc_1(A_661, B_662))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.67  tff(c_4347, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_4338])).
% 7.39/2.67  tff(c_52, plain, (v1_funct_1('#skF_8')), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.39/2.67  tff(c_81, plain, (![C_144, A_145, B_146]: (v1_relat_1(C_144) | ~m1_subset_1(C_144, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.39/2.67  tff(c_90, plain, (v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_48, c_81])).
% 7.39/2.67  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.39/2.67  tff(c_138, plain, (![A_159, B_160, C_161]: (r2_hidden('#skF_3'(A_159, B_160, C_161), B_160) | ~r2_hidden(A_159, k9_relat_1(C_161, B_160)) | ~v1_relat_1(C_161))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.39/2.67  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.39/2.67  tff(c_153, plain, (![B_162, A_163, C_164]: (~v1_xboole_0(B_162) | ~r2_hidden(A_163, k9_relat_1(C_164, B_162)) | ~v1_relat_1(C_164))), inference(resolution, [status(thm)], [c_138, c_2])).
% 7.49/2.67  tff(c_163, plain, (![B_162, C_164]: (~v1_xboole_0(B_162) | ~v1_relat_1(C_164) | v1_xboole_0(k9_relat_1(C_164, B_162)))), inference(resolution, [status(thm)], [c_4, c_153])).
% 7.49/2.67  tff(c_236, plain, (![A_199, B_200, C_201, D_202]: (k7_relset_1(A_199, B_200, C_201, D_202)=k9_relat_1(C_201, D_202) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.67  tff(c_251, plain, (![D_202]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_202)=k9_relat_1('#skF_8', D_202))), inference(resolution, [status(thm)], [c_48, c_236])).
% 7.49/2.67  tff(c_46, plain, (r2_hidden('#skF_9', k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.49/2.67  tff(c_64, plain, (~v1_xboole_0(k7_relset_1('#skF_5', '#skF_6', '#skF_8', '#skF_7'))), inference(resolution, [status(thm)], [c_46, c_2])).
% 7.49/2.67  tff(c_252, plain, (~v1_xboole_0(k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_64])).
% 7.49/2.67  tff(c_273, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_163, c_252])).
% 7.49/2.67  tff(c_279, plain, (~v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_273])).
% 7.49/2.67  tff(c_253, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_46])).
% 7.49/2.67  tff(c_254, plain, (![D_203]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_203)=k9_relat_1('#skF_8', D_203))), inference(resolution, [status(thm)], [c_48, c_236])).
% 7.49/2.67  tff(c_32, plain, (![A_29, B_30, C_31, D_32]: (m1_subset_1(k7_relset_1(A_29, B_30, C_31, D_32), k1_zfmisc_1(B_30)) | ~m1_subset_1(C_31, k1_zfmisc_1(k2_zfmisc_1(A_29, B_30))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 7.49/2.67  tff(c_260, plain, (![D_203]: (m1_subset_1(k9_relat_1('#skF_8', D_203), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_254, c_32])).
% 7.49/2.67  tff(c_345, plain, (![D_207]: (m1_subset_1(k9_relat_1('#skF_8', D_207), k1_zfmisc_1('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_260])).
% 7.49/2.67  tff(c_12, plain, (![A_10, C_12, B_11]: (m1_subset_1(A_10, C_12) | ~m1_subset_1(B_11, k1_zfmisc_1(C_12)) | ~r2_hidden(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.49/2.67  tff(c_355, plain, (![A_208, D_209]: (m1_subset_1(A_208, '#skF_6') | ~r2_hidden(A_208, k9_relat_1('#skF_8', D_209)))), inference(resolution, [status(thm)], [c_345, c_12])).
% 7.49/2.67  tff(c_371, plain, (m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_253, c_355])).
% 7.49/2.67  tff(c_10, plain, (![B_9, A_7]: (v1_xboole_0(B_9) | ~m1_subset_1(B_9, k1_zfmisc_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.49/2.67  tff(c_352, plain, (![D_207]: (v1_xboole_0(k9_relat_1('#skF_8', D_207)) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_345, c_10])).
% 7.49/2.67  tff(c_353, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_352])).
% 7.49/2.67  tff(c_91, plain, (![C_147, A_148, B_149]: (v1_xboole_0(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))) | ~v1_xboole_0(A_148))), inference(cnfTransformation, [status(thm)], [f_85])).
% 7.49/2.67  tff(c_100, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_48, c_91])).
% 7.49/2.67  tff(c_101, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_100])).
% 7.49/2.67  tff(c_651, plain, (![D_256, C_253, B_255, A_254, E_257]: (r2_hidden('#skF_4'(C_253, A_254, B_255, D_256, E_257), B_255) | ~r2_hidden(E_257, k7_relset_1(C_253, A_254, D_256, B_255)) | ~m1_subset_1(E_257, A_254) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(C_253, A_254))) | v1_xboole_0(C_253) | v1_xboole_0(B_255) | v1_xboole_0(A_254))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.49/2.67  tff(c_662, plain, (![B_255, E_257]: (r2_hidden('#skF_4'('#skF_5', '#skF_6', B_255, '#skF_8', E_257), B_255) | ~r2_hidden(E_257, k7_relset_1('#skF_5', '#skF_6', '#skF_8', B_255)) | ~m1_subset_1(E_257, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_255) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_48, c_651])).
% 7.49/2.67  tff(c_667, plain, (![B_255, E_257]: (r2_hidden('#skF_4'('#skF_5', '#skF_6', B_255, '#skF_8', E_257), B_255) | ~r2_hidden(E_257, k9_relat_1('#skF_8', B_255)) | ~m1_subset_1(E_257, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(B_255) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_662])).
% 7.49/2.67  tff(c_1307, plain, (![B_373, E_374]: (r2_hidden('#skF_4'('#skF_5', '#skF_6', B_373, '#skF_8', E_374), B_373) | ~r2_hidden(E_374, k9_relat_1('#skF_8', B_373)) | ~m1_subset_1(E_374, '#skF_6') | v1_xboole_0(B_373))), inference(negUnitSimplification, [status(thm)], [c_353, c_101, c_667])).
% 7.49/2.67  tff(c_44, plain, (![F_135]: (k1_funct_1('#skF_8', F_135)!='#skF_9' | ~r2_hidden(F_135, '#skF_7') | ~m1_subset_1(F_135, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.49/2.67  tff(c_1407, plain, (![E_374]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', E_374))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', E_374), '#skF_5') | ~r2_hidden(E_374, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_374, '#skF_6') | v1_xboole_0('#skF_7'))), inference(resolution, [status(thm)], [c_1307, c_44])).
% 7.49/2.67  tff(c_1525, plain, (![E_386]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', E_386))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', E_386), '#skF_5') | ~r2_hidden(E_386, k9_relat_1('#skF_8', '#skF_7')) | ~m1_subset_1(E_386, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_279, c_1407])).
% 7.49/2.67  tff(c_1540, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6')), inference(resolution, [status(thm)], [c_253, c_1525])).
% 7.49/2.67  tff(c_1560, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!='#skF_9' | ~m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_1540])).
% 7.49/2.67  tff(c_1567, plain, (~m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1560])).
% 7.49/2.67  tff(c_753, plain, (![A_285, C_284, B_286, D_287, E_288]: (m1_subset_1('#skF_4'(C_284, A_285, B_286, D_287, E_288), C_284) | ~r2_hidden(E_288, k7_relset_1(C_284, A_285, D_287, B_286)) | ~m1_subset_1(E_288, A_285) | ~m1_subset_1(D_287, k1_zfmisc_1(k2_zfmisc_1(C_284, A_285))) | v1_xboole_0(C_284) | v1_xboole_0(B_286) | v1_xboole_0(A_285))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.49/2.67  tff(c_761, plain, (![D_202, E_288]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', D_202, '#skF_8', E_288), '#skF_5') | ~r2_hidden(E_288, k9_relat_1('#skF_8', D_202)) | ~m1_subset_1(E_288, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_202) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_753])).
% 7.49/2.67  tff(c_771, plain, (![D_202, E_288]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', D_202, '#skF_8', E_288), '#skF_5') | ~r2_hidden(E_288, k9_relat_1('#skF_8', D_202)) | ~m1_subset_1(E_288, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_202) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_761])).
% 7.49/2.67  tff(c_1568, plain, (![D_389, E_390]: (m1_subset_1('#skF_4'('#skF_5', '#skF_6', D_389, '#skF_8', E_390), '#skF_5') | ~r2_hidden(E_390, k9_relat_1('#skF_8', D_389)) | ~m1_subset_1(E_390, '#skF_6') | v1_xboole_0(D_389))), inference(negUnitSimplification, [status(thm)], [c_353, c_101, c_771])).
% 7.49/2.67  tff(c_1587, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5') | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_253, c_1568])).
% 7.49/2.67  tff(c_1609, plain, (m1_subset_1('#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'), '#skF_5') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_1587])).
% 7.49/2.67  tff(c_1611, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_1567, c_1609])).
% 7.49/2.67  tff(c_1612, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))!='#skF_9'), inference(splitRight, [status(thm)], [c_1560])).
% 7.49/2.67  tff(c_886, plain, (![D_307, E_308, B_306, C_304, A_305]: (r2_hidden(k4_tarski('#skF_4'(C_304, A_305, B_306, D_307, E_308), E_308), D_307) | ~r2_hidden(E_308, k7_relset_1(C_304, A_305, D_307, B_306)) | ~m1_subset_1(E_308, A_305) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(C_304, A_305))) | v1_xboole_0(C_304) | v1_xboole_0(B_306) | v1_xboole_0(A_305))), inference(cnfTransformation, [status(thm)], [f_119])).
% 7.49/2.67  tff(c_24, plain, (![C_21, A_19, B_20]: (k1_funct_1(C_21, A_19)=B_20 | ~r2_hidden(k4_tarski(A_19, B_20), C_21) | ~v1_funct_1(C_21) | ~v1_relat_1(C_21))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.49/2.67  tff(c_4116, plain, (![B_631, C_630, E_632, A_633, D_629]: (k1_funct_1(D_629, '#skF_4'(C_630, A_633, B_631, D_629, E_632))=E_632 | ~v1_funct_1(D_629) | ~v1_relat_1(D_629) | ~r2_hidden(E_632, k7_relset_1(C_630, A_633, D_629, B_631)) | ~m1_subset_1(E_632, A_633) | ~m1_subset_1(D_629, k1_zfmisc_1(k2_zfmisc_1(C_630, A_633))) | v1_xboole_0(C_630) | v1_xboole_0(B_631) | v1_xboole_0(A_633))), inference(resolution, [status(thm)], [c_886, c_24])).
% 7.49/2.67  tff(c_4137, plain, (![D_202, E_632]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', D_202, '#skF_8', E_632))=E_632 | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8') | ~r2_hidden(E_632, k9_relat_1('#skF_8', D_202)) | ~m1_subset_1(E_632, '#skF_6') | ~m1_subset_1('#skF_8', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6'))) | v1_xboole_0('#skF_5') | v1_xboole_0(D_202) | v1_xboole_0('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_4116])).
% 7.49/2.67  tff(c_4153, plain, (![D_202, E_632]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', D_202, '#skF_8', E_632))=E_632 | ~r2_hidden(E_632, k9_relat_1('#skF_8', D_202)) | ~m1_subset_1(E_632, '#skF_6') | v1_xboole_0('#skF_5') | v1_xboole_0(D_202) | v1_xboole_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_90, c_52, c_4137])).
% 7.49/2.67  tff(c_4157, plain, (![D_634, E_635]: (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', D_634, '#skF_8', E_635))=E_635 | ~r2_hidden(E_635, k9_relat_1('#skF_8', D_634)) | ~m1_subset_1(E_635, '#skF_6') | v1_xboole_0(D_634))), inference(negUnitSimplification, [status(thm)], [c_353, c_101, c_4153])).
% 7.49/2.67  tff(c_4203, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | ~m1_subset_1('#skF_9', '#skF_6') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_253, c_4157])).
% 7.49/2.67  tff(c_4249, plain, (k1_funct_1('#skF_8', '#skF_4'('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_9'))='#skF_9' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_371, c_4203])).
% 7.49/2.67  tff(c_4251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_279, c_1612, c_4249])).
% 7.49/2.67  tff(c_4252, plain, (![D_207]: (v1_xboole_0(k9_relat_1('#skF_8', D_207)))), inference(splitRight, [status(thm)], [c_352])).
% 7.49/2.67  tff(c_4256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4252, c_252])).
% 7.49/2.67  tff(c_4258, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_100])).
% 7.49/2.67  tff(c_8, plain, (![A_5]: (m1_subset_1('#skF_2'(A_5), k1_zfmisc_1(A_5)) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.49/2.67  tff(c_4323, plain, (![A_656, B_657]: (v1_xboole_0('#skF_2'(k2_zfmisc_1(A_656, B_657))) | ~v1_xboole_0(A_656) | v1_xboole_0(k2_zfmisc_1(A_656, B_657)))), inference(resolution, [status(thm)], [c_8, c_91])).
% 7.49/2.67  tff(c_6, plain, (![A_5]: (~v1_xboole_0('#skF_2'(A_5)) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 7.49/2.67  tff(c_4328, plain, (![A_658, B_659]: (~v1_xboole_0(A_658) | v1_xboole_0(k2_zfmisc_1(A_658, B_659)))), inference(resolution, [status(thm)], [c_4323, c_6])).
% 7.49/2.67  tff(c_71, plain, (![B_142, A_143]: (v1_xboole_0(B_142) | ~m1_subset_1(B_142, k1_zfmisc_1(A_143)) | ~v1_xboole_0(A_143))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.49/2.67  tff(c_79, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_48, c_71])).
% 7.49/2.67  tff(c_80, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_79])).
% 7.49/2.67  tff(c_4331, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4328, c_80])).
% 7.49/2.67  tff(c_4335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4258, c_4331])).
% 7.49/2.67  tff(c_4336, plain, (v1_xboole_0('#skF_8')), inference(splitRight, [status(thm)], [c_79])).
% 7.49/2.67  tff(c_4580, plain, (![A_723, C_724]: (r2_hidden(k4_tarski(A_723, k1_funct_1(C_724, A_723)), C_724) | ~r2_hidden(A_723, k1_relat_1(C_724)) | ~v1_funct_1(C_724) | ~v1_relat_1(C_724))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.49/2.67  tff(c_4629, plain, (![C_725, A_726]: (~v1_xboole_0(C_725) | ~r2_hidden(A_726, k1_relat_1(C_725)) | ~v1_funct_1(C_725) | ~v1_relat_1(C_725))), inference(resolution, [status(thm)], [c_4580, c_2])).
% 7.49/2.67  tff(c_4649, plain, (![C_727]: (~v1_xboole_0(C_727) | ~v1_funct_1(C_727) | ~v1_relat_1(C_727) | v1_xboole_0(k1_relat_1(C_727)))), inference(resolution, [status(thm)], [c_4, c_4629])).
% 7.49/2.67  tff(c_4460, plain, (![A_704, B_705, C_706, D_707]: (k7_relset_1(A_704, B_705, C_706, D_707)=k9_relat_1(C_706, D_707) | ~m1_subset_1(C_706, k1_zfmisc_1(k2_zfmisc_1(A_704, B_705))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 7.49/2.67  tff(c_4475, plain, (![D_707]: (k7_relset_1('#skF_5', '#skF_6', '#skF_8', D_707)=k9_relat_1('#skF_8', D_707))), inference(resolution, [status(thm)], [c_48, c_4460])).
% 7.49/2.67  tff(c_4477, plain, (r2_hidden('#skF_9', k9_relat_1('#skF_8', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_4475, c_46])).
% 7.49/2.67  tff(c_4517, plain, (![A_710, B_711, C_712]: (r2_hidden('#skF_3'(A_710, B_711, C_712), k1_relat_1(C_712)) | ~r2_hidden(A_710, k9_relat_1(C_712, B_711)) | ~v1_relat_1(C_712))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.49/2.67  tff(c_4537, plain, (![C_715, A_716, B_717]: (~v1_xboole_0(k1_relat_1(C_715)) | ~r2_hidden(A_716, k9_relat_1(C_715, B_717)) | ~v1_relat_1(C_715))), inference(resolution, [status(thm)], [c_4517, c_2])).
% 7.49/2.67  tff(c_4540, plain, (~v1_xboole_0(k1_relat_1('#skF_8')) | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_4477, c_4537])).
% 7.49/2.67  tff(c_4551, plain, (~v1_xboole_0(k1_relat_1('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4347, c_4540])).
% 7.49/2.67  tff(c_4652, plain, (~v1_xboole_0('#skF_8') | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(resolution, [status(thm)], [c_4649, c_4551])).
% 7.49/2.67  tff(c_4656, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4347, c_52, c_4336, c_4652])).
% 7.49/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.49/2.67  
% 7.49/2.67  Inference rules
% 7.49/2.67  ----------------------
% 7.49/2.67  #Ref     : 0
% 7.49/2.67  #Sup     : 936
% 7.49/2.67  #Fact    : 0
% 7.49/2.67  #Define  : 0
% 7.49/2.67  #Split   : 16
% 7.49/2.67  #Chain   : 0
% 7.49/2.67  #Close   : 0
% 7.49/2.67  
% 7.49/2.67  Ordering : KBO
% 7.49/2.67  
% 7.49/2.67  Simplification rules
% 7.49/2.67  ----------------------
% 7.49/2.67  #Subsume      : 244
% 7.49/2.67  #Demod        : 159
% 7.49/2.67  #Tautology    : 44
% 7.49/2.67  #SimpNegUnit  : 38
% 7.49/2.67  #BackRed      : 5
% 7.49/2.67  
% 7.49/2.67  #Partial instantiations: 0
% 7.49/2.67  #Strategies tried      : 1
% 7.49/2.67  
% 7.49/2.67  Timing (in seconds)
% 7.49/2.67  ----------------------
% 7.49/2.67  Preprocessing        : 0.33
% 7.49/2.67  Parsing              : 0.16
% 7.49/2.67  CNF conversion       : 0.04
% 7.49/2.67  Main loop            : 1.45
% 7.49/2.67  Inferencing          : 0.46
% 7.49/2.67  Reduction            : 0.31
% 7.49/2.67  Demodulation         : 0.21
% 7.49/2.67  BG Simplification    : 0.04
% 7.49/2.67  Subsumption          : 0.53
% 7.49/2.67  Abstraction          : 0.07
% 7.49/2.67  MUC search           : 0.00
% 7.49/2.67  Cooper               : 0.00
% 7.49/2.67  Total                : 1.84
% 7.49/2.67  Index Insertion      : 0.00
% 7.49/2.67  Index Deletion       : 0.00
% 7.49/2.67  Index Matching       : 0.00
% 7.49/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
