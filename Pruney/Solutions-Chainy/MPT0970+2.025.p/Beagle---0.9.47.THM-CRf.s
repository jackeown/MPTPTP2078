%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:22 EST 2020

% Result     : Theorem 4.67s
% Output     : CNFRefutation 5.06s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 874 expanded)
%              Number of leaves         :   36 ( 316 expanded)
%              Depth                    :   26
%              Number of atoms          :  324 (2972 expanded)
%              Number of equality atoms :   99 ( 972 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_117,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_52,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_86,axiom,(
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

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_98,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_196,plain,(
    ! [A_101,B_102,C_103] :
      ( k2_relset_1(A_101,B_102,C_103) = k2_relat_1(C_103)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_205,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_196])).

tff(c_54,plain,(
    k2_relset_1('#skF_5','#skF_6','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_206,plain,(
    k2_relat_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_54])).

tff(c_58,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_88,plain,(
    ! [C_78,A_79,B_80] :
      ( v1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_79,B_80))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_97,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_28,plain,(
    ! [A_6,B_28] :
      ( k1_funct_1(A_6,'#skF_2'(A_6,B_28)) = '#skF_1'(A_6,B_28)
      | r2_hidden('#skF_3'(A_6,B_28),B_28)
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_64,plain,(
    ! [D_68] :
      ( r2_hidden('#skF_8'(D_68),'#skF_5')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_142,plain,(
    ! [A_89,B_90,C_91] :
      ( k1_relset_1(A_89,B_90,C_91) = k1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_151,plain,(
    k1_relset_1('#skF_5','#skF_6','#skF_7') = k1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_56,c_142])).

tff(c_702,plain,(
    ! [B_159,A_160,C_161] :
      ( k1_xboole_0 = B_159
      | k1_relset_1(A_160,B_159,C_161) = A_160
      | ~ v1_funct_2(C_161,A_160,B_159)
      | ~ m1_subset_1(C_161,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_717,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relset_1('#skF_5','#skF_6','#skF_7') = '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_702])).

tff(c_724,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_151,c_717])).

tff(c_725,plain,(
    k1_relat_1('#skF_7') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_724])).

tff(c_62,plain,(
    ! [D_68] :
      ( k1_funct_1('#skF_7','#skF_8'(D_68)) = D_68
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_1543,plain,(
    ! [A_263,B_264,D_265] :
      ( k1_funct_1(A_263,'#skF_2'(A_263,B_264)) = '#skF_1'(A_263,B_264)
      | k1_funct_1(A_263,D_265) != '#skF_3'(A_263,B_264)
      | ~ r2_hidden(D_265,k1_relat_1(A_263))
      | k2_relat_1(A_263) = B_264
      | ~ v1_funct_1(A_263)
      | ~ v1_relat_1(A_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1549,plain,(
    ! [B_264,D_68] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_264)) = '#skF_1'('#skF_7',B_264)
      | D_68 != '#skF_3'('#skF_7',B_264)
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_264
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1543])).

tff(c_1551,plain,(
    ! [B_264,D_68] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_264)) = '#skF_1'('#skF_7',B_264)
      | D_68 != '#skF_3'('#skF_7',B_264)
      | ~ r2_hidden('#skF_8'(D_68),'#skF_5')
      | k2_relat_1('#skF_7') = B_264
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_725,c_1549])).

tff(c_1937,plain,(
    ! [B_321] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_321)) = '#skF_1'('#skF_7',B_321)
      | ~ r2_hidden('#skF_8'('#skF_3'('#skF_7',B_321)),'#skF_5')
      | k2_relat_1('#skF_7') = B_321
      | ~ r2_hidden('#skF_3'('#skF_7',B_321),'#skF_6') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1551])).

tff(c_1942,plain,(
    ! [B_322] :
      ( k1_funct_1('#skF_7','#skF_2'('#skF_7',B_322)) = '#skF_1'('#skF_7',B_322)
      | k2_relat_1('#skF_7') = B_322
      | ~ r2_hidden('#skF_3'('#skF_7',B_322),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_1937])).

tff(c_1946,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_28,c_1942])).

tff(c_1959,plain,
    ( k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_1946])).

tff(c_1960,plain,(
    k1_funct_1('#skF_7','#skF_2'('#skF_7','#skF_6')) = '#skF_1'('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_1959])).

tff(c_837,plain,(
    ! [A_177,B_178] :
      ( r2_hidden('#skF_2'(A_177,B_178),k1_relat_1(A_177))
      | r2_hidden('#skF_3'(A_177,B_178),B_178)
      | k2_relat_1(A_177) = B_178
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_840,plain,(
    ! [B_178] :
      ( r2_hidden('#skF_2'('#skF_7',B_178),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_178),B_178)
      | k2_relat_1('#skF_7') = B_178
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_837])).

tff(c_842,plain,(
    ! [B_178] :
      ( r2_hidden('#skF_2'('#skF_7',B_178),'#skF_5')
      | r2_hidden('#skF_3'('#skF_7',B_178),B_178)
      | k2_relat_1('#skF_7') = B_178 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_840])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1026,plain,(
    ! [D_202,C_203,B_204,A_205] :
      ( r2_hidden(k1_funct_1(D_202,C_203),B_204)
      | k1_xboole_0 = B_204
      | ~ r2_hidden(C_203,A_205)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(k2_zfmisc_1(A_205,B_204)))
      | ~ v1_funct_2(D_202,A_205,B_204)
      | ~ v1_funct_1(D_202) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1232,plain,(
    ! [D_227,D_228,B_229] :
      ( r2_hidden(k1_funct_1(D_227,'#skF_8'(D_228)),B_229)
      | k1_xboole_0 = B_229
      | ~ m1_subset_1(D_227,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_229)))
      | ~ v1_funct_2(D_227,'#skF_5',B_229)
      | ~ v1_funct_1(D_227)
      | ~ r2_hidden(D_228,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_1026])).

tff(c_1237,plain,(
    ! [D_68,B_229] :
      ( r2_hidden(D_68,B_229)
      | k1_xboole_0 = B_229
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_229)))
      | ~ v1_funct_2('#skF_7','#skF_5',B_229)
      | ~ v1_funct_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1232])).

tff(c_1471,plain,(
    ! [D_253,B_254] :
      ( r2_hidden(D_253,B_254)
      | k1_xboole_0 = B_254
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_254)))
      | ~ v1_funct_2('#skF_7','#skF_5',B_254)
      | ~ r2_hidden(D_253,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1237])).

tff(c_1483,plain,(
    ! [D_255,B_256] :
      ( r2_hidden(D_255,B_256)
      | k1_xboole_0 = B_256
      | ~ v1_funct_2('#skF_7','#skF_5',B_256)
      | ~ r2_hidden(D_255,'#skF_6')
      | ~ r1_tarski('#skF_7',k2_zfmisc_1('#skF_5',B_256)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1471])).

tff(c_1492,plain,(
    ! [B_256] :
      ( r2_hidden('#skF_3'('#skF_7','#skF_6'),B_256)
      | k1_xboole_0 = B_256
      | ~ v1_funct_2('#skF_7','#skF_5',B_256)
      | ~ r1_tarski('#skF_7',k2_zfmisc_1('#skF_5',B_256))
      | r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_842,c_1483])).

tff(c_1501,plain,(
    ! [B_256] :
      ( r2_hidden('#skF_3'('#skF_7','#skF_6'),B_256)
      | k1_xboole_0 = B_256
      | ~ v1_funct_2('#skF_7','#skF_5',B_256)
      | ~ r1_tarski('#skF_7',k2_zfmisc_1('#skF_5',B_256))
      | r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_1492])).

tff(c_1692,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1501])).

tff(c_52,plain,(
    ! [D_64,C_63,B_62,A_61] :
      ( r2_hidden(k1_funct_1(D_64,C_63),B_62)
      | k1_xboole_0 = B_62
      | ~ r2_hidden(C_63,A_61)
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(D_64,A_61,B_62)
      | ~ v1_funct_1(D_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_1695,plain,(
    ! [D_64,B_62] :
      ( r2_hidden(k1_funct_1(D_64,'#skF_2'('#skF_7','#skF_6')),B_62)
      | k1_xboole_0 = B_62
      | ~ m1_subset_1(D_64,k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_62)))
      | ~ v1_funct_2(D_64,'#skF_5',B_62)
      | ~ v1_funct_1(D_64) ) ),
    inference(resolution,[status(thm)],[c_1692,c_52])).

tff(c_1971,plain,(
    ! [B_62] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),B_62)
      | k1_xboole_0 = B_62
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_62)))
      | ~ v1_funct_2('#skF_7','#skF_5',B_62)
      | ~ v1_funct_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1960,c_1695])).

tff(c_2058,plain,(
    ! [B_328] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),B_328)
      | k1_xboole_0 = B_328
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5',B_328)))
      | ~ v1_funct_2('#skF_7','#skF_5',B_328) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_1971])).

tff(c_2064,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_xboole_0 = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_2058])).

tff(c_2068,plain,
    ( r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6')
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2064])).

tff(c_2069,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2068])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2122,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2069,c_8])).

tff(c_243,plain,(
    ! [A_111,B_112,C_113] :
      ( m1_subset_1(k2_relset_1(A_111,B_112,C_113),k1_zfmisc_1(B_112))
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_267,plain,
    ( m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6'))
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_243])).

tff(c_273,plain,(
    m1_subset_1(k2_relat_1('#skF_7'),k1_zfmisc_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_267])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_277,plain,(
    r1_tarski(k2_relat_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_273,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_290,plain,
    ( k2_relat_1('#skF_7') = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_relat_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_277,c_2])).

tff(c_293,plain,(
    ~ r1_tarski('#skF_6',k2_relat_1('#skF_7')) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_290])).

tff(c_2148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2122,c_293])).

tff(c_2150,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2068])).

tff(c_68,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(A_72,B_73)
      | ~ m1_subset_1(A_72,k1_zfmisc_1(B_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_56,c_68])).

tff(c_2065,plain,(
    ! [B_328] :
      ( r2_hidden('#skF_1'('#skF_7','#skF_6'),B_328)
      | k1_xboole_0 = B_328
      | ~ v1_funct_2('#skF_7','#skF_5',B_328)
      | ~ r1_tarski('#skF_7',k2_zfmisc_1('#skF_5',B_328)) ) ),
    inference(resolution,[status(thm)],[c_12,c_2058])).

tff(c_26,plain,(
    ! [A_6,B_28] :
      ( ~ r2_hidden('#skF_1'(A_6,B_28),B_28)
      | r2_hidden('#skF_3'(A_6,B_28),B_28)
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_301,plain,(
    ! [A_118,D_119] :
      ( r2_hidden(k1_funct_1(A_118,D_119),k2_relat_1(A_118))
      | ~ r2_hidden(D_119,k1_relat_1(A_118))
      | ~ v1_funct_1(A_118)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_304,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_301])).

tff(c_306,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_304])).

tff(c_741,plain,(
    ! [D_162] :
      ( r2_hidden(D_162,k2_relat_1('#skF_7'))
      | ~ r2_hidden('#skF_8'(D_162),'#skF_5')
      | ~ r2_hidden(D_162,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_725,c_306])).

tff(c_745,plain,(
    ! [D_68] :
      ( r2_hidden(D_68,k2_relat_1('#skF_7'))
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_741])).

tff(c_16,plain,(
    ! [A_6,C_42] :
      ( k1_funct_1(A_6,'#skF_4'(A_6,k2_relat_1(A_6),C_42)) = C_42
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [A_6,C_42] :
      ( r2_hidden('#skF_4'(A_6,k2_relat_1(A_6),C_42),k1_relat_1(A_6))
      | ~ r2_hidden(C_42,k2_relat_1(A_6))
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_731,plain,(
    ! [C_42] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_42),'#skF_5')
      | ~ r2_hidden(C_42,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_725,c_18])).

tff(c_735,plain,(
    ! [C_42] :
      ( r2_hidden('#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_42),'#skF_5')
      | ~ r2_hidden(C_42,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_731])).

tff(c_2149,plain,(
    r2_hidden('#skF_1'('#skF_7','#skF_6'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2068])).

tff(c_20,plain,(
    ! [A_6,B_28,D_41] :
      ( ~ r2_hidden('#skF_1'(A_6,B_28),B_28)
      | k1_funct_1(A_6,D_41) != '#skF_3'(A_6,B_28)
      | ~ r2_hidden(D_41,k1_relat_1(A_6))
      | k2_relat_1(A_6) = B_28
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2175,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_7',D_41) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_41,k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = '#skF_6'
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(resolution,[status(thm)],[c_2149,c_20])).

tff(c_2181,plain,(
    ! [D_41] :
      ( k1_funct_1('#skF_7',D_41) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_41,'#skF_5')
      | k2_relat_1('#skF_7') = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_725,c_2175])).

tff(c_2184,plain,(
    ! [D_335] :
      ( k1_funct_1('#skF_7',D_335) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_335,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_2181])).

tff(c_2279,plain,(
    ! [C_338] :
      ( k1_funct_1('#skF_7','#skF_4'('#skF_7',k2_relat_1('#skF_7'),C_338)) != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_338,k2_relat_1('#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_735,c_2184])).

tff(c_2283,plain,(
    ! [C_42] :
      ( C_42 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_42,k2_relat_1('#skF_7'))
      | ~ r2_hidden(C_42,k2_relat_1('#skF_7'))
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2279])).

tff(c_2303,plain,(
    ! [C_342] :
      ( C_342 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(C_342,k2_relat_1('#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_2283])).

tff(c_2356,plain,(
    ! [D_343] :
      ( D_343 != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden(D_343,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_745,c_2303])).

tff(c_2453,plain,(
    ! [A_346] :
      ( '#skF_3'(A_346,'#skF_6') != '#skF_3'('#skF_7','#skF_6')
      | ~ r2_hidden('#skF_1'(A_346,'#skF_6'),'#skF_6')
      | k2_relat_1(A_346) = '#skF_6'
      | ~ v1_funct_1(A_346)
      | ~ v1_relat_1(A_346) ) ),
    inference(resolution,[status(thm)],[c_26,c_2356])).

tff(c_2457,plain,
    ( k2_relat_1('#skF_7') = '#skF_6'
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7')
    | k1_xboole_0 = '#skF_6'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_6')
    | ~ r1_tarski('#skF_7',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2065,c_2453])).

tff(c_2463,plain,
    ( k2_relat_1('#skF_7') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_58,c_97,c_60,c_2457])).

tff(c_2465,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2150,c_206,c_2463])).

tff(c_2467,plain,(
    ~ r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1501])).

tff(c_1368,plain,(
    ! [A_240,B_241,D_242] :
      ( r2_hidden('#skF_2'(A_240,B_241),k1_relat_1(A_240))
      | k1_funct_1(A_240,D_242) != '#skF_3'(A_240,B_241)
      | ~ r2_hidden(D_242,k1_relat_1(A_240))
      | k2_relat_1(A_240) = B_241
      | ~ v1_funct_1(A_240)
      | ~ v1_relat_1(A_240) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1374,plain,(
    ! [B_241,D_68] :
      ( r2_hidden('#skF_2'('#skF_7',B_241),k1_relat_1('#skF_7'))
      | D_68 != '#skF_3'('#skF_7',B_241)
      | ~ r2_hidden('#skF_8'(D_68),k1_relat_1('#skF_7'))
      | k2_relat_1('#skF_7') = B_241
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1368])).

tff(c_1376,plain,(
    ! [B_241,D_68] :
      ( r2_hidden('#skF_2'('#skF_7',B_241),'#skF_5')
      | D_68 != '#skF_3'('#skF_7',B_241)
      | ~ r2_hidden('#skF_8'(D_68),'#skF_5')
      | k2_relat_1('#skF_7') = B_241
      | ~ r2_hidden(D_68,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_60,c_725,c_725,c_1374])).

tff(c_2545,plain,(
    ! [B_358] :
      ( r2_hidden('#skF_2'('#skF_7',B_358),'#skF_5')
      | ~ r2_hidden('#skF_8'('#skF_3'('#skF_7',B_358)),'#skF_5')
      | k2_relat_1('#skF_7') = B_358
      | ~ r2_hidden('#skF_3'('#skF_7',B_358),'#skF_6') ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_1376])).

tff(c_2550,plain,(
    ! [B_359] :
      ( r2_hidden('#skF_2'('#skF_7',B_359),'#skF_5')
      | k2_relat_1('#skF_7') = B_359
      | ~ r2_hidden('#skF_3'('#skF_7',B_359),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_64,c_2545])).

tff(c_2562,plain,
    ( r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_5')
    | k2_relat_1('#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_842,c_2550])).

tff(c_2580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_206,c_2467,c_206,c_2467,c_2562])).

tff(c_2581,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_724])).

tff(c_2603,plain,(
    ! [A_3] : r1_tarski('#skF_6',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2581,c_8])).

tff(c_2611,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2603,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.67/1.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.93  
% 5.06/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.93  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_8 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_1
% 5.06/1.93  
% 5.06/1.93  %Foreground sorts:
% 5.06/1.93  
% 5.06/1.93  
% 5.06/1.93  %Background operators:
% 5.06/1.93  
% 5.06/1.93  
% 5.06/1.93  %Foreground operators:
% 5.06/1.93  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.06/1.93  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.06/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.06/1.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.06/1.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.06/1.93  tff('#skF_8', type, '#skF_8': $i > $i).
% 5.06/1.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 5.06/1.93  tff('#skF_7', type, '#skF_7': $i).
% 5.06/1.93  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.06/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.06/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.06/1.93  tff('#skF_5', type, '#skF_5': $i).
% 5.06/1.93  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.06/1.93  tff('#skF_6', type, '#skF_6': $i).
% 5.06/1.93  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.06/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.06/1.94  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.06/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.06/1.94  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.06/1.94  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.06/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.06/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.06/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.06/1.94  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.06/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.06/1.94  
% 5.06/1.96  tff(f_117, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 5.06/1.96  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.06/1.96  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 5.06/1.96  tff(f_52, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 5.06/1.96  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.06/1.96  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.06/1.96  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.06/1.96  tff(f_98, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 5.06/1.96  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.06/1.96  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 5.06/1.96  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.06/1.96  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.06/1.96  tff(c_196, plain, (![A_101, B_102, C_103]: (k2_relset_1(A_101, B_102, C_103)=k2_relat_1(C_103) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.06/1.96  tff(c_205, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_196])).
% 5.06/1.96  tff(c_54, plain, (k2_relset_1('#skF_5', '#skF_6', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.06/1.96  tff(c_206, plain, (k2_relat_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_205, c_54])).
% 5.06/1.96  tff(c_58, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.06/1.96  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.06/1.96  tff(c_88, plain, (![C_78, A_79, B_80]: (v1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_79, B_80))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.06/1.96  tff(c_97, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_88])).
% 5.06/1.96  tff(c_28, plain, (![A_6, B_28]: (k1_funct_1(A_6, '#skF_2'(A_6, B_28))='#skF_1'(A_6, B_28) | r2_hidden('#skF_3'(A_6, B_28), B_28) | k2_relat_1(A_6)=B_28 | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_64, plain, (![D_68]: (r2_hidden('#skF_8'(D_68), '#skF_5') | ~r2_hidden(D_68, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.06/1.96  tff(c_142, plain, (![A_89, B_90, C_91]: (k1_relset_1(A_89, B_90, C_91)=k1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.06/1.96  tff(c_151, plain, (k1_relset_1('#skF_5', '#skF_6', '#skF_7')=k1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_56, c_142])).
% 5.06/1.96  tff(c_702, plain, (![B_159, A_160, C_161]: (k1_xboole_0=B_159 | k1_relset_1(A_160, B_159, C_161)=A_160 | ~v1_funct_2(C_161, A_160, B_159) | ~m1_subset_1(C_161, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.06/1.96  tff(c_717, plain, (k1_xboole_0='#skF_6' | k1_relset_1('#skF_5', '#skF_6', '#skF_7')='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_702])).
% 5.06/1.96  tff(c_724, plain, (k1_xboole_0='#skF_6' | k1_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_151, c_717])).
% 5.06/1.96  tff(c_725, plain, (k1_relat_1('#skF_7')='#skF_5'), inference(splitLeft, [status(thm)], [c_724])).
% 5.06/1.96  tff(c_62, plain, (![D_68]: (k1_funct_1('#skF_7', '#skF_8'(D_68))=D_68 | ~r2_hidden(D_68, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_117])).
% 5.06/1.96  tff(c_1543, plain, (![A_263, B_264, D_265]: (k1_funct_1(A_263, '#skF_2'(A_263, B_264))='#skF_1'(A_263, B_264) | k1_funct_1(A_263, D_265)!='#skF_3'(A_263, B_264) | ~r2_hidden(D_265, k1_relat_1(A_263)) | k2_relat_1(A_263)=B_264 | ~v1_funct_1(A_263) | ~v1_relat_1(A_263))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_1549, plain, (![B_264, D_68]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_264))='#skF_1'('#skF_7', B_264) | D_68!='#skF_3'('#skF_7', B_264) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_264 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1543])).
% 5.06/1.96  tff(c_1551, plain, (![B_264, D_68]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_264))='#skF_1'('#skF_7', B_264) | D_68!='#skF_3'('#skF_7', B_264) | ~r2_hidden('#skF_8'(D_68), '#skF_5') | k2_relat_1('#skF_7')=B_264 | ~r2_hidden(D_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_725, c_1549])).
% 5.06/1.96  tff(c_1937, plain, (![B_321]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_321))='#skF_1'('#skF_7', B_321) | ~r2_hidden('#skF_8'('#skF_3'('#skF_7', B_321)), '#skF_5') | k2_relat_1('#skF_7')=B_321 | ~r2_hidden('#skF_3'('#skF_7', B_321), '#skF_6'))), inference(reflexivity, [status(thm), theory('equality')], [c_1551])).
% 5.06/1.96  tff(c_1942, plain, (![B_322]: (k1_funct_1('#skF_7', '#skF_2'('#skF_7', B_322))='#skF_1'('#skF_7', B_322) | k2_relat_1('#skF_7')=B_322 | ~r2_hidden('#skF_3'('#skF_7', B_322), '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_1937])).
% 5.06/1.96  tff(c_1946, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6') | k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_28, c_1942])).
% 5.06/1.96  tff(c_1959, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6') | k2_relat_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_1946])).
% 5.06/1.96  tff(c_1960, plain, (k1_funct_1('#skF_7', '#skF_2'('#skF_7', '#skF_6'))='#skF_1'('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_206, c_1959])).
% 5.06/1.96  tff(c_837, plain, (![A_177, B_178]: (r2_hidden('#skF_2'(A_177, B_178), k1_relat_1(A_177)) | r2_hidden('#skF_3'(A_177, B_178), B_178) | k2_relat_1(A_177)=B_178 | ~v1_funct_1(A_177) | ~v1_relat_1(A_177))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_840, plain, (![B_178]: (r2_hidden('#skF_2'('#skF_7', B_178), '#skF_5') | r2_hidden('#skF_3'('#skF_7', B_178), B_178) | k2_relat_1('#skF_7')=B_178 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_725, c_837])).
% 5.06/1.96  tff(c_842, plain, (![B_178]: (r2_hidden('#skF_2'('#skF_7', B_178), '#skF_5') | r2_hidden('#skF_3'('#skF_7', B_178), B_178) | k2_relat_1('#skF_7')=B_178)), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_840])).
% 5.06/1.96  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.06/1.96  tff(c_1026, plain, (![D_202, C_203, B_204, A_205]: (r2_hidden(k1_funct_1(D_202, C_203), B_204) | k1_xboole_0=B_204 | ~r2_hidden(C_203, A_205) | ~m1_subset_1(D_202, k1_zfmisc_1(k2_zfmisc_1(A_205, B_204))) | ~v1_funct_2(D_202, A_205, B_204) | ~v1_funct_1(D_202))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.06/1.96  tff(c_1232, plain, (![D_227, D_228, B_229]: (r2_hidden(k1_funct_1(D_227, '#skF_8'(D_228)), B_229) | k1_xboole_0=B_229 | ~m1_subset_1(D_227, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_229))) | ~v1_funct_2(D_227, '#skF_5', B_229) | ~v1_funct_1(D_227) | ~r2_hidden(D_228, '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_1026])).
% 5.06/1.96  tff(c_1237, plain, (![D_68, B_229]: (r2_hidden(D_68, B_229) | k1_xboole_0=B_229 | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_229))) | ~v1_funct_2('#skF_7', '#skF_5', B_229) | ~v1_funct_1('#skF_7') | ~r2_hidden(D_68, '#skF_6') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1232])).
% 5.06/1.96  tff(c_1471, plain, (![D_253, B_254]: (r2_hidden(D_253, B_254) | k1_xboole_0=B_254 | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_254))) | ~v1_funct_2('#skF_7', '#skF_5', B_254) | ~r2_hidden(D_253, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1237])).
% 5.06/1.96  tff(c_1483, plain, (![D_255, B_256]: (r2_hidden(D_255, B_256) | k1_xboole_0=B_256 | ~v1_funct_2('#skF_7', '#skF_5', B_256) | ~r2_hidden(D_255, '#skF_6') | ~r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', B_256)))), inference(resolution, [status(thm)], [c_12, c_1471])).
% 5.06/1.96  tff(c_1492, plain, (![B_256]: (r2_hidden('#skF_3'('#skF_7', '#skF_6'), B_256) | k1_xboole_0=B_256 | ~v1_funct_2('#skF_7', '#skF_5', B_256) | ~r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', B_256)) | r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5') | k2_relat_1('#skF_7')='#skF_6')), inference(resolution, [status(thm)], [c_842, c_1483])).
% 5.06/1.96  tff(c_1501, plain, (![B_256]: (r2_hidden('#skF_3'('#skF_7', '#skF_6'), B_256) | k1_xboole_0=B_256 | ~v1_funct_2('#skF_7', '#skF_5', B_256) | ~r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', B_256)) | r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_206, c_1492])).
% 5.06/1.96  tff(c_1692, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1501])).
% 5.06/1.96  tff(c_52, plain, (![D_64, C_63, B_62, A_61]: (r2_hidden(k1_funct_1(D_64, C_63), B_62) | k1_xboole_0=B_62 | ~r2_hidden(C_63, A_61) | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(D_64, A_61, B_62) | ~v1_funct_1(D_64))), inference(cnfTransformation, [status(thm)], [f_98])).
% 5.06/1.96  tff(c_1695, plain, (![D_64, B_62]: (r2_hidden(k1_funct_1(D_64, '#skF_2'('#skF_7', '#skF_6')), B_62) | k1_xboole_0=B_62 | ~m1_subset_1(D_64, k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_62))) | ~v1_funct_2(D_64, '#skF_5', B_62) | ~v1_funct_1(D_64))), inference(resolution, [status(thm)], [c_1692, c_52])).
% 5.06/1.96  tff(c_1971, plain, (![B_62]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), B_62) | k1_xboole_0=B_62 | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_62))) | ~v1_funct_2('#skF_7', '#skF_5', B_62) | ~v1_funct_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1960, c_1695])).
% 5.06/1.96  tff(c_2058, plain, (![B_328]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), B_328) | k1_xboole_0=B_328 | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', B_328))) | ~v1_funct_2('#skF_7', '#skF_5', B_328))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_1971])).
% 5.06/1.96  tff(c_2064, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_xboole_0='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_2058])).
% 5.06/1.96  tff(c_2068, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6') | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2064])).
% 5.06/1.96  tff(c_2069, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_2068])).
% 5.06/1.96  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.06/1.96  tff(c_2122, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2069, c_8])).
% 5.06/1.96  tff(c_243, plain, (![A_111, B_112, C_113]: (m1_subset_1(k2_relset_1(A_111, B_112, C_113), k1_zfmisc_1(B_112)) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.06/1.96  tff(c_267, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_205, c_243])).
% 5.06/1.96  tff(c_273, plain, (m1_subset_1(k2_relat_1('#skF_7'), k1_zfmisc_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_267])).
% 5.06/1.96  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.06/1.96  tff(c_277, plain, (r1_tarski(k2_relat_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_273, c_10])).
% 5.06/1.96  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.06/1.96  tff(c_290, plain, (k2_relat_1('#skF_7')='#skF_6' | ~r1_tarski('#skF_6', k2_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_277, c_2])).
% 5.06/1.96  tff(c_293, plain, (~r1_tarski('#skF_6', k2_relat_1('#skF_7'))), inference(negUnitSimplification, [status(thm)], [c_206, c_290])).
% 5.06/1.96  tff(c_2148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2122, c_293])).
% 5.06/1.96  tff(c_2150, plain, (k1_xboole_0!='#skF_6'), inference(splitRight, [status(thm)], [c_2068])).
% 5.06/1.96  tff(c_68, plain, (![A_72, B_73]: (r1_tarski(A_72, B_73) | ~m1_subset_1(A_72, k1_zfmisc_1(B_73)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.06/1.96  tff(c_72, plain, (r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_56, c_68])).
% 5.06/1.96  tff(c_2065, plain, (![B_328]: (r2_hidden('#skF_1'('#skF_7', '#skF_6'), B_328) | k1_xboole_0=B_328 | ~v1_funct_2('#skF_7', '#skF_5', B_328) | ~r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', B_328)))), inference(resolution, [status(thm)], [c_12, c_2058])).
% 5.06/1.96  tff(c_26, plain, (![A_6, B_28]: (~r2_hidden('#skF_1'(A_6, B_28), B_28) | r2_hidden('#skF_3'(A_6, B_28), B_28) | k2_relat_1(A_6)=B_28 | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_301, plain, (![A_118, D_119]: (r2_hidden(k1_funct_1(A_118, D_119), k2_relat_1(A_118)) | ~r2_hidden(D_119, k1_relat_1(A_118)) | ~v1_funct_1(A_118) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_304, plain, (![D_68]: (r2_hidden(D_68, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_301])).
% 5.06/1.96  tff(c_306, plain, (![D_68]: (r2_hidden(D_68, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | ~r2_hidden(D_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_304])).
% 5.06/1.96  tff(c_741, plain, (![D_162]: (r2_hidden(D_162, k2_relat_1('#skF_7')) | ~r2_hidden('#skF_8'(D_162), '#skF_5') | ~r2_hidden(D_162, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_725, c_306])).
% 5.06/1.96  tff(c_745, plain, (![D_68]: (r2_hidden(D_68, k2_relat_1('#skF_7')) | ~r2_hidden(D_68, '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_741])).
% 5.06/1.96  tff(c_16, plain, (![A_6, C_42]: (k1_funct_1(A_6, '#skF_4'(A_6, k2_relat_1(A_6), C_42))=C_42 | ~r2_hidden(C_42, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_18, plain, (![A_6, C_42]: (r2_hidden('#skF_4'(A_6, k2_relat_1(A_6), C_42), k1_relat_1(A_6)) | ~r2_hidden(C_42, k2_relat_1(A_6)) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_731, plain, (![C_42]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_42), '#skF_5') | ~r2_hidden(C_42, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_725, c_18])).
% 5.06/1.96  tff(c_735, plain, (![C_42]: (r2_hidden('#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_42), '#skF_5') | ~r2_hidden(C_42, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_731])).
% 5.06/1.96  tff(c_2149, plain, (r2_hidden('#skF_1'('#skF_7', '#skF_6'), '#skF_6')), inference(splitRight, [status(thm)], [c_2068])).
% 5.06/1.96  tff(c_20, plain, (![A_6, B_28, D_41]: (~r2_hidden('#skF_1'(A_6, B_28), B_28) | k1_funct_1(A_6, D_41)!='#skF_3'(A_6, B_28) | ~r2_hidden(D_41, k1_relat_1(A_6)) | k2_relat_1(A_6)=B_28 | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_2175, plain, (![D_41]: (k1_funct_1('#skF_7', D_41)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_41, k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(resolution, [status(thm)], [c_2149, c_20])).
% 5.06/1.96  tff(c_2181, plain, (![D_41]: (k1_funct_1('#skF_7', D_41)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_41, '#skF_5') | k2_relat_1('#skF_7')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_725, c_2175])).
% 5.06/1.96  tff(c_2184, plain, (![D_335]: (k1_funct_1('#skF_7', D_335)!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_335, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_206, c_2181])).
% 5.06/1.96  tff(c_2279, plain, (![C_338]: (k1_funct_1('#skF_7', '#skF_4'('#skF_7', k2_relat_1('#skF_7'), C_338))!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_338, k2_relat_1('#skF_7')))), inference(resolution, [status(thm)], [c_735, c_2184])).
% 5.06/1.96  tff(c_2283, plain, (![C_42]: (C_42!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_42, k2_relat_1('#skF_7')) | ~r2_hidden(C_42, k2_relat_1('#skF_7')) | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2279])).
% 5.06/1.96  tff(c_2303, plain, (![C_342]: (C_342!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(C_342, k2_relat_1('#skF_7')))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_2283])).
% 5.06/1.96  tff(c_2356, plain, (![D_343]: (D_343!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden(D_343, '#skF_6'))), inference(resolution, [status(thm)], [c_745, c_2303])).
% 5.06/1.96  tff(c_2453, plain, (![A_346]: ('#skF_3'(A_346, '#skF_6')!='#skF_3'('#skF_7', '#skF_6') | ~r2_hidden('#skF_1'(A_346, '#skF_6'), '#skF_6') | k2_relat_1(A_346)='#skF_6' | ~v1_funct_1(A_346) | ~v1_relat_1(A_346))), inference(resolution, [status(thm)], [c_26, c_2356])).
% 5.06/1.96  tff(c_2457, plain, (k2_relat_1('#skF_7')='#skF_6' | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | k1_xboole_0='#skF_6' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_6') | ~r1_tarski('#skF_7', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2065, c_2453])).
% 5.06/1.96  tff(c_2463, plain, (k2_relat_1('#skF_7')='#skF_6' | k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_58, c_97, c_60, c_2457])).
% 5.06/1.96  tff(c_2465, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2150, c_206, c_2463])).
% 5.06/1.96  tff(c_2467, plain, (~r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_1501])).
% 5.06/1.96  tff(c_1368, plain, (![A_240, B_241, D_242]: (r2_hidden('#skF_2'(A_240, B_241), k1_relat_1(A_240)) | k1_funct_1(A_240, D_242)!='#skF_3'(A_240, B_241) | ~r2_hidden(D_242, k1_relat_1(A_240)) | k2_relat_1(A_240)=B_241 | ~v1_funct_1(A_240) | ~v1_relat_1(A_240))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.06/1.96  tff(c_1374, plain, (![B_241, D_68]: (r2_hidden('#skF_2'('#skF_7', B_241), k1_relat_1('#skF_7')) | D_68!='#skF_3'('#skF_7', B_241) | ~r2_hidden('#skF_8'(D_68), k1_relat_1('#skF_7')) | k2_relat_1('#skF_7')=B_241 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(D_68, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_62, c_1368])).
% 5.06/1.96  tff(c_1376, plain, (![B_241, D_68]: (r2_hidden('#skF_2'('#skF_7', B_241), '#skF_5') | D_68!='#skF_3'('#skF_7', B_241) | ~r2_hidden('#skF_8'(D_68), '#skF_5') | k2_relat_1('#skF_7')=B_241 | ~r2_hidden(D_68, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_60, c_725, c_725, c_1374])).
% 5.06/1.96  tff(c_2545, plain, (![B_358]: (r2_hidden('#skF_2'('#skF_7', B_358), '#skF_5') | ~r2_hidden('#skF_8'('#skF_3'('#skF_7', B_358)), '#skF_5') | k2_relat_1('#skF_7')=B_358 | ~r2_hidden('#skF_3'('#skF_7', B_358), '#skF_6'))), inference(reflexivity, [status(thm), theory('equality')], [c_1376])).
% 5.06/1.96  tff(c_2550, plain, (![B_359]: (r2_hidden('#skF_2'('#skF_7', B_359), '#skF_5') | k2_relat_1('#skF_7')=B_359 | ~r2_hidden('#skF_3'('#skF_7', B_359), '#skF_6'))), inference(resolution, [status(thm)], [c_64, c_2545])).
% 5.06/1.96  tff(c_2562, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_5') | k2_relat_1('#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_842, c_2550])).
% 5.06/1.96  tff(c_2580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_206, c_2467, c_206, c_2467, c_2562])).
% 5.06/1.96  tff(c_2581, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_724])).
% 5.06/1.96  tff(c_2603, plain, (![A_3]: (r1_tarski('#skF_6', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_2581, c_8])).
% 5.06/1.96  tff(c_2611, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2603, c_293])).
% 5.06/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.06/1.96  
% 5.06/1.96  Inference rules
% 5.06/1.96  ----------------------
% 5.06/1.96  #Ref     : 2
% 5.06/1.96  #Sup     : 487
% 5.06/1.96  #Fact    : 0
% 5.06/1.96  #Define  : 0
% 5.06/1.96  #Split   : 8
% 5.06/1.96  #Chain   : 0
% 5.06/1.96  #Close   : 0
% 5.06/1.96  
% 5.06/1.96  Ordering : KBO
% 5.06/1.96  
% 5.06/1.96  Simplification rules
% 5.06/1.96  ----------------------
% 5.06/1.96  #Subsume      : 48
% 5.06/1.96  #Demod        : 534
% 5.06/1.96  #Tautology    : 177
% 5.06/1.96  #SimpNegUnit  : 35
% 5.06/1.96  #BackRed      : 85
% 5.06/1.96  
% 5.06/1.96  #Partial instantiations: 0
% 5.06/1.96  #Strategies tried      : 1
% 5.06/1.96  
% 5.06/1.96  Timing (in seconds)
% 5.06/1.96  ----------------------
% 5.06/1.96  Preprocessing        : 0.35
% 5.06/1.96  Parsing              : 0.17
% 5.06/1.96  CNF conversion       : 0.03
% 5.06/1.96  Main loop            : 0.80
% 5.06/1.96  Inferencing          : 0.27
% 5.06/1.96  Reduction            : 0.27
% 5.06/1.96  Demodulation         : 0.19
% 5.06/1.96  BG Simplification    : 0.04
% 5.06/1.96  Subsumption          : 0.16
% 5.06/1.96  Abstraction          : 0.05
% 5.06/1.96  MUC search           : 0.00
% 5.06/1.96  Cooper               : 0.00
% 5.06/1.96  Total                : 1.19
% 5.06/1.96  Index Insertion      : 0.00
% 5.06/1.96  Index Deletion       : 0.00
% 5.06/1.96  Index Matching       : 0.00
% 5.06/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
