%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:36 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.97s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 434 expanded)
%              Number of leaves         :   37 ( 159 expanded)
%              Depth                    :   10
%              Number of atoms          :  292 (1262 expanded)
%              Number of equality atoms :   28 ( 159 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_151,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_132,axiom,(
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

tff(f_84,axiom,(
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

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(c_20,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_56,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_101,plain,(
    ! [B_153,A_154] :
      ( v1_relat_1(B_153)
      | ~ m1_subset_1(B_153,k1_zfmisc_1(A_154))
      | ~ v1_relat_1(A_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_112,plain,
    ( v1_relat_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_56,c_101])).

tff(c_117,plain,(
    v1_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_112])).

tff(c_60,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( m1_subset_1(B_6,A_5)
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( r2_hidden(B_6,A_5)
      | ~ m1_subset_1(B_6,A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,(
    ! [F_157] :
      ( k1_funct_1('#skF_7',F_157) != '#skF_8'
      | ~ r2_hidden(F_157,'#skF_6')
      | ~ m1_subset_1(F_157,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_137,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ m1_subset_1(B_6,'#skF_4')
      | ~ m1_subset_1(B_6,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_260,plain,(
    ! [B_182] :
      ( k1_funct_1('#skF_7',B_182) != '#skF_8'
      | ~ m1_subset_1(B_182,'#skF_4')
      | ~ m1_subset_1(B_182,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_269,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ m1_subset_1(B_6,'#skF_4')
      | ~ v1_xboole_0(B_6)
      | ~ v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_10,c_260])).

tff(c_271,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_284,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k7_relset_1(A_189,B_190,C_191,D_192) = k9_relat_1(C_191,D_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_295,plain,(
    ! [D_192] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_192) = k9_relat_1('#skF_7',D_192) ),
    inference(resolution,[status(thm)],[c_56,c_284])).

tff(c_54,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_298,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_54])).

tff(c_383,plain,(
    ! [A_206,B_207,C_208,D_209] :
      ( m1_subset_1(k7_relset_1(A_206,B_207,C_208,D_209),k1_zfmisc_1(B_207))
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_405,plain,(
    ! [D_192] :
      ( m1_subset_1(k9_relat_1('#skF_7',D_192),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_383])).

tff(c_414,plain,(
    ! [D_210] : m1_subset_1(k9_relat_1('#skF_7',D_210),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_405])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_433,plain,(
    ! [A_213,D_214] :
      ( m1_subset_1(A_213,'#skF_5')
      | ~ r2_hidden(A_213,k9_relat_1('#skF_7',D_214)) ) ),
    inference(resolution,[status(thm)],[c_414,c_16])).

tff(c_449,plain,(
    m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_298,c_433])).

tff(c_157,plain,(
    ! [C_163,B_164,A_165] :
      ( v1_xboole_0(C_163)
      | ~ m1_subset_1(C_163,k1_zfmisc_1(k2_zfmisc_1(B_164,A_165)))
      | ~ v1_xboole_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_171,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_157])).

tff(c_172,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_171])).

tff(c_141,plain,(
    ! [C_160,A_161,B_162] :
      ( v1_xboole_0(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162)))
      | ~ v1_xboole_0(A_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_155,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_56,c_141])).

tff(c_156,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_1002,plain,(
    ! [A_285,E_283,D_286,C_287,B_284] :
      ( r2_hidden('#skF_3'(E_283,B_284,A_285,D_286,C_287),B_284)
      | ~ r2_hidden(E_283,k7_relset_1(C_287,A_285,D_286,B_284))
      | ~ m1_subset_1(E_283,A_285)
      | ~ m1_subset_1(D_286,k1_zfmisc_1(k2_zfmisc_1(C_287,A_285)))
      | v1_xboole_0(C_287)
      | v1_xboole_0(B_284)
      | v1_xboole_0(A_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1016,plain,(
    ! [E_283,B_284] :
      ( r2_hidden('#skF_3'(E_283,B_284,'#skF_5','#skF_7','#skF_4'),B_284)
      | ~ r2_hidden(E_283,k7_relset_1('#skF_4','#skF_5','#skF_7',B_284))
      | ~ m1_subset_1(E_283,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_284)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1002])).

tff(c_1022,plain,(
    ! [E_283,B_284] :
      ( r2_hidden('#skF_3'(E_283,B_284,'#skF_5','#skF_7','#skF_4'),B_284)
      | ~ r2_hidden(E_283,k9_relat_1('#skF_7',B_284))
      | ~ m1_subset_1(E_283,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_284)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_1016])).

tff(c_2103,plain,(
    ! [E_427,B_428] :
      ( r2_hidden('#skF_3'(E_427,B_428,'#skF_5','#skF_7','#skF_4'),B_428)
      | ~ r2_hidden(E_427,k9_relat_1('#skF_7',B_428))
      | ~ m1_subset_1(E_427,'#skF_5')
      | v1_xboole_0(B_428) ) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_156,c_1022])).

tff(c_52,plain,(
    ! [F_140] :
      ( k1_funct_1('#skF_7',F_140) != '#skF_8'
      | ~ r2_hidden(F_140,'#skF_6')
      | ~ m1_subset_1(F_140,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_2199,plain,(
    ! [E_427] :
      ( k1_funct_1('#skF_7','#skF_3'(E_427,'#skF_6','#skF_5','#skF_7','#skF_4')) != '#skF_8'
      | ~ m1_subset_1('#skF_3'(E_427,'#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4')
      | ~ r2_hidden(E_427,k9_relat_1('#skF_7','#skF_6'))
      | ~ m1_subset_1(E_427,'#skF_5')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_2103,c_52])).

tff(c_2380,plain,(
    ! [E_451] :
      ( k1_funct_1('#skF_7','#skF_3'(E_451,'#skF_6','#skF_5','#skF_7','#skF_4')) != '#skF_8'
      | ~ m1_subset_1('#skF_3'(E_451,'#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4')
      | ~ r2_hidden(E_451,k9_relat_1('#skF_7','#skF_6'))
      | ~ m1_subset_1(E_451,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_2199])).

tff(c_2399,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_298,c_2380])).

tff(c_2420,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_2399])).

tff(c_2428,plain,(
    ~ m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2420])).

tff(c_1276,plain,(
    ! [A_315,E_313,D_316,C_317,B_314] :
      ( m1_subset_1('#skF_3'(E_313,B_314,A_315,D_316,C_317),C_317)
      | ~ r2_hidden(E_313,k7_relset_1(C_317,A_315,D_316,B_314))
      | ~ m1_subset_1(E_313,A_315)
      | ~ m1_subset_1(D_316,k1_zfmisc_1(k2_zfmisc_1(C_317,A_315)))
      | v1_xboole_0(C_317)
      | v1_xboole_0(B_314)
      | v1_xboole_0(A_315) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1284,plain,(
    ! [E_313,D_192] :
      ( m1_subset_1('#skF_3'(E_313,D_192,'#skF_5','#skF_7','#skF_4'),'#skF_4')
      | ~ r2_hidden(E_313,k9_relat_1('#skF_7',D_192))
      | ~ m1_subset_1(E_313,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_192)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_1276])).

tff(c_1297,plain,(
    ! [E_313,D_192] :
      ( m1_subset_1('#skF_3'(E_313,D_192,'#skF_5','#skF_7','#skF_4'),'#skF_4')
      | ~ r2_hidden(E_313,k9_relat_1('#skF_7',D_192))
      | ~ m1_subset_1(E_313,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_192)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1284])).

tff(c_2433,plain,(
    ! [E_452,D_453] :
      ( m1_subset_1('#skF_3'(E_452,D_453,'#skF_5','#skF_7','#skF_4'),'#skF_4')
      | ~ r2_hidden(E_452,k9_relat_1('#skF_7',D_453))
      | ~ m1_subset_1(E_452,'#skF_5')
      | v1_xboole_0(D_453) ) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_156,c_1297])).

tff(c_2456,plain,
    ( m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_298,c_2433])).

tff(c_2479,plain,
    ( m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_2456])).

tff(c_2481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_2428,c_2479])).

tff(c_2482,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2420])).

tff(c_1414,plain,(
    ! [D_346,B_344,A_345,E_343,C_347] :
      ( r2_hidden(k4_tarski('#skF_3'(E_343,B_344,A_345,D_346,C_347),E_343),D_346)
      | ~ r2_hidden(E_343,k7_relset_1(C_347,A_345,D_346,B_344))
      | ~ m1_subset_1(E_343,A_345)
      | ~ m1_subset_1(D_346,k1_zfmisc_1(k2_zfmisc_1(C_347,A_345)))
      | v1_xboole_0(C_347)
      | v1_xboole_0(B_344)
      | v1_xboole_0(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5843,plain,(
    ! [E_674,D_677,C_675,B_676,A_673] :
      ( k1_funct_1(D_677,'#skF_3'(E_674,B_676,A_673,D_677,C_675)) = E_674
      | ~ v1_funct_1(D_677)
      | ~ v1_relat_1(D_677)
      | ~ r2_hidden(E_674,k7_relset_1(C_675,A_673,D_677,B_676))
      | ~ m1_subset_1(E_674,A_673)
      | ~ m1_subset_1(D_677,k1_zfmisc_1(k2_zfmisc_1(C_675,A_673)))
      | v1_xboole_0(C_675)
      | v1_xboole_0(B_676)
      | v1_xboole_0(A_673) ) ),
    inference(resolution,[status(thm)],[c_1414,c_32])).

tff(c_5857,plain,(
    ! [E_674,D_192] :
      ( k1_funct_1('#skF_7','#skF_3'(E_674,D_192,'#skF_5','#skF_7','#skF_4')) = E_674
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(E_674,k9_relat_1('#skF_7',D_192))
      | ~ m1_subset_1(E_674,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_192)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_5843])).

tff(c_5872,plain,(
    ! [E_674,D_192] :
      ( k1_funct_1('#skF_7','#skF_3'(E_674,D_192,'#skF_5','#skF_7','#skF_4')) = E_674
      | ~ r2_hidden(E_674,k9_relat_1('#skF_7',D_192))
      | ~ m1_subset_1(E_674,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_192)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117,c_60,c_5857])).

tff(c_5877,plain,(
    ! [E_678,D_679] :
      ( k1_funct_1('#skF_7','#skF_3'(E_678,D_679,'#skF_5','#skF_7','#skF_4')) = E_678
      | ~ r2_hidden(E_678,k9_relat_1('#skF_7',D_679))
      | ~ m1_subset_1(E_678,'#skF_5')
      | v1_xboole_0(D_679) ) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_156,c_5872])).

tff(c_5926,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) = '#skF_8'
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_298,c_5877])).

tff(c_5974,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) = '#skF_8'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_449,c_5926])).

tff(c_5976,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_271,c_2482,c_5974])).

tff(c_5978,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_207,plain,(
    ! [A_172,B_173,C_174] :
      ( r2_hidden('#skF_2'(A_172,B_173,C_174),B_173)
      | ~ r2_hidden(A_172,k9_relat_1(C_174,B_173))
      | ~ v1_relat_1(C_174) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_226,plain,(
    ! [B_175,A_176,C_177] :
      ( ~ v1_xboole_0(B_175)
      | ~ r2_hidden(A_176,k9_relat_1(C_177,B_175))
      | ~ v1_relat_1(C_177) ) ),
    inference(resolution,[status(thm)],[c_207,c_2])).

tff(c_241,plain,(
    ! [B_175,C_177] :
      ( ~ v1_xboole_0(B_175)
      | ~ v1_relat_1(C_177)
      | v1_xboole_0(k9_relat_1(C_177,B_175)) ) ),
    inference(resolution,[status(thm)],[c_4,c_226])).

tff(c_6103,plain,(
    ! [A_709,B_710,C_711,D_712] :
      ( k7_relset_1(A_709,B_710,C_711,D_712) = k9_relat_1(C_711,D_712)
      | ~ m1_subset_1(C_711,k1_zfmisc_1(k2_zfmisc_1(A_709,B_710))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6122,plain,(
    ! [D_712] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_712) = k9_relat_1('#skF_7',D_712) ),
    inference(resolution,[status(thm)],[c_56,c_6103])).

tff(c_82,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_6133,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6122,c_82])).

tff(c_6151,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_241,c_6133])).

tff(c_6155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_5978,c_6151])).

tff(c_6156,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_6378,plain,(
    ! [A_767,B_768,C_769,D_770] :
      ( k7_relset_1(A_767,B_768,C_769,D_770) = k9_relat_1(C_769,D_770)
      | ~ m1_subset_1(C_769,k1_zfmisc_1(k2_zfmisc_1(A_767,B_768))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6397,plain,(
    ! [D_770] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_770) = k9_relat_1('#skF_7',D_770) ),
    inference(resolution,[status(thm)],[c_56,c_6378])).

tff(c_6400,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6397,c_54])).

tff(c_6569,plain,(
    ! [A_777,B_778,C_779] :
      ( r2_hidden(k4_tarski('#skF_2'(A_777,B_778,C_779),A_777),C_779)
      | ~ r2_hidden(A_777,k9_relat_1(C_779,B_778))
      | ~ v1_relat_1(C_779) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6625,plain,(
    ! [C_780,A_781,B_782] :
      ( ~ v1_xboole_0(C_780)
      | ~ r2_hidden(A_781,k9_relat_1(C_780,B_782))
      | ~ v1_relat_1(C_780) ) ),
    inference(resolution,[status(thm)],[c_6569,c_2])).

tff(c_6636,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6400,c_6625])).

tff(c_6654,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_6156,c_6636])).

tff(c_6655,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_7005,plain,(
    ! [A_841,C_842] :
      ( r2_hidden(k4_tarski(A_841,k1_funct_1(C_842,A_841)),C_842)
      | ~ r2_hidden(A_841,k1_relat_1(C_842))
      | ~ v1_funct_1(C_842)
      | ~ v1_relat_1(C_842) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7092,plain,(
    ! [C_848,A_849] :
      ( ~ v1_xboole_0(C_848)
      | ~ r2_hidden(A_849,k1_relat_1(C_848))
      | ~ v1_funct_1(C_848)
      | ~ v1_relat_1(C_848) ) ),
    inference(resolution,[status(thm)],[c_7005,c_2])).

tff(c_7117,plain,(
    ! [C_850] :
      ( ~ v1_xboole_0(C_850)
      | ~ v1_funct_1(C_850)
      | ~ v1_relat_1(C_850)
      | v1_xboole_0(k1_relat_1(C_850)) ) ),
    inference(resolution,[status(thm)],[c_4,c_7092])).

tff(c_6869,plain,(
    ! [A_828,B_829,C_830,D_831] :
      ( k7_relset_1(A_828,B_829,C_830,D_831) = k9_relat_1(C_830,D_831)
      | ~ m1_subset_1(C_830,k1_zfmisc_1(k2_zfmisc_1(A_828,B_829))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6888,plain,(
    ! [D_831] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_831) = k9_relat_1('#skF_7',D_831) ),
    inference(resolution,[status(thm)],[c_56,c_6869])).

tff(c_6891,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6888,c_54])).

tff(c_6954,plain,(
    ! [A_834,B_835,C_836] :
      ( r2_hidden('#skF_2'(A_834,B_835,C_836),k1_relat_1(C_836))
      | ~ r2_hidden(A_834,k9_relat_1(C_836,B_835))
      | ~ v1_relat_1(C_836) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7057,plain,(
    ! [C_843,A_844,B_845] :
      ( ~ v1_xboole_0(k1_relat_1(C_843))
      | ~ r2_hidden(A_844,k9_relat_1(C_843,B_845))
      | ~ v1_relat_1(C_843) ) ),
    inference(resolution,[status(thm)],[c_6954,c_2])).

tff(c_7064,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6891,c_7057])).

tff(c_7080,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_7064])).

tff(c_7120,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7117,c_7080])).

tff(c_7124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_60,c_6655,c_7120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:34:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.86  
% 7.69/2.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.87  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 7.69/2.87  
% 7.69/2.87  %Foreground sorts:
% 7.69/2.87  
% 7.69/2.87  
% 7.69/2.87  %Background operators:
% 7.69/2.87  
% 7.69/2.87  
% 7.69/2.87  %Foreground operators:
% 7.69/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.69/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.69/2.87  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.69/2.87  tff('#skF_1', type, '#skF_1': $i > $i).
% 7.69/2.87  tff('#skF_7', type, '#skF_7': $i).
% 7.69/2.87  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 7.69/2.87  tff('#skF_5', type, '#skF_5': $i).
% 7.69/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.69/2.87  tff('#skF_6', type, '#skF_6': $i).
% 7.69/2.87  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.69/2.87  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.69/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.69/2.87  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.69/2.87  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 7.69/2.87  tff('#skF_8', type, '#skF_8': $i).
% 7.69/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.69/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.69/2.87  tff('#skF_4', type, '#skF_4': $i).
% 7.69/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.69/2.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.69/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.69/2.87  
% 7.97/2.91  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.97/2.91  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: (m1_subset_1(F, A) => ~(r2_hidden(F, C) & (E = k1_funct_1(D, F))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t116_funct_2)).
% 7.97/2.91  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.97/2.91  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 7.97/2.91  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 7.97/2.91  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 7.97/2.91  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 7.97/2.91  tff(f_98, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.97/2.91  tff(f_91, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc3_relset_1)).
% 7.97/2.91  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_relset_1)).
% 7.97/2.91  tff(f_84, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_1)).
% 7.97/2.91  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 7.97/2.91  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 7.97/2.91  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.97/2.91  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.97/2.91  tff(c_101, plain, (![B_153, A_154]: (v1_relat_1(B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(A_154)) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.97/2.91  tff(c_112, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_101])).
% 7.97/2.91  tff(c_117, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_112])).
% 7.97/2.91  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.97/2.91  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.97/2.91  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.97/2.91  tff(c_128, plain, (![F_157]: (k1_funct_1('#skF_7', F_157)!='#skF_8' | ~r2_hidden(F_157, '#skF_6') | ~m1_subset_1(F_157, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.97/2.91  tff(c_137, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~m1_subset_1(B_6, '#skF_4') | ~m1_subset_1(B_6, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_8, c_128])).
% 7.97/2.91  tff(c_260, plain, (![B_182]: (k1_funct_1('#skF_7', B_182)!='#skF_8' | ~m1_subset_1(B_182, '#skF_4') | ~m1_subset_1(B_182, '#skF_6'))), inference(splitLeft, [status(thm)], [c_137])).
% 7.97/2.91  tff(c_269, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~m1_subset_1(B_6, '#skF_4') | ~v1_xboole_0(B_6) | ~v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_10, c_260])).
% 7.97/2.91  tff(c_271, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_269])).
% 7.97/2.91  tff(c_284, plain, (![A_189, B_190, C_191, D_192]: (k7_relset_1(A_189, B_190, C_191, D_192)=k9_relat_1(C_191, D_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.97/2.91  tff(c_295, plain, (![D_192]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_192)=k9_relat_1('#skF_7', D_192))), inference(resolution, [status(thm)], [c_56, c_284])).
% 7.97/2.91  tff(c_54, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.97/2.91  tff(c_298, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_54])).
% 7.97/2.91  tff(c_383, plain, (![A_206, B_207, C_208, D_209]: (m1_subset_1(k7_relset_1(A_206, B_207, C_208, D_209), k1_zfmisc_1(B_207)) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.97/2.91  tff(c_405, plain, (![D_192]: (m1_subset_1(k9_relat_1('#skF_7', D_192), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_295, c_383])).
% 7.97/2.91  tff(c_414, plain, (![D_210]: (m1_subset_1(k9_relat_1('#skF_7', D_210), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_405])).
% 7.97/2.91  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.97/2.91  tff(c_433, plain, (![A_213, D_214]: (m1_subset_1(A_213, '#skF_5') | ~r2_hidden(A_213, k9_relat_1('#skF_7', D_214)))), inference(resolution, [status(thm)], [c_414, c_16])).
% 7.97/2.91  tff(c_449, plain, (m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_298, c_433])).
% 7.97/2.91  tff(c_157, plain, (![C_163, B_164, A_165]: (v1_xboole_0(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(B_164, A_165))) | ~v1_xboole_0(A_165))), inference(cnfTransformation, [status(thm)], [f_98])).
% 7.97/2.91  tff(c_171, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_157])).
% 7.97/2.91  tff(c_172, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_171])).
% 7.97/2.91  tff(c_141, plain, (![C_160, A_161, B_162]: (v1_xboole_0(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_91])).
% 7.97/2.91  tff(c_155, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_141])).
% 7.97/2.91  tff(c_156, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_155])).
% 7.97/2.91  tff(c_1002, plain, (![A_285, E_283, D_286, C_287, B_284]: (r2_hidden('#skF_3'(E_283, B_284, A_285, D_286, C_287), B_284) | ~r2_hidden(E_283, k7_relset_1(C_287, A_285, D_286, B_284)) | ~m1_subset_1(E_283, A_285) | ~m1_subset_1(D_286, k1_zfmisc_1(k2_zfmisc_1(C_287, A_285))) | v1_xboole_0(C_287) | v1_xboole_0(B_284) | v1_xboole_0(A_285))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.97/2.91  tff(c_1016, plain, (![E_283, B_284]: (r2_hidden('#skF_3'(E_283, B_284, '#skF_5', '#skF_7', '#skF_4'), B_284) | ~r2_hidden(E_283, k7_relset_1('#skF_4', '#skF_5', '#skF_7', B_284)) | ~m1_subset_1(E_283, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_284) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1002])).
% 7.97/2.91  tff(c_1022, plain, (![E_283, B_284]: (r2_hidden('#skF_3'(E_283, B_284, '#skF_5', '#skF_7', '#skF_4'), B_284) | ~r2_hidden(E_283, k9_relat_1('#skF_7', B_284)) | ~m1_subset_1(E_283, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_284) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_295, c_1016])).
% 7.97/2.91  tff(c_2103, plain, (![E_427, B_428]: (r2_hidden('#skF_3'(E_427, B_428, '#skF_5', '#skF_7', '#skF_4'), B_428) | ~r2_hidden(E_427, k9_relat_1('#skF_7', B_428)) | ~m1_subset_1(E_427, '#skF_5') | v1_xboole_0(B_428))), inference(negUnitSimplification, [status(thm)], [c_172, c_156, c_1022])).
% 7.97/2.91  tff(c_52, plain, (![F_140]: (k1_funct_1('#skF_7', F_140)!='#skF_8' | ~r2_hidden(F_140, '#skF_6') | ~m1_subset_1(F_140, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 7.97/2.91  tff(c_2199, plain, (![E_427]: (k1_funct_1('#skF_7', '#skF_3'(E_427, '#skF_6', '#skF_5', '#skF_7', '#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_3'(E_427, '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~r2_hidden(E_427, k9_relat_1('#skF_7', '#skF_6')) | ~m1_subset_1(E_427, '#skF_5') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_2103, c_52])).
% 7.97/2.91  tff(c_2380, plain, (![E_451]: (k1_funct_1('#skF_7', '#skF_3'(E_451, '#skF_6', '#skF_5', '#skF_7', '#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_3'(E_451, '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~r2_hidden(E_451, k9_relat_1('#skF_7', '#skF_6')) | ~m1_subset_1(E_451, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_271, c_2199])).
% 7.97/2.91  tff(c_2399, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_298, c_2380])).
% 7.97/2.91  tff(c_2420, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_449, c_2399])).
% 7.97/2.91  tff(c_2428, plain, (~m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_2420])).
% 7.97/2.91  tff(c_1276, plain, (![A_315, E_313, D_316, C_317, B_314]: (m1_subset_1('#skF_3'(E_313, B_314, A_315, D_316, C_317), C_317) | ~r2_hidden(E_313, k7_relset_1(C_317, A_315, D_316, B_314)) | ~m1_subset_1(E_313, A_315) | ~m1_subset_1(D_316, k1_zfmisc_1(k2_zfmisc_1(C_317, A_315))) | v1_xboole_0(C_317) | v1_xboole_0(B_314) | v1_xboole_0(A_315))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.97/2.91  tff(c_1284, plain, (![E_313, D_192]: (m1_subset_1('#skF_3'(E_313, D_192, '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~r2_hidden(E_313, k9_relat_1('#skF_7', D_192)) | ~m1_subset_1(E_313, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_192) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_1276])).
% 7.97/2.91  tff(c_1297, plain, (![E_313, D_192]: (m1_subset_1('#skF_3'(E_313, D_192, '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~r2_hidden(E_313, k9_relat_1('#skF_7', D_192)) | ~m1_subset_1(E_313, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_192) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1284])).
% 7.97/2.91  tff(c_2433, plain, (![E_452, D_453]: (m1_subset_1('#skF_3'(E_452, D_453, '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~r2_hidden(E_452, k9_relat_1('#skF_7', D_453)) | ~m1_subset_1(E_452, '#skF_5') | v1_xboole_0(D_453))), inference(negUnitSimplification, [status(thm)], [c_172, c_156, c_1297])).
% 7.97/2.91  tff(c_2456, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_298, c_2433])).
% 7.97/2.91  tff(c_2479, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_449, c_2456])).
% 7.97/2.91  tff(c_2481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_2428, c_2479])).
% 7.97/2.91  tff(c_2482, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))!='#skF_8'), inference(splitRight, [status(thm)], [c_2420])).
% 7.97/2.91  tff(c_1414, plain, (![D_346, B_344, A_345, E_343, C_347]: (r2_hidden(k4_tarski('#skF_3'(E_343, B_344, A_345, D_346, C_347), E_343), D_346) | ~r2_hidden(E_343, k7_relset_1(C_347, A_345, D_346, B_344)) | ~m1_subset_1(E_343, A_345) | ~m1_subset_1(D_346, k1_zfmisc_1(k2_zfmisc_1(C_347, A_345))) | v1_xboole_0(C_347) | v1_xboole_0(B_344) | v1_xboole_0(A_345))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.97/2.91  tff(c_32, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.97/2.91  tff(c_5843, plain, (![E_674, D_677, C_675, B_676, A_673]: (k1_funct_1(D_677, '#skF_3'(E_674, B_676, A_673, D_677, C_675))=E_674 | ~v1_funct_1(D_677) | ~v1_relat_1(D_677) | ~r2_hidden(E_674, k7_relset_1(C_675, A_673, D_677, B_676)) | ~m1_subset_1(E_674, A_673) | ~m1_subset_1(D_677, k1_zfmisc_1(k2_zfmisc_1(C_675, A_673))) | v1_xboole_0(C_675) | v1_xboole_0(B_676) | v1_xboole_0(A_673))), inference(resolution, [status(thm)], [c_1414, c_32])).
% 7.97/2.91  tff(c_5857, plain, (![E_674, D_192]: (k1_funct_1('#skF_7', '#skF_3'(E_674, D_192, '#skF_5', '#skF_7', '#skF_4'))=E_674 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(E_674, k9_relat_1('#skF_7', D_192)) | ~m1_subset_1(E_674, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_192) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_295, c_5843])).
% 7.97/2.91  tff(c_5872, plain, (![E_674, D_192]: (k1_funct_1('#skF_7', '#skF_3'(E_674, D_192, '#skF_5', '#skF_7', '#skF_4'))=E_674 | ~r2_hidden(E_674, k9_relat_1('#skF_7', D_192)) | ~m1_subset_1(E_674, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_192) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117, c_60, c_5857])).
% 7.97/2.91  tff(c_5877, plain, (![E_678, D_679]: (k1_funct_1('#skF_7', '#skF_3'(E_678, D_679, '#skF_5', '#skF_7', '#skF_4'))=E_678 | ~r2_hidden(E_678, k9_relat_1('#skF_7', D_679)) | ~m1_subset_1(E_678, '#skF_5') | v1_xboole_0(D_679))), inference(negUnitSimplification, [status(thm)], [c_172, c_156, c_5872])).
% 7.97/2.91  tff(c_5926, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))='#skF_8' | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_298, c_5877])).
% 7.97/2.91  tff(c_5974, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))='#skF_8' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_449, c_5926])).
% 7.97/2.91  tff(c_5976, plain, $false, inference(negUnitSimplification, [status(thm)], [c_271, c_2482, c_5974])).
% 7.97/2.91  tff(c_5978, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_269])).
% 7.97/2.91  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.97/2.91  tff(c_207, plain, (![A_172, B_173, C_174]: (r2_hidden('#skF_2'(A_172, B_173, C_174), B_173) | ~r2_hidden(A_172, k9_relat_1(C_174, B_173)) | ~v1_relat_1(C_174))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.97/2.91  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.97/2.91  tff(c_226, plain, (![B_175, A_176, C_177]: (~v1_xboole_0(B_175) | ~r2_hidden(A_176, k9_relat_1(C_177, B_175)) | ~v1_relat_1(C_177))), inference(resolution, [status(thm)], [c_207, c_2])).
% 7.97/2.91  tff(c_241, plain, (![B_175, C_177]: (~v1_xboole_0(B_175) | ~v1_relat_1(C_177) | v1_xboole_0(k9_relat_1(C_177, B_175)))), inference(resolution, [status(thm)], [c_4, c_226])).
% 7.97/2.91  tff(c_6103, plain, (![A_709, B_710, C_711, D_712]: (k7_relset_1(A_709, B_710, C_711, D_712)=k9_relat_1(C_711, D_712) | ~m1_subset_1(C_711, k1_zfmisc_1(k2_zfmisc_1(A_709, B_710))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.97/2.91  tff(c_6122, plain, (![D_712]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_712)=k9_relat_1('#skF_7', D_712))), inference(resolution, [status(thm)], [c_56, c_6103])).
% 7.97/2.91  tff(c_82, plain, (~v1_xboole_0(k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_54, c_2])).
% 7.97/2.91  tff(c_6133, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6122, c_82])).
% 7.97/2.91  tff(c_6151, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_241, c_6133])).
% 7.97/2.91  tff(c_6155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_5978, c_6151])).
% 7.97/2.91  tff(c_6156, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_171])).
% 7.97/2.91  tff(c_6378, plain, (![A_767, B_768, C_769, D_770]: (k7_relset_1(A_767, B_768, C_769, D_770)=k9_relat_1(C_769, D_770) | ~m1_subset_1(C_769, k1_zfmisc_1(k2_zfmisc_1(A_767, B_768))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.97/2.91  tff(c_6397, plain, (![D_770]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_770)=k9_relat_1('#skF_7', D_770))), inference(resolution, [status(thm)], [c_56, c_6378])).
% 7.97/2.91  tff(c_6400, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6397, c_54])).
% 7.97/2.91  tff(c_6569, plain, (![A_777, B_778, C_779]: (r2_hidden(k4_tarski('#skF_2'(A_777, B_778, C_779), A_777), C_779) | ~r2_hidden(A_777, k9_relat_1(C_779, B_778)) | ~v1_relat_1(C_779))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.97/2.91  tff(c_6625, plain, (![C_780, A_781, B_782]: (~v1_xboole_0(C_780) | ~r2_hidden(A_781, k9_relat_1(C_780, B_782)) | ~v1_relat_1(C_780))), inference(resolution, [status(thm)], [c_6569, c_2])).
% 7.97/2.91  tff(c_6636, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6400, c_6625])).
% 7.97/2.91  tff(c_6654, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_6156, c_6636])).
% 7.97/2.91  tff(c_6655, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_155])).
% 7.97/2.91  tff(c_7005, plain, (![A_841, C_842]: (r2_hidden(k4_tarski(A_841, k1_funct_1(C_842, A_841)), C_842) | ~r2_hidden(A_841, k1_relat_1(C_842)) | ~v1_funct_1(C_842) | ~v1_relat_1(C_842))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.97/2.91  tff(c_7092, plain, (![C_848, A_849]: (~v1_xboole_0(C_848) | ~r2_hidden(A_849, k1_relat_1(C_848)) | ~v1_funct_1(C_848) | ~v1_relat_1(C_848))), inference(resolution, [status(thm)], [c_7005, c_2])).
% 7.97/2.91  tff(c_7117, plain, (![C_850]: (~v1_xboole_0(C_850) | ~v1_funct_1(C_850) | ~v1_relat_1(C_850) | v1_xboole_0(k1_relat_1(C_850)))), inference(resolution, [status(thm)], [c_4, c_7092])).
% 7.97/2.91  tff(c_6869, plain, (![A_828, B_829, C_830, D_831]: (k7_relset_1(A_828, B_829, C_830, D_831)=k9_relat_1(C_830, D_831) | ~m1_subset_1(C_830, k1_zfmisc_1(k2_zfmisc_1(A_828, B_829))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.97/2.91  tff(c_6888, plain, (![D_831]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_831)=k9_relat_1('#skF_7', D_831))), inference(resolution, [status(thm)], [c_56, c_6869])).
% 7.97/2.91  tff(c_6891, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6888, c_54])).
% 7.97/2.91  tff(c_6954, plain, (![A_834, B_835, C_836]: (r2_hidden('#skF_2'(A_834, B_835, C_836), k1_relat_1(C_836)) | ~r2_hidden(A_834, k9_relat_1(C_836, B_835)) | ~v1_relat_1(C_836))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.97/2.91  tff(c_7057, plain, (![C_843, A_844, B_845]: (~v1_xboole_0(k1_relat_1(C_843)) | ~r2_hidden(A_844, k9_relat_1(C_843, B_845)) | ~v1_relat_1(C_843))), inference(resolution, [status(thm)], [c_6954, c_2])).
% 7.97/2.91  tff(c_7064, plain, (~v1_xboole_0(k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6891, c_7057])).
% 7.97/2.91  tff(c_7080, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_7064])).
% 7.97/2.91  tff(c_7120, plain, (~v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7117, c_7080])).
% 7.97/2.91  tff(c_7124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_60, c_6655, c_7120])).
% 7.97/2.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.97/2.91  
% 7.97/2.91  Inference rules
% 7.97/2.91  ----------------------
% 7.97/2.91  #Ref     : 0
% 7.97/2.91  #Sup     : 1448
% 7.97/2.91  #Fact    : 0
% 7.97/2.91  #Define  : 0
% 7.97/2.91  #Split   : 40
% 7.97/2.91  #Chain   : 0
% 7.97/2.91  #Close   : 0
% 7.97/2.91  
% 7.97/2.91  Ordering : KBO
% 7.97/2.91  
% 7.97/2.91  Simplification rules
% 7.97/2.91  ----------------------
% 7.97/2.91  #Subsume      : 367
% 7.97/2.91  #Demod        : 392
% 7.97/2.91  #Tautology    : 119
% 7.97/2.91  #SimpNegUnit  : 135
% 7.97/2.91  #BackRed      : 12
% 7.97/2.91  
% 7.97/2.91  #Partial instantiations: 0
% 7.97/2.91  #Strategies tried      : 1
% 7.97/2.91  
% 7.97/2.91  Timing (in seconds)
% 7.97/2.91  ----------------------
% 7.97/2.92  Preprocessing        : 0.34
% 7.97/2.92  Parsing              : 0.17
% 7.97/2.92  CNF conversion       : 0.03
% 7.97/2.92  Main loop            : 1.77
% 7.97/2.92  Inferencing          : 0.56
% 7.97/2.92  Reduction            : 0.46
% 7.97/2.92  Demodulation         : 0.31
% 7.97/2.92  BG Simplification    : 0.06
% 7.97/2.92  Subsumption          : 0.55
% 7.97/2.92  Abstraction          : 0.08
% 7.97/2.92  MUC search           : 0.00
% 7.97/2.92  Cooper               : 0.00
% 7.97/2.92  Total                : 2.19
% 7.97/2.92  Index Insertion      : 0.00
% 7.97/2.92  Index Deletion       : 0.00
% 7.97/2.92  Index Matching       : 0.00
% 7.97/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
