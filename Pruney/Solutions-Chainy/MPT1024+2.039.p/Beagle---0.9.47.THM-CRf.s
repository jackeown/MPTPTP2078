%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:27 EST 2020

% Result     : Theorem 7.79s
% Output     : CNFRefutation 8.00s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 458 expanded)
%              Number of leaves         :   38 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  309 (1275 expanded)
%              Number of equality atoms :   29 ( 145 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_151,negated_conjecture,(
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

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k7_relset_1(A,B,C,D),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_98,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(k4_tarski(A,B),C)
      <=> ( r2_hidden(A,k1_relat_1(C))
          & B = k1_funct_1(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

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

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

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
      | ~ r2_hidden(F_157,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_137,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ r2_hidden(B_6,'#skF_4')
      | ~ m1_subset_1(B_6,'#skF_6')
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_250,plain,(
    ! [B_180] :
      ( k1_funct_1('#skF_7',B_180) != '#skF_8'
      | ~ r2_hidden(B_180,'#skF_4')
      | ~ m1_subset_1(B_180,'#skF_6') ) ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_262,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) != '#skF_8'
    | ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_6')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4,c_250])).

tff(c_269,plain,
    ( k1_funct_1('#skF_7','#skF_1'('#skF_4')) != '#skF_8'
    | ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_262])).

tff(c_270,plain,(
    ~ m1_subset_1('#skF_1'('#skF_4'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_274,plain,
    ( ~ v1_xboole_0('#skF_1'('#skF_4'))
    | ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_10,c_270])).

tff(c_275,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_410,plain,(
    ! [A_215,B_216,C_217,D_218] :
      ( k7_relset_1(A_215,B_216,C_217,D_218) = k9_relat_1(C_217,D_218)
      | ~ m1_subset_1(C_217,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_425,plain,(
    ! [D_218] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_218) = k9_relat_1('#skF_7',D_218) ),
    inference(resolution,[status(thm)],[c_56,c_410])).

tff(c_54,plain,(
    r2_hidden('#skF_8',k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_428,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_54])).

tff(c_454,plain,(
    ! [A_220,B_221,C_222,D_223] :
      ( m1_subset_1(k7_relset_1(A_220,B_221,C_222,D_223),k1_zfmisc_1(B_221))
      | ~ m1_subset_1(C_222,k1_zfmisc_1(k2_zfmisc_1(A_220,B_221))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_476,plain,(
    ! [D_218] :
      ( m1_subset_1(k9_relat_1('#skF_7',D_218),k1_zfmisc_1('#skF_5'))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_454])).

tff(c_511,plain,(
    ! [D_224] : m1_subset_1(k9_relat_1('#skF_7',D_224),k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_476])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( m1_subset_1(A_9,C_11)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(C_11))
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_555,plain,(
    ! [A_227,D_228] :
      ( m1_subset_1(A_227,'#skF_5')
      | ~ r2_hidden(A_227,k9_relat_1('#skF_7',D_228)) ) ),
    inference(resolution,[status(thm)],[c_511,c_16])).

tff(c_571,plain,(
    m1_subset_1('#skF_8','#skF_5') ),
    inference(resolution,[status(thm)],[c_428,c_555])).

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

tff(c_1273,plain,(
    ! [D_307,B_305,A_306,C_308,E_304] :
      ( m1_subset_1('#skF_3'(E_304,B_305,A_306,D_307,C_308),C_308)
      | ~ r2_hidden(E_304,k7_relset_1(C_308,A_306,D_307,B_305))
      | ~ m1_subset_1(E_304,A_306)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(C_308,A_306)))
      | v1_xboole_0(C_308)
      | v1_xboole_0(B_305)
      | v1_xboole_0(A_306) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1281,plain,(
    ! [E_304,D_218] :
      ( m1_subset_1('#skF_3'(E_304,D_218,'#skF_5','#skF_7','#skF_4'),'#skF_4')
      | ~ r2_hidden(E_304,k9_relat_1('#skF_7',D_218))
      | ~ m1_subset_1(E_304,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_218)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_1273])).

tff(c_1294,plain,(
    ! [E_304,D_218] :
      ( m1_subset_1('#skF_3'(E_304,D_218,'#skF_5','#skF_7','#skF_4'),'#skF_4')
      | ~ r2_hidden(E_304,k9_relat_1('#skF_7',D_218))
      | ~ m1_subset_1(E_304,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_218)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1281])).

tff(c_2122,plain,(
    ! [E_385,D_386] :
      ( m1_subset_1('#skF_3'(E_385,D_386,'#skF_5','#skF_7','#skF_4'),'#skF_4')
      | ~ r2_hidden(E_385,k9_relat_1('#skF_7',D_386))
      | ~ m1_subset_1(E_385,'#skF_5')
      | v1_xboole_0(D_386) ) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_156,c_1294])).

tff(c_2145,plain,
    ( m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_428,c_2122])).

tff(c_2168,plain,
    ( m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_2145])).

tff(c_2169,plain,(
    m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_2168])).

tff(c_1022,plain,(
    ! [E_274,C_278,B_275,A_276,D_277] :
      ( r2_hidden('#skF_3'(E_274,B_275,A_276,D_277,C_278),B_275)
      | ~ r2_hidden(E_274,k7_relset_1(C_278,A_276,D_277,B_275))
      | ~ m1_subset_1(E_274,A_276)
      | ~ m1_subset_1(D_277,k1_zfmisc_1(k2_zfmisc_1(C_278,A_276)))
      | v1_xboole_0(C_278)
      | v1_xboole_0(B_275)
      | v1_xboole_0(A_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1036,plain,(
    ! [E_274,B_275] :
      ( r2_hidden('#skF_3'(E_274,B_275,'#skF_5','#skF_7','#skF_4'),B_275)
      | ~ r2_hidden(E_274,k7_relset_1('#skF_4','#skF_5','#skF_7',B_275))
      | ~ m1_subset_1(E_274,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_275)
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_56,c_1022])).

tff(c_1042,plain,(
    ! [E_274,B_275] :
      ( r2_hidden('#skF_3'(E_274,B_275,'#skF_5','#skF_7','#skF_4'),B_275)
      | ~ r2_hidden(E_274,k9_relat_1('#skF_7',B_275))
      | ~ m1_subset_1(E_274,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(B_275)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_1036])).

tff(c_1381,plain,(
    ! [E_319,B_320] :
      ( r2_hidden('#skF_3'(E_319,B_320,'#skF_5','#skF_7','#skF_4'),B_320)
      | ~ r2_hidden(E_319,k9_relat_1('#skF_7',B_320))
      | ~ m1_subset_1(E_319,'#skF_5')
      | v1_xboole_0(B_320) ) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_156,c_1042])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2496,plain,(
    ! [E_440,B_441] :
      ( m1_subset_1('#skF_3'(E_440,B_441,'#skF_5','#skF_7','#skF_4'),B_441)
      | ~ r2_hidden(E_440,k9_relat_1('#skF_7',B_441))
      | ~ m1_subset_1(E_440,'#skF_5')
      | v1_xboole_0(B_441) ) ),
    inference(resolution,[status(thm)],[c_1381,c_14])).

tff(c_2513,plain,
    ( m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_6')
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_428,c_2496])).

tff(c_2533,plain,
    ( m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_6')
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_2513])).

tff(c_2534,plain,(
    m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_2533])).

tff(c_258,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ m1_subset_1(B_6,'#skF_6')
      | ~ m1_subset_1(B_6,'#skF_4')
      | v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8,c_250])).

tff(c_266,plain,(
    ! [B_6] :
      ( k1_funct_1('#skF_7',B_6) != '#skF_8'
      | ~ m1_subset_1(B_6,'#skF_6')
      | ~ m1_subset_1(B_6,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_258])).

tff(c_2545,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) != '#skF_8'
    | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2534,c_266])).

tff(c_2551,plain,(
    k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2169,c_2545])).

tff(c_1576,plain,(
    ! [D_339,E_336,C_340,A_338,B_337] :
      ( r2_hidden(k4_tarski('#skF_3'(E_336,B_337,A_338,D_339,C_340),E_336),D_339)
      | ~ r2_hidden(E_336,k7_relset_1(C_340,A_338,D_339,B_337))
      | ~ m1_subset_1(E_336,A_338)
      | ~ m1_subset_1(D_339,k1_zfmisc_1(k2_zfmisc_1(C_340,A_338)))
      | v1_xboole_0(C_340)
      | v1_xboole_0(B_337)
      | v1_xboole_0(A_338) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( k1_funct_1(C_25,A_23) = B_24
      | ~ r2_hidden(k4_tarski(A_23,B_24),C_25)
      | ~ v1_funct_1(C_25)
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5872,plain,(
    ! [E_648,D_649,B_651,A_647,C_650] :
      ( k1_funct_1(D_649,'#skF_3'(E_648,B_651,A_647,D_649,C_650)) = E_648
      | ~ v1_funct_1(D_649)
      | ~ v1_relat_1(D_649)
      | ~ r2_hidden(E_648,k7_relset_1(C_650,A_647,D_649,B_651))
      | ~ m1_subset_1(E_648,A_647)
      | ~ m1_subset_1(D_649,k1_zfmisc_1(k2_zfmisc_1(C_650,A_647)))
      | v1_xboole_0(C_650)
      | v1_xboole_0(B_651)
      | v1_xboole_0(A_647) ) ),
    inference(resolution,[status(thm)],[c_1576,c_32])).

tff(c_5886,plain,(
    ! [E_648,D_218] :
      ( k1_funct_1('#skF_7','#skF_3'(E_648,D_218,'#skF_5','#skF_7','#skF_4')) = E_648
      | ~ v1_funct_1('#skF_7')
      | ~ v1_relat_1('#skF_7')
      | ~ r2_hidden(E_648,k9_relat_1('#skF_7',D_218))
      | ~ m1_subset_1(E_648,'#skF_5')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5')))
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_218)
      | v1_xboole_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_5872])).

tff(c_5901,plain,(
    ! [E_648,D_218] :
      ( k1_funct_1('#skF_7','#skF_3'(E_648,D_218,'#skF_5','#skF_7','#skF_4')) = E_648
      | ~ r2_hidden(E_648,k9_relat_1('#skF_7',D_218))
      | ~ m1_subset_1(E_648,'#skF_5')
      | v1_xboole_0('#skF_4')
      | v1_xboole_0(D_218)
      | v1_xboole_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_117,c_60,c_5886])).

tff(c_5907,plain,(
    ! [E_652,D_653] :
      ( k1_funct_1('#skF_7','#skF_3'(E_652,D_653,'#skF_5','#skF_7','#skF_4')) = E_652
      | ~ r2_hidden(E_652,k9_relat_1('#skF_7',D_653))
      | ~ m1_subset_1(E_652,'#skF_5')
      | v1_xboole_0(D_653) ) ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_156,c_5901])).

tff(c_5959,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) = '#skF_8'
    | ~ m1_subset_1('#skF_8','#skF_5')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_428,c_5907])).

tff(c_6010,plain,
    ( k1_funct_1('#skF_7','#skF_3'('#skF_8','#skF_6','#skF_5','#skF_7','#skF_4')) = '#skF_8'
    | v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_571,c_5959])).

tff(c_6012,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_2551,c_6010])).

tff(c_6014,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_202,plain,(
    ! [A_170,B_171,C_172] :
      ( r2_hidden('#skF_2'(A_170,B_171,C_172),B_171)
      | ~ r2_hidden(A_170,k9_relat_1(C_172,B_171))
      | ~ v1_relat_1(C_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_216,plain,(
    ! [B_173,A_174,C_175] :
      ( ~ v1_xboole_0(B_173)
      | ~ r2_hidden(A_174,k9_relat_1(C_175,B_173))
      | ~ v1_relat_1(C_175) ) ),
    inference(resolution,[status(thm)],[c_202,c_2])).

tff(c_231,plain,(
    ! [B_173,C_175] :
      ( ~ v1_xboole_0(B_173)
      | ~ v1_relat_1(C_175)
      | v1_xboole_0(k9_relat_1(C_175,B_173)) ) ),
    inference(resolution,[status(thm)],[c_4,c_216])).

tff(c_6173,plain,(
    ! [A_688,B_689,C_690,D_691] :
      ( k7_relset_1(A_688,B_689,C_690,D_691) = k9_relat_1(C_690,D_691)
      | ~ m1_subset_1(C_690,k1_zfmisc_1(k2_zfmisc_1(A_688,B_689))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6192,plain,(
    ! [D_691] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_691) = k9_relat_1('#skF_7',D_691) ),
    inference(resolution,[status(thm)],[c_56,c_6173])).

tff(c_82,plain,(
    ~ v1_xboole_0(k7_relset_1('#skF_4','#skF_5','#skF_7','#skF_6')) ),
    inference(resolution,[status(thm)],[c_54,c_2])).

tff(c_6194,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6192,c_82])).

tff(c_6212,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_231,c_6194])).

tff(c_6216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_6014,c_6212])).

tff(c_6217,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_6267,plain,(
    ! [A_711,B_712,C_713,D_714] :
      ( k7_relset_1(A_711,B_712,C_713,D_714) = k9_relat_1(C_713,D_714)
      | ~ m1_subset_1(C_713,k1_zfmisc_1(k2_zfmisc_1(A_711,B_712))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6278,plain,(
    ! [D_714] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_714) = k9_relat_1('#skF_7',D_714) ),
    inference(resolution,[status(thm)],[c_56,c_6267])).

tff(c_6280,plain,(
    ~ v1_xboole_0(k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6278,c_82])).

tff(c_6293,plain,
    ( ~ v1_xboole_0('#skF_6')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_231,c_6280])).

tff(c_6297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_6217,c_6293])).

tff(c_6298,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_171])).

tff(c_6764,plain,(
    ! [A_787,C_788] :
      ( r2_hidden(k4_tarski(A_787,k1_funct_1(C_788,A_787)),C_788)
      | ~ r2_hidden(A_787,k1_relat_1(C_788))
      | ~ v1_funct_1(C_788)
      | ~ v1_relat_1(C_788) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6831,plain,(
    ! [C_789,A_790] :
      ( ~ v1_xboole_0(C_789)
      | ~ r2_hidden(A_790,k1_relat_1(C_789))
      | ~ v1_funct_1(C_789)
      | ~ v1_relat_1(C_789) ) ),
    inference(resolution,[status(thm)],[c_6764,c_2])).

tff(c_6856,plain,(
    ! [C_791] :
      ( ~ v1_xboole_0(C_791)
      | ~ v1_funct_1(C_791)
      | ~ v1_relat_1(C_791)
      | v1_xboole_0(k1_relat_1(C_791)) ) ),
    inference(resolution,[status(thm)],[c_4,c_6831])).

tff(c_6465,plain,(
    ! [A_752,B_753,C_754,D_755] :
      ( k7_relset_1(A_752,B_753,C_754,D_755) = k9_relat_1(C_754,D_755)
      | ~ m1_subset_1(C_754,k1_zfmisc_1(k2_zfmisc_1(A_752,B_753))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6476,plain,(
    ! [D_755] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_755) = k9_relat_1('#skF_7',D_755) ),
    inference(resolution,[status(thm)],[c_56,c_6465])).

tff(c_6479,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6476,c_54])).

tff(c_6653,plain,(
    ! [A_769,B_770,C_771] :
      ( r2_hidden('#skF_2'(A_769,B_770,C_771),k1_relat_1(C_771))
      | ~ r2_hidden(A_769,k9_relat_1(C_771,B_770))
      | ~ v1_relat_1(C_771) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6662,plain,(
    ! [C_772,A_773,B_774] :
      ( ~ v1_xboole_0(k1_relat_1(C_772))
      | ~ r2_hidden(A_773,k9_relat_1(C_772,B_774))
      | ~ v1_relat_1(C_772) ) ),
    inference(resolution,[status(thm)],[c_6653,c_2])).

tff(c_6665,plain,
    ( ~ v1_xboole_0(k1_relat_1('#skF_7'))
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6479,c_6662])).

tff(c_6680,plain,(
    ~ v1_xboole_0(k1_relat_1('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_6665])).

tff(c_6859,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_6856,c_6680])).

tff(c_6863,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_60,c_6298,c_6859])).

tff(c_6864,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_7068,plain,(
    ! [A_837,B_838,C_839,D_840] :
      ( k7_relset_1(A_837,B_838,C_839,D_840) = k9_relat_1(C_839,D_840)
      | ~ m1_subset_1(C_839,k1_zfmisc_1(k2_zfmisc_1(A_837,B_838))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_7087,plain,(
    ! [D_840] : k7_relset_1('#skF_4','#skF_5','#skF_7',D_840) = k9_relat_1('#skF_7',D_840) ),
    inference(resolution,[status(thm)],[c_56,c_7068])).

tff(c_7099,plain,(
    r2_hidden('#skF_8',k9_relat_1('#skF_7','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7087,c_54])).

tff(c_7161,plain,(
    ! [A_846,B_847,C_848] :
      ( r2_hidden(k4_tarski('#skF_2'(A_846,B_847,C_848),A_846),C_848)
      | ~ r2_hidden(A_846,k9_relat_1(C_848,B_847))
      | ~ v1_relat_1(C_848) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7291,plain,(
    ! [C_853,A_854,B_855] :
      ( ~ v1_xboole_0(C_853)
      | ~ r2_hidden(A_854,k9_relat_1(C_853,B_855))
      | ~ v1_relat_1(C_853) ) ),
    inference(resolution,[status(thm)],[c_7161,c_2])).

tff(c_7302,plain,
    ( ~ v1_xboole_0('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_7099,c_7291])).

tff(c_7320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_117,c_6864,c_7302])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n012.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 17:57:37 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.79/2.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.00/2.84  
% 8.00/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.00/2.84  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 8.00/2.84  
% 8.00/2.84  %Foreground sorts:
% 8.00/2.84  
% 8.00/2.84  
% 8.00/2.84  %Background operators:
% 8.00/2.84  
% 8.00/2.84  
% 8.00/2.84  %Foreground operators:
% 8.00/2.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.00/2.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.00/2.84  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.00/2.84  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 8.00/2.84  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.00/2.84  tff('#skF_7', type, '#skF_7': $i).
% 8.00/2.84  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.00/2.84  tff('#skF_5', type, '#skF_5': $i).
% 8.00/2.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.00/2.84  tff('#skF_6', type, '#skF_6': $i).
% 8.00/2.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.00/2.84  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 8.00/2.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.00/2.84  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.00/2.84  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 8.00/2.84  tff('#skF_8', type, '#skF_8': $i).
% 8.00/2.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.00/2.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.00/2.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.00/2.84  tff('#skF_4', type, '#skF_4': $i).
% 8.00/2.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.00/2.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.00/2.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.00/2.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.00/2.84  
% 8.00/2.87  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 8.00/2.87  tff(f_151, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: ~(r2_hidden(E, k7_relset_1(A, B, D, C)) & (![F]: ~((r2_hidden(F, A) & r2_hidden(F, C)) & (E = k1_funct_1(D, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t115_funct_2)).
% 8.00/2.87  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 8.00/2.87  tff(f_44, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 8.00/2.87  tff(f_91, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 8.00/2.87  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 8.00/2.87  tff(f_106, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 8.00/2.87  tff(f_102, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k7_relset_1(A, B, C, D), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relset_1)).
% 8.00/2.87  tff(f_54, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 8.00/2.87  tff(f_98, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 8.00/2.87  tff(f_132, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (![E]: (m1_subset_1(E, A) => (r2_hidden(E, k7_relset_1(C, A, D, B)) <=> (?[F]: ((m1_subset_1(F, C) & r2_hidden(k4_tarski(F, E), D)) & r2_hidden(F, B)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_relset_1)).
% 8.00/2.87  tff(f_48, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 8.00/2.87  tff(f_84, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(k4_tarski(A, B), C) <=> (r2_hidden(A, k1_relat_1(C)) & (B = k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_1)).
% 8.00/2.87  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 8.00/2.87  tff(c_20, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.00/2.87  tff(c_56, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.00/2.87  tff(c_101, plain, (![B_153, A_154]: (v1_relat_1(B_153) | ~m1_subset_1(B_153, k1_zfmisc_1(A_154)) | ~v1_relat_1(A_154))), inference(cnfTransformation, [status(thm)], [f_61])).
% 8.00/2.87  tff(c_112, plain, (v1_relat_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_56, c_101])).
% 8.00/2.87  tff(c_117, plain, (v1_relat_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_20, c_112])).
% 8.00/2.87  tff(c_60, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.00/2.87  tff(c_10, plain, (![B_6, A_5]: (m1_subset_1(B_6, A_5) | ~v1_xboole_0(B_6) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.00/2.87  tff(c_141, plain, (![C_160, A_161, B_162]: (v1_xboole_0(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))) | ~v1_xboole_0(A_161))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.00/2.87  tff(c_155, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_56, c_141])).
% 8.00/2.87  tff(c_156, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_155])).
% 8.00/2.87  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.00/2.87  tff(c_8, plain, (![B_6, A_5]: (r2_hidden(B_6, A_5) | ~m1_subset_1(B_6, A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.00/2.87  tff(c_128, plain, (![F_157]: (k1_funct_1('#skF_7', F_157)!='#skF_8' | ~r2_hidden(F_157, '#skF_6') | ~r2_hidden(F_157, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.00/2.87  tff(c_137, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~r2_hidden(B_6, '#skF_4') | ~m1_subset_1(B_6, '#skF_6') | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_8, c_128])).
% 8.00/2.87  tff(c_250, plain, (![B_180]: (k1_funct_1('#skF_7', B_180)!='#skF_8' | ~r2_hidden(B_180, '#skF_4') | ~m1_subset_1(B_180, '#skF_6'))), inference(splitLeft, [status(thm)], [c_137])).
% 8.00/2.87  tff(c_262, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_1'('#skF_4'), '#skF_6') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4, c_250])).
% 8.00/2.87  tff(c_269, plain, (k1_funct_1('#skF_7', '#skF_1'('#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_1'('#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_156, c_262])).
% 8.00/2.87  tff(c_270, plain, (~m1_subset_1('#skF_1'('#skF_4'), '#skF_6')), inference(splitLeft, [status(thm)], [c_269])).
% 8.00/2.87  tff(c_274, plain, (~v1_xboole_0('#skF_1'('#skF_4')) | ~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_10, c_270])).
% 8.00/2.87  tff(c_275, plain, (~v1_xboole_0('#skF_6')), inference(splitLeft, [status(thm)], [c_274])).
% 8.00/2.87  tff(c_410, plain, (![A_215, B_216, C_217, D_218]: (k7_relset_1(A_215, B_216, C_217, D_218)=k9_relat_1(C_217, D_218) | ~m1_subset_1(C_217, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.00/2.87  tff(c_425, plain, (![D_218]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_218)=k9_relat_1('#skF_7', D_218))), inference(resolution, [status(thm)], [c_56, c_410])).
% 8.00/2.87  tff(c_54, plain, (r2_hidden('#skF_8', k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_151])).
% 8.00/2.87  tff(c_428, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_54])).
% 8.00/2.87  tff(c_454, plain, (![A_220, B_221, C_222, D_223]: (m1_subset_1(k7_relset_1(A_220, B_221, C_222, D_223), k1_zfmisc_1(B_221)) | ~m1_subset_1(C_222, k1_zfmisc_1(k2_zfmisc_1(A_220, B_221))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 8.00/2.87  tff(c_476, plain, (![D_218]: (m1_subset_1(k9_relat_1('#skF_7', D_218), k1_zfmisc_1('#skF_5')) | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))))), inference(superposition, [status(thm), theory('equality')], [c_425, c_454])).
% 8.00/2.87  tff(c_511, plain, (![D_224]: (m1_subset_1(k9_relat_1('#skF_7', D_224), k1_zfmisc_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_476])).
% 8.00/2.87  tff(c_16, plain, (![A_9, C_11, B_10]: (m1_subset_1(A_9, C_11) | ~m1_subset_1(B_10, k1_zfmisc_1(C_11)) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_54])).
% 8.00/2.87  tff(c_555, plain, (![A_227, D_228]: (m1_subset_1(A_227, '#skF_5') | ~r2_hidden(A_227, k9_relat_1('#skF_7', D_228)))), inference(resolution, [status(thm)], [c_511, c_16])).
% 8.00/2.87  tff(c_571, plain, (m1_subset_1('#skF_8', '#skF_5')), inference(resolution, [status(thm)], [c_428, c_555])).
% 8.00/2.87  tff(c_157, plain, (![C_163, B_164, A_165]: (v1_xboole_0(C_163) | ~m1_subset_1(C_163, k1_zfmisc_1(k2_zfmisc_1(B_164, A_165))) | ~v1_xboole_0(A_165))), inference(cnfTransformation, [status(thm)], [f_98])).
% 8.00/2.87  tff(c_171, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_56, c_157])).
% 8.00/2.87  tff(c_172, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_171])).
% 8.00/2.87  tff(c_1273, plain, (![D_307, B_305, A_306, C_308, E_304]: (m1_subset_1('#skF_3'(E_304, B_305, A_306, D_307, C_308), C_308) | ~r2_hidden(E_304, k7_relset_1(C_308, A_306, D_307, B_305)) | ~m1_subset_1(E_304, A_306) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(C_308, A_306))) | v1_xboole_0(C_308) | v1_xboole_0(B_305) | v1_xboole_0(A_306))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.00/2.87  tff(c_1281, plain, (![E_304, D_218]: (m1_subset_1('#skF_3'(E_304, D_218, '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~r2_hidden(E_304, k9_relat_1('#skF_7', D_218)) | ~m1_subset_1(E_304, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_218) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_1273])).
% 8.00/2.87  tff(c_1294, plain, (![E_304, D_218]: (m1_subset_1('#skF_3'(E_304, D_218, '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~r2_hidden(E_304, k9_relat_1('#skF_7', D_218)) | ~m1_subset_1(E_304, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_218) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1281])).
% 8.00/2.87  tff(c_2122, plain, (![E_385, D_386]: (m1_subset_1('#skF_3'(E_385, D_386, '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~r2_hidden(E_385, k9_relat_1('#skF_7', D_386)) | ~m1_subset_1(E_385, '#skF_5') | v1_xboole_0(D_386))), inference(negUnitSimplification, [status(thm)], [c_172, c_156, c_1294])).
% 8.00/2.87  tff(c_2145, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_428, c_2122])).
% 8.00/2.87  tff(c_2168, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_2145])).
% 8.00/2.87  tff(c_2169, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_275, c_2168])).
% 8.00/2.87  tff(c_1022, plain, (![E_274, C_278, B_275, A_276, D_277]: (r2_hidden('#skF_3'(E_274, B_275, A_276, D_277, C_278), B_275) | ~r2_hidden(E_274, k7_relset_1(C_278, A_276, D_277, B_275)) | ~m1_subset_1(E_274, A_276) | ~m1_subset_1(D_277, k1_zfmisc_1(k2_zfmisc_1(C_278, A_276))) | v1_xboole_0(C_278) | v1_xboole_0(B_275) | v1_xboole_0(A_276))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.00/2.87  tff(c_1036, plain, (![E_274, B_275]: (r2_hidden('#skF_3'(E_274, B_275, '#skF_5', '#skF_7', '#skF_4'), B_275) | ~r2_hidden(E_274, k7_relset_1('#skF_4', '#skF_5', '#skF_7', B_275)) | ~m1_subset_1(E_274, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_275) | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_56, c_1022])).
% 8.00/2.87  tff(c_1042, plain, (![E_274, B_275]: (r2_hidden('#skF_3'(E_274, B_275, '#skF_5', '#skF_7', '#skF_4'), B_275) | ~r2_hidden(E_274, k9_relat_1('#skF_7', B_275)) | ~m1_subset_1(E_274, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(B_275) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_425, c_1036])).
% 8.00/2.87  tff(c_1381, plain, (![E_319, B_320]: (r2_hidden('#skF_3'(E_319, B_320, '#skF_5', '#skF_7', '#skF_4'), B_320) | ~r2_hidden(E_319, k9_relat_1('#skF_7', B_320)) | ~m1_subset_1(E_319, '#skF_5') | v1_xboole_0(B_320))), inference(negUnitSimplification, [status(thm)], [c_172, c_156, c_1042])).
% 8.00/2.87  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.00/2.87  tff(c_2496, plain, (![E_440, B_441]: (m1_subset_1('#skF_3'(E_440, B_441, '#skF_5', '#skF_7', '#skF_4'), B_441) | ~r2_hidden(E_440, k9_relat_1('#skF_7', B_441)) | ~m1_subset_1(E_440, '#skF_5') | v1_xboole_0(B_441))), inference(resolution, [status(thm)], [c_1381, c_14])).
% 8.00/2.87  tff(c_2513, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_6') | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_428, c_2496])).
% 8.00/2.87  tff(c_2533, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_6') | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_2513])).
% 8.00/2.87  tff(c_2534, plain, (m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_275, c_2533])).
% 8.00/2.87  tff(c_258, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~m1_subset_1(B_6, '#skF_6') | ~m1_subset_1(B_6, '#skF_4') | v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_250])).
% 8.00/2.87  tff(c_266, plain, (![B_6]: (k1_funct_1('#skF_7', B_6)!='#skF_8' | ~m1_subset_1(B_6, '#skF_6') | ~m1_subset_1(B_6, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_156, c_258])).
% 8.00/2.87  tff(c_2545, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))!='#skF_8' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_2534, c_266])).
% 8.00/2.87  tff(c_2551, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2169, c_2545])).
% 8.00/2.87  tff(c_1576, plain, (![D_339, E_336, C_340, A_338, B_337]: (r2_hidden(k4_tarski('#skF_3'(E_336, B_337, A_338, D_339, C_340), E_336), D_339) | ~r2_hidden(E_336, k7_relset_1(C_340, A_338, D_339, B_337)) | ~m1_subset_1(E_336, A_338) | ~m1_subset_1(D_339, k1_zfmisc_1(k2_zfmisc_1(C_340, A_338))) | v1_xboole_0(C_340) | v1_xboole_0(B_337) | v1_xboole_0(A_338))), inference(cnfTransformation, [status(thm)], [f_132])).
% 8.00/2.87  tff(c_32, plain, (![C_25, A_23, B_24]: (k1_funct_1(C_25, A_23)=B_24 | ~r2_hidden(k4_tarski(A_23, B_24), C_25) | ~v1_funct_1(C_25) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.00/2.87  tff(c_5872, plain, (![E_648, D_649, B_651, A_647, C_650]: (k1_funct_1(D_649, '#skF_3'(E_648, B_651, A_647, D_649, C_650))=E_648 | ~v1_funct_1(D_649) | ~v1_relat_1(D_649) | ~r2_hidden(E_648, k7_relset_1(C_650, A_647, D_649, B_651)) | ~m1_subset_1(E_648, A_647) | ~m1_subset_1(D_649, k1_zfmisc_1(k2_zfmisc_1(C_650, A_647))) | v1_xboole_0(C_650) | v1_xboole_0(B_651) | v1_xboole_0(A_647))), inference(resolution, [status(thm)], [c_1576, c_32])).
% 8.00/2.87  tff(c_5886, plain, (![E_648, D_218]: (k1_funct_1('#skF_7', '#skF_3'(E_648, D_218, '#skF_5', '#skF_7', '#skF_4'))=E_648 | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7') | ~r2_hidden(E_648, k9_relat_1('#skF_7', D_218)) | ~m1_subset_1(E_648, '#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5'))) | v1_xboole_0('#skF_4') | v1_xboole_0(D_218) | v1_xboole_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_5872])).
% 8.00/2.87  tff(c_5901, plain, (![E_648, D_218]: (k1_funct_1('#skF_7', '#skF_3'(E_648, D_218, '#skF_5', '#skF_7', '#skF_4'))=E_648 | ~r2_hidden(E_648, k9_relat_1('#skF_7', D_218)) | ~m1_subset_1(E_648, '#skF_5') | v1_xboole_0('#skF_4') | v1_xboole_0(D_218) | v1_xboole_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_117, c_60, c_5886])).
% 8.00/2.87  tff(c_5907, plain, (![E_652, D_653]: (k1_funct_1('#skF_7', '#skF_3'(E_652, D_653, '#skF_5', '#skF_7', '#skF_4'))=E_652 | ~r2_hidden(E_652, k9_relat_1('#skF_7', D_653)) | ~m1_subset_1(E_652, '#skF_5') | v1_xboole_0(D_653))), inference(negUnitSimplification, [status(thm)], [c_172, c_156, c_5901])).
% 8.00/2.87  tff(c_5959, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))='#skF_8' | ~m1_subset_1('#skF_8', '#skF_5') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_428, c_5907])).
% 8.00/2.87  tff(c_6010, plain, (k1_funct_1('#skF_7', '#skF_3'('#skF_8', '#skF_6', '#skF_5', '#skF_7', '#skF_4'))='#skF_8' | v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_571, c_5959])).
% 8.00/2.87  tff(c_6012, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_2551, c_6010])).
% 8.00/2.87  tff(c_6014, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_274])).
% 8.00/2.87  tff(c_202, plain, (![A_170, B_171, C_172]: (r2_hidden('#skF_2'(A_170, B_171, C_172), B_171) | ~r2_hidden(A_170, k9_relat_1(C_172, B_171)) | ~v1_relat_1(C_172))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.00/2.87  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.00/2.87  tff(c_216, plain, (![B_173, A_174, C_175]: (~v1_xboole_0(B_173) | ~r2_hidden(A_174, k9_relat_1(C_175, B_173)) | ~v1_relat_1(C_175))), inference(resolution, [status(thm)], [c_202, c_2])).
% 8.00/2.87  tff(c_231, plain, (![B_173, C_175]: (~v1_xboole_0(B_173) | ~v1_relat_1(C_175) | v1_xboole_0(k9_relat_1(C_175, B_173)))), inference(resolution, [status(thm)], [c_4, c_216])).
% 8.00/2.87  tff(c_6173, plain, (![A_688, B_689, C_690, D_691]: (k7_relset_1(A_688, B_689, C_690, D_691)=k9_relat_1(C_690, D_691) | ~m1_subset_1(C_690, k1_zfmisc_1(k2_zfmisc_1(A_688, B_689))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.00/2.87  tff(c_6192, plain, (![D_691]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_691)=k9_relat_1('#skF_7', D_691))), inference(resolution, [status(thm)], [c_56, c_6173])).
% 8.00/2.87  tff(c_82, plain, (~v1_xboole_0(k7_relset_1('#skF_4', '#skF_5', '#skF_7', '#skF_6'))), inference(resolution, [status(thm)], [c_54, c_2])).
% 8.00/2.87  tff(c_6194, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6192, c_82])).
% 8.00/2.87  tff(c_6212, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_231, c_6194])).
% 8.00/2.87  tff(c_6216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_6014, c_6212])).
% 8.00/2.87  tff(c_6217, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_137])).
% 8.00/2.87  tff(c_6267, plain, (![A_711, B_712, C_713, D_714]: (k7_relset_1(A_711, B_712, C_713, D_714)=k9_relat_1(C_713, D_714) | ~m1_subset_1(C_713, k1_zfmisc_1(k2_zfmisc_1(A_711, B_712))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.00/2.87  tff(c_6278, plain, (![D_714]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_714)=k9_relat_1('#skF_7', D_714))), inference(resolution, [status(thm)], [c_56, c_6267])).
% 8.00/2.87  tff(c_6280, plain, (~v1_xboole_0(k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6278, c_82])).
% 8.00/2.87  tff(c_6293, plain, (~v1_xboole_0('#skF_6') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_231, c_6280])).
% 8.00/2.87  tff(c_6297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_6217, c_6293])).
% 8.00/2.87  tff(c_6298, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_171])).
% 8.00/2.87  tff(c_6764, plain, (![A_787, C_788]: (r2_hidden(k4_tarski(A_787, k1_funct_1(C_788, A_787)), C_788) | ~r2_hidden(A_787, k1_relat_1(C_788)) | ~v1_funct_1(C_788) | ~v1_relat_1(C_788))), inference(cnfTransformation, [status(thm)], [f_84])).
% 8.00/2.87  tff(c_6831, plain, (![C_789, A_790]: (~v1_xboole_0(C_789) | ~r2_hidden(A_790, k1_relat_1(C_789)) | ~v1_funct_1(C_789) | ~v1_relat_1(C_789))), inference(resolution, [status(thm)], [c_6764, c_2])).
% 8.00/2.87  tff(c_6856, plain, (![C_791]: (~v1_xboole_0(C_791) | ~v1_funct_1(C_791) | ~v1_relat_1(C_791) | v1_xboole_0(k1_relat_1(C_791)))), inference(resolution, [status(thm)], [c_4, c_6831])).
% 8.00/2.87  tff(c_6465, plain, (![A_752, B_753, C_754, D_755]: (k7_relset_1(A_752, B_753, C_754, D_755)=k9_relat_1(C_754, D_755) | ~m1_subset_1(C_754, k1_zfmisc_1(k2_zfmisc_1(A_752, B_753))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.00/2.87  tff(c_6476, plain, (![D_755]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_755)=k9_relat_1('#skF_7', D_755))), inference(resolution, [status(thm)], [c_56, c_6465])).
% 8.00/2.87  tff(c_6479, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_6476, c_54])).
% 8.00/2.87  tff(c_6653, plain, (![A_769, B_770, C_771]: (r2_hidden('#skF_2'(A_769, B_770, C_771), k1_relat_1(C_771)) | ~r2_hidden(A_769, k9_relat_1(C_771, B_770)) | ~v1_relat_1(C_771))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.00/2.87  tff(c_6662, plain, (![C_772, A_773, B_774]: (~v1_xboole_0(k1_relat_1(C_772)) | ~r2_hidden(A_773, k9_relat_1(C_772, B_774)) | ~v1_relat_1(C_772))), inference(resolution, [status(thm)], [c_6653, c_2])).
% 8.00/2.87  tff(c_6665, plain, (~v1_xboole_0(k1_relat_1('#skF_7')) | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6479, c_6662])).
% 8.00/2.87  tff(c_6680, plain, (~v1_xboole_0(k1_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_117, c_6665])).
% 8.00/2.87  tff(c_6859, plain, (~v1_xboole_0('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_6856, c_6680])).
% 8.00/2.87  tff(c_6863, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_60, c_6298, c_6859])).
% 8.00/2.87  tff(c_6864, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_155])).
% 8.00/2.87  tff(c_7068, plain, (![A_837, B_838, C_839, D_840]: (k7_relset_1(A_837, B_838, C_839, D_840)=k9_relat_1(C_839, D_840) | ~m1_subset_1(C_839, k1_zfmisc_1(k2_zfmisc_1(A_837, B_838))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.00/2.87  tff(c_7087, plain, (![D_840]: (k7_relset_1('#skF_4', '#skF_5', '#skF_7', D_840)=k9_relat_1('#skF_7', D_840))), inference(resolution, [status(thm)], [c_56, c_7068])).
% 8.00/2.87  tff(c_7099, plain, (r2_hidden('#skF_8', k9_relat_1('#skF_7', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_7087, c_54])).
% 8.00/2.87  tff(c_7161, plain, (![A_846, B_847, C_848]: (r2_hidden(k4_tarski('#skF_2'(A_846, B_847, C_848), A_846), C_848) | ~r2_hidden(A_846, k9_relat_1(C_848, B_847)) | ~v1_relat_1(C_848))), inference(cnfTransformation, [status(thm)], [f_74])).
% 8.00/2.87  tff(c_7291, plain, (![C_853, A_854, B_855]: (~v1_xboole_0(C_853) | ~r2_hidden(A_854, k9_relat_1(C_853, B_855)) | ~v1_relat_1(C_853))), inference(resolution, [status(thm)], [c_7161, c_2])).
% 8.00/2.87  tff(c_7302, plain, (~v1_xboole_0('#skF_7') | ~v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_7099, c_7291])).
% 8.00/2.87  tff(c_7320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_117, c_6864, c_7302])).
% 8.00/2.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.00/2.87  
% 8.00/2.87  Inference rules
% 8.00/2.87  ----------------------
% 8.00/2.87  #Ref     : 0
% 8.00/2.87  #Sup     : 1478
% 8.00/2.87  #Fact    : 0
% 8.00/2.87  #Define  : 0
% 8.00/2.87  #Split   : 39
% 8.00/2.87  #Chain   : 0
% 8.00/2.87  #Close   : 0
% 8.00/2.87  
% 8.00/2.87  Ordering : KBO
% 8.00/2.87  
% 8.00/2.87  Simplification rules
% 8.00/2.87  ----------------------
% 8.00/2.87  #Subsume      : 345
% 8.00/2.87  #Demod        : 392
% 8.00/2.87  #Tautology    : 122
% 8.00/2.87  #SimpNegUnit  : 157
% 8.00/2.87  #BackRed      : 15
% 8.00/2.87  
% 8.00/2.87  #Partial instantiations: 0
% 8.00/2.87  #Strategies tried      : 1
% 8.00/2.87  
% 8.00/2.87  Timing (in seconds)
% 8.00/2.87  ----------------------
% 8.00/2.87  Preprocessing        : 0.34
% 8.00/2.87  Parsing              : 0.17
% 8.00/2.87  CNF conversion       : 0.03
% 8.00/2.87  Main loop            : 1.63
% 8.00/2.87  Inferencing          : 0.52
% 8.00/2.87  Reduction            : 0.41
% 8.00/2.87  Demodulation         : 0.28
% 8.00/2.87  BG Simplification    : 0.05
% 8.00/2.87  Subsumption          : 0.51
% 8.00/2.87  Abstraction          : 0.07
% 8.00/2.87  MUC search           : 0.00
% 8.00/2.87  Cooper               : 0.00
% 8.00/2.87  Total                : 2.02
% 8.00/2.87  Index Insertion      : 0.00
% 8.00/2.87  Index Deletion       : 0.00
% 8.00/2.87  Index Matching       : 0.00
% 8.00/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
