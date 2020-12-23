%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:22 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 365 expanded)
%              Number of leaves         :   40 ( 138 expanded)
%              Depth                    :   14
%              Number of atoms          :  145 ( 724 expanded)
%              Number of equality atoms :   43 ( 189 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
               => ~ ( k2_relset_1(B,A,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k1_relset_1(B,A,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_39,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k1_relat_1(k7_relat_1(C,B)))
      <=> ( r2_hidden(A,B)
          & r2_hidden(A,k1_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_26,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_27,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_93,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1445,plain,(
    ! [A_229,B_230,C_231] :
      ( k1_relset_1(A_229,B_230,C_231) = k1_relat_1(C_231)
      | ~ m1_subset_1(C_231,k1_zfmisc_1(k2_zfmisc_1(A_229,B_230))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1460,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1445])).

tff(c_8,plain,(
    ! [A_2] :
      ( r2_hidden('#skF_1'(A_2),A_2)
      | k1_xboole_0 = A_2 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_135,plain,(
    ! [D_60] :
      ( ~ r2_hidden(D_60,k1_relset_1('#skF_3','#skF_2','#skF_4'))
      | ~ m1_subset_1(D_60,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_140,plain,
    ( ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3')
    | k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_135])).

tff(c_1345,plain,(
    ~ m1_subset_1('#skF_1'(k1_relset_1('#skF_3','#skF_2','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_140])).

tff(c_1484,plain,(
    ~ m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1460,c_1345])).

tff(c_115,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_128,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_1272,plain,(
    ! [C_202,A_203,B_204] :
      ( v4_relat_1(C_202,A_203)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_203,B_204))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1287,plain,(
    v4_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1272])).

tff(c_1321,plain,(
    ! [B_212,A_213] :
      ( k7_relat_1(B_212,A_213) = B_212
      | ~ v4_relat_1(B_212,A_213)
      | ~ v1_relat_1(B_212) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1327,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1287,c_1321])).

tff(c_1333,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1327])).

tff(c_1372,plain,(
    ! [A_221,B_222,C_223] :
      ( r2_hidden(A_221,B_222)
      | ~ r2_hidden(A_221,k1_relat_1(k7_relat_1(C_223,B_222)))
      | ~ v1_relat_1(C_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1378,plain,(
    ! [A_221] :
      ( r2_hidden(A_221,'#skF_3')
      | ~ r2_hidden(A_221,k1_relat_1('#skF_4'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1333,c_1372])).

tff(c_1418,plain,(
    ! [A_225] :
      ( r2_hidden(A_225,'#skF_3')
      | ~ r2_hidden(A_225,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_128,c_1378])).

tff(c_1423,plain,
    ( r2_hidden('#skF_1'(k1_relat_1('#skF_4')),'#skF_3')
    | k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_1418])).

tff(c_1502,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_1423])).

tff(c_1658,plain,(
    ! [D_256,B_257,C_258,A_259] :
      ( m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(B_257,C_258)))
      | ~ r1_tarski(k1_relat_1(D_256),B_257)
      | ~ m1_subset_1(D_256,k1_zfmisc_1(k2_zfmisc_1(A_259,C_258))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1663,plain,(
    ! [B_257] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_257,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_257) ) ),
    inference(resolution,[status(thm)],[c_50,c_1658])).

tff(c_1690,plain,(
    ! [B_261] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_261,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1502,c_1663])).

tff(c_1713,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_1690])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1354,plain,(
    ! [C_218,B_219,A_220] :
      ( v1_xboole_0(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k2_zfmisc_1(B_219,A_220)))
      | ~ v1_xboole_0(A_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1364,plain,(
    ! [C_218] :
      ( v1_xboole_0(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1354])).

tff(c_1371,plain,(
    ! [C_218] :
      ( v1_xboole_0(C_218)
      | ~ m1_subset_1(C_218,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1364])).

tff(c_1758,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1713,c_1371])).

tff(c_6,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1767,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1758,c_6])).

tff(c_1503,plain,(
    ! [A_235,B_236,C_237] :
      ( k2_relset_1(A_235,B_236,C_237) = k2_relat_1(C_237)
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1518,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1503])).

tff(c_48,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_1531,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1518,c_48])).

tff(c_1778,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_1531])).

tff(c_22,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1801,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1767,c_1767,c_22])).

tff(c_1855,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1778,c_1801])).

tff(c_1856,plain,(
    r2_hidden('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1423])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,B_8)
      | ~ r2_hidden(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1860,plain,(
    m1_subset_1('#skF_1'(k1_relat_1('#skF_4')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1856,c_18])).

tff(c_1864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1484,c_1860])).

tff(c_1865,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_140])).

tff(c_1994,plain,(
    ! [A_283,B_284,C_285] :
      ( k1_relset_1(A_283,B_284,C_285) = k1_relat_1(C_285)
      | ~ m1_subset_1(C_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2001,plain,(
    k1_relset_1('#skF_3','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1994])).

tff(c_2010,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1865,c_2001])).

tff(c_2169,plain,(
    ! [D_307,B_308,C_309,A_310] :
      ( m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(B_308,C_309)))
      | ~ r1_tarski(k1_relat_1(D_307),B_308)
      | ~ m1_subset_1(D_307,k1_zfmisc_1(k2_zfmisc_1(A_310,C_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2174,plain,(
    ! [B_308] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_308,'#skF_2')))
      | ~ r1_tarski(k1_relat_1('#skF_4'),B_308) ) ),
    inference(resolution,[status(thm)],[c_50,c_2169])).

tff(c_2186,plain,(
    ! [B_311] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_311,'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_2010,c_2174])).

tff(c_2209,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2186])).

tff(c_1867,plain,(
    ! [C_268,B_269,A_270] :
      ( v1_xboole_0(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k2_zfmisc_1(B_269,A_270)))
      | ~ v1_xboole_0(A_270) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_1877,plain,(
    ! [C_268] :
      ( v1_xboole_0(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1867])).

tff(c_1884,plain,(
    ! [C_268] :
      ( v1_xboole_0(C_268)
      | ~ m1_subset_1(C_268,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_1877])).

tff(c_2254,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2209,c_1884])).

tff(c_2263,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2254,c_6])).

tff(c_2018,plain,(
    ! [A_286,B_287,C_288] :
      ( k2_relset_1(A_286,B_287,C_288) = k2_relat_1(C_288)
      | ~ m1_subset_1(C_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287))) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2033,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2018])).

tff(c_2034,plain,(
    k2_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2033,c_48])).

tff(c_2273,plain,(
    k2_relat_1('#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2263,c_2034])).

tff(c_2297,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2263,c_2263,c_22])).

tff(c_2343,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2273,c_2297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:52:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.90/1.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.66  
% 3.90/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.66  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 3.90/1.66  
% 3.90/1.66  %Foreground sorts:
% 3.90/1.66  
% 3.90/1.66  
% 3.90/1.66  %Background operators:
% 3.90/1.66  
% 3.90/1.66  
% 3.90/1.66  %Foreground operators:
% 3.90/1.66  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.90/1.66  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.90/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.90/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.90/1.66  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.90/1.66  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.90/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.90/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.90/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.90/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.90/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.90/1.66  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.90/1.66  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.90/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.90/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.90/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.90/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.90/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.90/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.90/1.66  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.90/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.90/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.90/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.90/1.66  
% 3.90/1.68  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.90/1.68  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.90/1.68  tff(f_120, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ~(~(k2_relset_1(B, A, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k1_relset_1(B, A, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_relset_1)).
% 3.90/1.68  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.90/1.68  tff(f_39, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.90/1.68  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.90/1.68  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.90/1.68  tff(f_57, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 3.90/1.68  tff(f_68, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k1_relat_1(k7_relat_1(C, B))) <=> (r2_hidden(A, B) & r2_hidden(A, k1_relat_1(C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_relat_1)).
% 3.90/1.68  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 3.90/1.68  tff(f_26, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 3.90/1.68  tff(f_27, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 3.90/1.68  tff(f_85, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 3.90/1.68  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.90/1.68  tff(f_93, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.90/1.68  tff(f_60, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.90/1.68  tff(f_51, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.90/1.68  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.90/1.68  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.90/1.68  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.68  tff(c_1445, plain, (![A_229, B_230, C_231]: (k1_relset_1(A_229, B_230, C_231)=k1_relat_1(C_231) | ~m1_subset_1(C_231, k1_zfmisc_1(k2_zfmisc_1(A_229, B_230))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.90/1.68  tff(c_1460, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1445])).
% 3.90/1.68  tff(c_8, plain, (![A_2]: (r2_hidden('#skF_1'(A_2), A_2) | k1_xboole_0=A_2)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.90/1.68  tff(c_135, plain, (![D_60]: (~r2_hidden(D_60, k1_relset_1('#skF_3', '#skF_2', '#skF_4')) | ~m1_subset_1(D_60, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.68  tff(c_140, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3') | k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_135])).
% 3.90/1.68  tff(c_1345, plain, (~m1_subset_1('#skF_1'(k1_relset_1('#skF_3', '#skF_2', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_140])).
% 3.90/1.68  tff(c_1484, plain, (~m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1460, c_1345])).
% 3.90/1.68  tff(c_115, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.90/1.68  tff(c_128, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_115])).
% 3.90/1.68  tff(c_1272, plain, (![C_202, A_203, B_204]: (v4_relat_1(C_202, A_203) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_203, B_204))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.90/1.68  tff(c_1287, plain, (v4_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_1272])).
% 3.90/1.68  tff(c_1321, plain, (![B_212, A_213]: (k7_relat_1(B_212, A_213)=B_212 | ~v4_relat_1(B_212, A_213) | ~v1_relat_1(B_212))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.90/1.68  tff(c_1327, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1287, c_1321])).
% 3.90/1.68  tff(c_1333, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1327])).
% 3.90/1.68  tff(c_1372, plain, (![A_221, B_222, C_223]: (r2_hidden(A_221, B_222) | ~r2_hidden(A_221, k1_relat_1(k7_relat_1(C_223, B_222))) | ~v1_relat_1(C_223))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.90/1.68  tff(c_1378, plain, (![A_221]: (r2_hidden(A_221, '#skF_3') | ~r2_hidden(A_221, k1_relat_1('#skF_4')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1333, c_1372])).
% 3.90/1.68  tff(c_1418, plain, (![A_225]: (r2_hidden(A_225, '#skF_3') | ~r2_hidden(A_225, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_128, c_1378])).
% 3.90/1.68  tff(c_1423, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4')), '#skF_3') | k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_1418])).
% 3.90/1.68  tff(c_1502, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_1423])).
% 3.90/1.68  tff(c_1658, plain, (![D_256, B_257, C_258, A_259]: (m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(B_257, C_258))) | ~r1_tarski(k1_relat_1(D_256), B_257) | ~m1_subset_1(D_256, k1_zfmisc_1(k2_zfmisc_1(A_259, C_258))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.90/1.68  tff(c_1663, plain, (![B_257]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_257, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_257))), inference(resolution, [status(thm)], [c_50, c_1658])).
% 3.90/1.68  tff(c_1690, plain, (![B_261]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_261, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1502, c_1663])).
% 3.90/1.68  tff(c_1713, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_1690])).
% 3.90/1.68  tff(c_2, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.90/1.68  tff(c_4, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.90/1.68  tff(c_55, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.90/1.68  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.90/1.68  tff(c_1354, plain, (![C_218, B_219, A_220]: (v1_xboole_0(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k2_zfmisc_1(B_219, A_220))) | ~v1_xboole_0(A_220))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/1.68  tff(c_1364, plain, (![C_218]: (v1_xboole_0(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1354])).
% 3.90/1.68  tff(c_1371, plain, (![C_218]: (v1_xboole_0(C_218) | ~m1_subset_1(C_218, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1364])).
% 3.90/1.68  tff(c_1758, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_1713, c_1371])).
% 3.90/1.68  tff(c_6, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.90/1.68  tff(c_1767, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_1758, c_6])).
% 3.90/1.68  tff(c_1503, plain, (![A_235, B_236, C_237]: (k2_relset_1(A_235, B_236, C_237)=k2_relat_1(C_237) | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.90/1.68  tff(c_1518, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1503])).
% 3.90/1.68  tff(c_48, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_120])).
% 3.90/1.68  tff(c_1531, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1518, c_48])).
% 3.90/1.68  tff(c_1778, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_1531])).
% 3.90/1.68  tff(c_22, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.90/1.68  tff(c_1801, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1767, c_1767, c_22])).
% 3.90/1.68  tff(c_1855, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1778, c_1801])).
% 3.90/1.68  tff(c_1856, plain, (r2_hidden('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(splitRight, [status(thm)], [c_1423])).
% 3.90/1.68  tff(c_18, plain, (![A_7, B_8]: (m1_subset_1(A_7, B_8) | ~r2_hidden(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.90/1.68  tff(c_1860, plain, (m1_subset_1('#skF_1'(k1_relat_1('#skF_4')), '#skF_3')), inference(resolution, [status(thm)], [c_1856, c_18])).
% 3.90/1.68  tff(c_1864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1484, c_1860])).
% 3.90/1.68  tff(c_1865, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_xboole_0), inference(splitRight, [status(thm)], [c_140])).
% 3.90/1.68  tff(c_1994, plain, (![A_283, B_284, C_285]: (k1_relset_1(A_283, B_284, C_285)=k1_relat_1(C_285) | ~m1_subset_1(C_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.90/1.68  tff(c_2001, plain, (k1_relset_1('#skF_3', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_1994])).
% 3.90/1.68  tff(c_2010, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1865, c_2001])).
% 3.90/1.68  tff(c_2169, plain, (![D_307, B_308, C_309, A_310]: (m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(B_308, C_309))) | ~r1_tarski(k1_relat_1(D_307), B_308) | ~m1_subset_1(D_307, k1_zfmisc_1(k2_zfmisc_1(A_310, C_309))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.90/1.68  tff(c_2174, plain, (![B_308]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_308, '#skF_2'))) | ~r1_tarski(k1_relat_1('#skF_4'), B_308))), inference(resolution, [status(thm)], [c_50, c_2169])).
% 3.90/1.68  tff(c_2186, plain, (![B_311]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_311, '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_2010, c_2174])).
% 3.90/1.68  tff(c_2209, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2186])).
% 3.90/1.68  tff(c_1867, plain, (![C_268, B_269, A_270]: (v1_xboole_0(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k2_zfmisc_1(B_269, A_270))) | ~v1_xboole_0(A_270))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.90/1.68  tff(c_1877, plain, (![C_268]: (v1_xboole_0(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1867])).
% 3.90/1.68  tff(c_1884, plain, (![C_268]: (v1_xboole_0(C_268) | ~m1_subset_1(C_268, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_1877])).
% 3.90/1.68  tff(c_2254, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2209, c_1884])).
% 3.90/1.68  tff(c_2263, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2254, c_6])).
% 3.90/1.68  tff(c_2018, plain, (![A_286, B_287, C_288]: (k2_relset_1(A_286, B_287, C_288)=k2_relat_1(C_288) | ~m1_subset_1(C_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.90/1.68  tff(c_2033, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_50, c_2018])).
% 3.90/1.68  tff(c_2034, plain, (k2_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2033, c_48])).
% 3.90/1.68  tff(c_2273, plain, (k2_relat_1('#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2263, c_2034])).
% 3.90/1.68  tff(c_2297, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2263, c_2263, c_22])).
% 3.90/1.68  tff(c_2343, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2273, c_2297])).
% 3.90/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/1.68  
% 3.90/1.68  Inference rules
% 3.90/1.68  ----------------------
% 3.90/1.68  #Ref     : 0
% 3.90/1.68  #Sup     : 479
% 3.90/1.68  #Fact    : 0
% 3.90/1.68  #Define  : 0
% 3.90/1.68  #Split   : 6
% 3.90/1.68  #Chain   : 0
% 3.90/1.68  #Close   : 0
% 3.90/1.68  
% 3.90/1.68  Ordering : KBO
% 3.90/1.68  
% 3.90/1.68  Simplification rules
% 3.90/1.68  ----------------------
% 3.90/1.68  #Subsume      : 35
% 3.90/1.68  #Demod        : 578
% 3.90/1.68  #Tautology    : 244
% 3.90/1.68  #SimpNegUnit  : 22
% 3.90/1.68  #BackRed      : 176
% 3.90/1.68  
% 3.90/1.68  #Partial instantiations: 0
% 3.90/1.68  #Strategies tried      : 1
% 3.90/1.68  
% 3.90/1.68  Timing (in seconds)
% 3.90/1.68  ----------------------
% 3.90/1.68  Preprocessing        : 0.33
% 3.90/1.68  Parsing              : 0.18
% 3.90/1.68  CNF conversion       : 0.02
% 3.90/1.68  Main loop            : 0.59
% 3.90/1.68  Inferencing          : 0.20
% 3.90/1.68  Reduction            : 0.20
% 3.90/1.68  Demodulation         : 0.14
% 3.90/1.68  BG Simplification    : 0.03
% 3.90/1.68  Subsumption          : 0.10
% 3.90/1.68  Abstraction          : 0.03
% 3.90/1.68  MUC search           : 0.00
% 3.90/1.68  Cooper               : 0.00
% 3.90/1.68  Total                : 0.96
% 3.90/1.68  Index Insertion      : 0.00
% 3.90/1.68  Index Deletion       : 0.00
% 3.90/1.68  Index Matching       : 0.00
% 3.90/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
