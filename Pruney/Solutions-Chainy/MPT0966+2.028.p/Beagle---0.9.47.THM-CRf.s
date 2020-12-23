%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:12 EST 2020

% Result     : Theorem 5.37s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  250 (3103 expanded)
%              Number of leaves         :   38 (1002 expanded)
%              Depth                    :   18
%              Number of atoms          :  417 (8193 expanded)
%              Number of equality atoms :  156 (2079 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_127,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_70,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_44,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_112,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_62,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4691,plain,(
    ! [A_524,B_525,C_526] :
      ( k1_relset_1(A_524,B_525,C_526) = k1_relat_1(C_526)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(A_524,B_525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4706,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_4691])).

tff(c_4902,plain,(
    ! [B_555,A_556,C_557] :
      ( k1_xboole_0 = B_555
      | k1_relset_1(A_556,B_555,C_557) = A_556
      | ~ v1_funct_2(C_557,A_556,B_555)
      | ~ m1_subset_1(C_557,k1_zfmisc_1(k2_zfmisc_1(A_556,B_555))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_4912,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_4902])).

tff(c_4923,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4706,c_4912])).

tff(c_4924,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_4923])).

tff(c_32,plain,(
    ! [A_19,B_20] : v1_relat_1(k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4580,plain,(
    ! [B_509,A_510] :
      ( v1_relat_1(B_509)
      | ~ m1_subset_1(B_509,k1_zfmisc_1(A_510))
      | ~ v1_relat_1(A_510) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4586,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_4580])).

tff(c_4590,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_4586])).

tff(c_4712,plain,(
    ! [A_527,B_528,C_529] :
      ( k2_relset_1(A_527,B_528,C_529) = k2_relat_1(C_529)
      | ~ m1_subset_1(C_529,k1_zfmisc_1(k2_zfmisc_1(A_527,B_528))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4727,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_4712])).

tff(c_60,plain,(
    r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_4729,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4727,c_60])).

tff(c_4788,plain,(
    ! [C_539,A_540,B_541] :
      ( m1_subset_1(C_539,k1_zfmisc_1(k2_zfmisc_1(A_540,B_541)))
      | ~ r1_tarski(k2_relat_1(C_539),B_541)
      | ~ r1_tarski(k1_relat_1(C_539),A_540)
      | ~ v1_relat_1(C_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1341,plain,(
    ! [A_184,B_185,C_186] :
      ( k1_relset_1(A_184,B_185,C_186) = k1_relat_1(C_186)
      | ~ m1_subset_1(C_186,k1_zfmisc_1(k2_zfmisc_1(A_184,B_185))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1356,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1341])).

tff(c_1628,plain,(
    ! [B_228,A_229,C_230] :
      ( k1_xboole_0 = B_228
      | k1_relset_1(A_229,B_228,C_230) = A_229
      | ~ v1_funct_2(C_230,A_229,B_228)
      | ~ m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_229,B_228))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_1638,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1628])).

tff(c_1649,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1356,c_1638])).

tff(c_1650,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_1649])).

tff(c_147,plain,(
    ! [B_49,A_50] :
      ( v1_relat_1(B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_50))
      | ~ v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_153,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_147])).

tff(c_157,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_153])).

tff(c_1295,plain,(
    ! [A_179,B_180,C_181] :
      ( k2_relset_1(A_179,B_180,C_181) = k2_relat_1(C_181)
      | ~ m1_subset_1(C_181,k1_zfmisc_1(k2_zfmisc_1(A_179,B_180))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1310,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_1295])).

tff(c_1312,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_60])).

tff(c_1473,plain,(
    ! [C_205,A_206,B_207] :
      ( m1_subset_1(C_205,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ r1_tarski(k2_relat_1(C_205),B_207)
      | ~ r1_tarski(k1_relat_1(C_205),A_206)
      | ~ v1_relat_1(C_205) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1739,plain,(
    ! [C_242,A_243,B_244] :
      ( r1_tarski(C_242,k2_zfmisc_1(A_243,B_244))
      | ~ r1_tarski(k2_relat_1(C_242),B_244)
      | ~ r1_tarski(k1_relat_1(C_242),A_243)
      | ~ v1_relat_1(C_242) ) ),
    inference(resolution,[status(thm)],[c_1473,c_24])).

tff(c_1741,plain,(
    ! [A_243] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_243,'#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_243)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1312,c_1739])).

tff(c_1753,plain,(
    ! [A_245] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_245,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1650,c_1741])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1355,plain,(
    ! [A_184,B_185,A_11] :
      ( k1_relset_1(A_184,B_185,A_11) = k1_relat_1(A_11)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_184,B_185)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1341])).

tff(c_1756,plain,(
    ! [A_245] :
      ( k1_relset_1(A_245,'#skF_4','#skF_5') = k1_relat_1('#skF_5')
      | ~ r1_tarski('#skF_2',A_245) ) ),
    inference(resolution,[status(thm)],[c_1753,c_1355])).

tff(c_1780,plain,(
    ! [A_246] :
      ( k1_relset_1(A_246,'#skF_4','#skF_5') = '#skF_2'
      | ~ r1_tarski('#skF_2',A_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_1756])).

tff(c_1785,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_5') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_1780])).

tff(c_1230,plain,(
    ! [C_169,B_170,A_171] :
      ( ~ v1_xboole_0(C_169)
      | ~ m1_subset_1(B_170,k1_zfmisc_1(C_169))
      | ~ r2_hidden(A_171,B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1272,plain,(
    ! [B_174,A_175,A_176] :
      ( ~ v1_xboole_0(B_174)
      | ~ r2_hidden(A_175,A_176)
      | ~ r1_tarski(A_176,B_174) ) ),
    inference(resolution,[status(thm)],[c_26,c_1230])).

tff(c_1276,plain,(
    ! [B_177,A_178] :
      ( ~ v1_xboole_0(B_177)
      | ~ r1_tarski(A_178,B_177)
      | v1_xboole_0(A_178) ) ),
    inference(resolution,[status(thm)],[c_4,c_1272])).

tff(c_1290,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_1276])).

tff(c_1294,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1290])).

tff(c_1749,plain,(
    ! [A_243] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_243,'#skF_4'))
      | ~ r1_tarski('#skF_2',A_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_1650,c_1741])).

tff(c_2112,plain,(
    ! [B_270,A_271,A_272] :
      ( k1_xboole_0 = B_270
      | k1_relset_1(A_271,B_270,A_272) = A_271
      | ~ v1_funct_2(A_272,A_271,B_270)
      | ~ r1_tarski(A_272,k2_zfmisc_1(A_271,B_270)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1628])).

tff(c_2137,plain,(
    ! [A_243] :
      ( k1_xboole_0 = '#skF_4'
      | k1_relset_1(A_243,'#skF_4','#skF_5') = A_243
      | ~ v1_funct_2('#skF_5',A_243,'#skF_4')
      | ~ r1_tarski('#skF_2',A_243) ) ),
    inference(resolution,[status(thm)],[c_1749,c_2112])).

tff(c_2183,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2137])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2222,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2183,c_6])).

tff(c_2225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1294,c_2222])).

tff(c_2227,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2137])).

tff(c_1687,plain,(
    ! [B_236,C_237,A_238] :
      ( k1_xboole_0 = B_236
      | v1_funct_2(C_237,A_238,B_236)
      | k1_relset_1(A_238,B_236,C_237) != A_238
      | ~ m1_subset_1(C_237,k1_zfmisc_1(k2_zfmisc_1(A_238,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2254,plain,(
    ! [B_280,A_281,A_282] :
      ( k1_xboole_0 = B_280
      | v1_funct_2(A_281,A_282,B_280)
      | k1_relset_1(A_282,B_280,A_281) != A_282
      | ~ r1_tarski(A_281,k2_zfmisc_1(A_282,B_280)) ) ),
    inference(resolution,[status(thm)],[c_26,c_1687])).

tff(c_2260,plain,(
    ! [A_243] :
      ( k1_xboole_0 = '#skF_4'
      | v1_funct_2('#skF_5',A_243,'#skF_4')
      | k1_relset_1(A_243,'#skF_4','#skF_5') != A_243
      | ~ r1_tarski('#skF_2',A_243) ) ),
    inference(resolution,[status(thm)],[c_1749,c_2254])).

tff(c_2317,plain,(
    ! [A_285] :
      ( v1_funct_2('#skF_5',A_285,'#skF_4')
      | k1_relset_1(A_285,'#skF_4','#skF_5') != A_285
      | ~ r1_tarski('#skF_2',A_285) ) ),
    inference(negUnitSimplification,[status(thm)],[c_2227,c_2260])).

tff(c_66,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_56,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_68,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4')))
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_56])).

tff(c_125,plain,(
    ~ v1_funct_2('#skF_5','#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_2330,plain,
    ( k1_relset_1('#skF_2','#skF_4','#skF_5') != '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_2317,c_125])).

tff(c_2338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1785,c_2330])).

tff(c_2340,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_1290])).

tff(c_8,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_2549,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2340,c_8])).

tff(c_2556,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_112])).

tff(c_16,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2560,plain,(
    ! [A_8] : r1_tarski('#skF_4',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_16])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2557,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_4',B_10) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2549,c_22])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2562,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2549,c_36])).

tff(c_2605,plain,(
    ! [A_302,B_303,C_304] :
      ( k1_relset_1(A_302,B_303,C_304) = k1_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_3045,plain,(
    ! [A_355,B_356,A_357] :
      ( k1_relset_1(A_355,B_356,A_357) = k1_relat_1(A_357)
      | ~ r1_tarski(A_357,k2_zfmisc_1(A_355,B_356)) ) ),
    inference(resolution,[status(thm)],[c_26,c_2605])).

tff(c_3055,plain,(
    ! [A_355,B_356] : k1_relset_1(A_355,B_356,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2560,c_3045])).

tff(c_3064,plain,(
    ! [A_355,B_356] : k1_relset_1(A_355,B_356,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_3055])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2558,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2549,c_20])).

tff(c_2614,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2605])).

tff(c_54,plain,(
    ! [B_31,A_30,C_32] :
      ( k1_xboole_0 = B_31
      | k1_relset_1(A_30,B_31,C_32) = A_30
      | ~ v1_funct_2(C_32,A_30,B_31)
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2903,plain,(
    ! [B_337,A_338,C_339] :
      ( B_337 = '#skF_4'
      | k1_relset_1(A_338,B_337,C_339) = A_338
      | ~ v1_funct_2(C_339,A_338,B_337)
      | ~ m1_subset_1(C_339,k1_zfmisc_1(k2_zfmisc_1(A_338,B_337))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_54])).

tff(c_2919,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2903])).

tff(c_2925,plain,
    ( '#skF_3' = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2614,c_2919])).

tff(c_2926,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_2556,c_2925])).

tff(c_2530,plain,(
    ! [A_297,B_298,C_299] :
      ( k2_relset_1(A_297,B_298,C_299) = k2_relat_1(C_299)
      | ~ m1_subset_1(C_299,k1_zfmisc_1(k2_zfmisc_1(A_297,B_298))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2545,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_62,c_2530])).

tff(c_2571,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2545,c_60])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2619,plain,
    ( k2_relat_1('#skF_5') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2571,c_10])).

tff(c_2628,plain,(
    k2_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2619])).

tff(c_2787,plain,(
    ! [C_321,A_322,B_323] :
      ( m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_322,B_323)))
      | ~ r1_tarski(k2_relat_1(C_321),B_323)
      | ~ r1_tarski(k1_relat_1(C_321),A_322)
      | ~ v1_relat_1(C_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3117,plain,(
    ! [C_366,A_367,B_368] :
      ( r1_tarski(C_366,k2_zfmisc_1(A_367,B_368))
      | ~ r1_tarski(k2_relat_1(C_366),B_368)
      | ~ r1_tarski(k1_relat_1(C_366),A_367)
      | ~ v1_relat_1(C_366) ) ),
    inference(resolution,[status(thm)],[c_2787,c_24])).

tff(c_3119,plain,(
    ! [A_367,B_368] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_367,B_368))
      | ~ r1_tarski('#skF_4',B_368)
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_367)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_3117])).

tff(c_3131,plain,(
    ! [A_369,B_370] :
      ( r1_tarski('#skF_5',k2_zfmisc_1(A_369,B_370))
      | ~ r1_tarski('#skF_2',A_369) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_2926,c_2560,c_3119])).

tff(c_3151,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_5','#skF_4')
      | ~ r1_tarski('#skF_2',A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2558,c_3131])).

tff(c_3162,plain,(
    ! [A_371] : ~ r1_tarski('#skF_2',A_371) ),
    inference(splitLeft,[status(thm)],[c_3151])).

tff(c_3167,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_3162])).

tff(c_3168,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3151])).

tff(c_1201,plain,(
    ! [B_166,A_167] :
      ( B_166 = A_167
      | ~ r1_tarski(B_166,A_167)
      | ~ r1_tarski(A_167,B_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1212,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_16,c_1201])).

tff(c_2553,plain,(
    ! [A_8] :
      ( A_8 = '#skF_4'
      | ~ r1_tarski(A_8,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2549,c_1212])).

tff(c_3196,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3168,c_2553])).

tff(c_2927,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2926,c_2614])).

tff(c_3208,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3196,c_2927])).

tff(c_3221,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3064,c_3208])).

tff(c_3102,plain,(
    ! [C_364,B_365] :
      ( m1_subset_1(C_364,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(C_364),B_365)
      | ~ r1_tarski(k1_relat_1(C_364),'#skF_4')
      | ~ v1_relat_1(C_364) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2557,c_2787])).

tff(c_3105,plain,(
    ! [B_365] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski('#skF_4',B_365)
      | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_3102])).

tff(c_3113,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_2926,c_2560,c_3105])).

tff(c_3130,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3113])).

tff(c_3242,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3221,c_3130])).

tff(c_3246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_3242])).

tff(c_3248,plain,(
    r1_tarski('#skF_2','#skF_4') ),
    inference(splitRight,[status(thm)],[c_3113])).

tff(c_3272,plain,(
    '#skF_2' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3248,c_2553])).

tff(c_127,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_62,c_127])).

tff(c_1210,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_135,c_1201])).

tff(c_2749,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1210])).

tff(c_3285,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_3'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_2749])).

tff(c_3295,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2560,c_2557,c_3285])).

tff(c_3296,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1210])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( k1_xboole_0 = B_10
      | k1_xboole_0 = A_9
      | k2_zfmisc_1(A_9,B_10) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2554,plain,(
    ! [B_10,A_9] :
      ( B_10 = '#skF_4'
      | A_9 = '#skF_4'
      | k2_zfmisc_1(A_9,B_10) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2549,c_2549,c_2549,c_18])).

tff(c_3305,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_2' = '#skF_4'
    | '#skF_5' != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3296,c_2554])).

tff(c_3316,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_5' != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2556,c_3305])).

tff(c_3333,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3316])).

tff(c_3528,plain,(
    ! [C_400,A_401,B_402] :
      ( m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_401,B_402)))
      | ~ r1_tarski(k2_relat_1(C_400),B_402)
      | ~ r1_tarski(k1_relat_1(C_400),A_401)
      | ~ v1_relat_1(C_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3781,plain,(
    ! [C_430,A_431] :
      ( m1_subset_1(C_430,k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k2_relat_1(C_430),'#skF_4')
      | ~ r1_tarski(k1_relat_1(C_430),A_431)
      | ~ v1_relat_1(C_430) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2558,c_3528])).

tff(c_3783,plain,(
    ! [A_431] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski('#skF_4','#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_431)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2628,c_3781])).

tff(c_3787,plain,(
    ! [A_431] :
      ( m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
      | ~ r1_tarski(k1_relat_1('#skF_5'),A_431) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_2560,c_3783])).

tff(c_3813,plain,(
    ! [A_435] : ~ r1_tarski(k1_relat_1('#skF_5'),A_435) ),
    inference(splitLeft,[status(thm)],[c_3787])).

tff(c_3818,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_3813])).

tff(c_3819,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3787])).

tff(c_3851,plain,(
    r1_tarski('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_3819,c_24])).

tff(c_3885,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3851,c_2553])).

tff(c_3905,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3333,c_3885])).

tff(c_3907,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3316])).

tff(c_1236,plain,(
    ! [A_171] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3'))
      | ~ r2_hidden(A_171,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_62,c_1230])).

tff(c_1270,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1236])).

tff(c_3298,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3296,c_1270])).

tff(c_3919,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3907,c_3298])).

tff(c_3926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2340,c_3919])).

tff(c_3929,plain,(
    ! [A_437] : ~ r2_hidden(A_437,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_3934,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_4,c_3929])).

tff(c_3939,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3934,c_8])).

tff(c_3946,plain,(
    '#skF_5' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_112])).

tff(c_3928,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1236])).

tff(c_3979,plain,(
    ! [A_440] :
      ( A_440 = '#skF_5'
      | ~ v1_xboole_0(A_440) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_8])).

tff(c_3986,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_3928,c_3979])).

tff(c_4109,plain,(
    ! [B_455,A_456] :
      ( B_455 = '#skF_5'
      | A_456 = '#skF_5'
      | k2_zfmisc_1(A_456,B_455) != '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_3939,c_3939,c_18])).

tff(c_4112,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_3986,c_4109])).

tff(c_4121,plain,(
    '#skF_5' = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_3946,c_4112])).

tff(c_3952,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_3939,c_36])).

tff(c_4140,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4121,c_4121,c_3952])).

tff(c_44,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_30,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_71,plain,(
    ! [A_30] :
      ( v1_funct_2(k1_xboole_0,A_30,k1_xboole_0)
      | k1_xboole_0 = A_30
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_44])).

tff(c_1237,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_71])).

tff(c_1240,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_26,c_1237])).

tff(c_1244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_1240])).

tff(c_1246,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_71])).

tff(c_3942,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_3939,c_1246])).

tff(c_4136,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4121,c_4121,c_3942])).

tff(c_3947,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_5',B_10) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3939,c_3939,c_22])).

tff(c_4258,plain,(
    ! [B_466] : k2_zfmisc_1('#skF_2',B_466) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4121,c_4121,c_3947])).

tff(c_38,plain,(
    ! [A_21,B_22,C_23] :
      ( k1_relset_1(A_21,B_22,C_23) = k1_relat_1(C_23)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_4504,plain,(
    ! [B_496,C_497] :
      ( k1_relset_1('#skF_2',B_496,C_497) = k1_relat_1(C_497)
      | ~ m1_subset_1(C_497,k1_zfmisc_1('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4258,c_38])).

tff(c_4506,plain,(
    ! [B_496] : k1_relset_1('#skF_2',B_496,'#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4136,c_4504])).

tff(c_4511,plain,(
    ! [B_496] : k1_relset_1('#skF_2',B_496,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4140,c_4506])).

tff(c_4143,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4121,c_3939])).

tff(c_48,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70,plain,(
    ! [C_32,B_31] :
      ( v1_funct_2(C_32,k1_xboole_0,B_31)
      | k1_relset_1(k1_xboole_0,B_31,C_32) != k1_xboole_0
      | ~ m1_subset_1(C_32,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_48])).

tff(c_4226,plain,(
    ! [C_463,B_464] :
      ( v1_funct_2(C_463,'#skF_2',B_464)
      | k1_relset_1('#skF_2',B_464,C_463) != '#skF_2'
      | ~ m1_subset_1(C_463,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4143,c_4143,c_4143,c_4143,c_70])).

tff(c_4325,plain,(
    ! [B_473] :
      ( v1_funct_2('#skF_2','#skF_2',B_473)
      | k1_relset_1('#skF_2',B_473,'#skF_2') != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_4136,c_4226])).

tff(c_4147,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4121,c_125])).

tff(c_4334,plain,(
    k1_relset_1('#skF_2','#skF_4','#skF_2') != '#skF_2' ),
    inference(resolution,[status(thm)],[c_4325,c_4147])).

tff(c_4536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4511,c_4334])).

tff(c_4537,plain,(
    ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4805,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_4788,c_4537])).

tff(c_4821,plain,(
    ~ r1_tarski(k1_relat_1('#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4590,c_4729,c_4805])).

tff(c_4926,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4924,c_4821])).

tff(c_4930,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4926])).

tff(c_4932,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4931,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_4944,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4932,c_4931])).

tff(c_4938,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4931,c_4931,c_36])).

tff(c_4954,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4944,c_4944,c_4938])).

tff(c_4936,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4931,c_16])).

tff(c_4959,plain,(
    ! [A_8] : r1_tarski('#skF_3',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4944,c_4936])).

tff(c_5160,plain,(
    ! [A_590,B_591,C_592] :
      ( k1_relset_1(A_590,B_591,C_592) = k1_relat_1(C_592)
      | ~ m1_subset_1(C_592,k1_zfmisc_1(k2_zfmisc_1(A_590,B_591))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5234,plain,(
    ! [A_603,B_604,A_605] :
      ( k1_relset_1(A_603,B_604,A_605) = k1_relat_1(A_605)
      | ~ r1_tarski(A_605,k2_zfmisc_1(A_603,B_604)) ) ),
    inference(resolution,[status(thm)],[c_26,c_5160])).

tff(c_5244,plain,(
    ! [A_603,B_604] : k1_relset_1(A_603,B_604,'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4959,c_5234])).

tff(c_5250,plain,(
    ! [A_603,B_604] : k1_relset_1(A_603,B_604,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4954,c_5244])).

tff(c_4934,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4931,c_4931,c_20])).

tff(c_4968,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4944,c_4944,c_4934])).

tff(c_5005,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4968,c_4944,c_62])).

tff(c_5015,plain,(
    ! [A_569,B_570] :
      ( r1_tarski(A_569,B_570)
      | ~ m1_subset_1(A_569,k1_zfmisc_1(B_570)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_5023,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_5005,c_5015])).

tff(c_5036,plain,(
    ! [B_573,A_574] :
      ( B_573 = A_574
      | ~ r1_tarski(B_573,A_574)
      | ~ r1_tarski(A_574,B_573) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5038,plain,
    ( '#skF_5' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_5023,c_5036])).

tff(c_5047,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4959,c_5038])).

tff(c_5069,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5047,c_5005])).

tff(c_5372,plain,(
    ! [C_625,B_626] :
      ( v1_funct_2(C_625,'#skF_3',B_626)
      | k1_relset_1('#skF_3',B_626,C_625) != '#skF_3'
      | ~ m1_subset_1(C_625,k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4932,c_4932,c_4932,c_4932,c_70])).

tff(c_5374,plain,(
    ! [B_626] :
      ( v1_funct_2('#skF_3','#skF_3',B_626)
      | k1_relset_1('#skF_3',B_626,'#skF_3') != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_5069,c_5372])).

tff(c_5380,plain,(
    ! [B_626] : v1_funct_2('#skF_3','#skF_3',B_626) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5250,c_5374])).

tff(c_4933,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_2',B_10) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4931,c_4931,c_22])).

tff(c_4978,plain,(
    ! [B_10] : k2_zfmisc_1('#skF_3',B_10) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4944,c_4944,c_4933])).

tff(c_5013,plain,(
    ~ v1_funct_2('#skF_5','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4944,c_5005,c_4978,c_4944,c_68])).

tff(c_5067,plain,(
    ~ v1_funct_2('#skF_3','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5047,c_5013])).

tff(c_5385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5380,c_5067])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.37/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.09  
% 5.77/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.77/2.09  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.77/2.09  
% 5.77/2.09  %Foreground sorts:
% 5.77/2.09  
% 5.77/2.09  
% 5.77/2.09  %Background operators:
% 5.77/2.09  
% 5.77/2.09  
% 5.77/2.09  %Foreground operators:
% 5.77/2.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 5.77/2.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.77/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.77/2.09  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.77/2.09  tff('#skF_1', type, '#skF_1': $i > $i).
% 5.77/2.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.77/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.77/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.77/2.09  tff('#skF_5', type, '#skF_5': $i).
% 5.77/2.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.77/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.77/2.09  tff('#skF_3', type, '#skF_3': $i).
% 5.77/2.09  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.77/2.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.77/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.77/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.77/2.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.77/2.09  tff('#skF_4', type, '#skF_4': $i).
% 5.77/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.77/2.09  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.77/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.77/2.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.77/2.09  
% 5.97/2.13  tff(f_42, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.97/2.13  tff(f_127, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_funct_2)).
% 5.97/2.13  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.97/2.13  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 5.97/2.13  tff(f_70, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.97/2.13  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.97/2.13  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 5.97/2.13  tff(f_89, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 5.97/2.13  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 5.97/2.13  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 5.97/2.13  tff(f_61, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 5.97/2.13  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 5.97/2.13  tff(f_36, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 5.97/2.13  tff(f_44, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.97/2.13  tff(f_50, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.97/2.13  tff(f_73, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 5.97/2.13  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.13  tff(c_58, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.97/2.13  tff(c_112, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_58])).
% 5.97/2.13  tff(c_64, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.97/2.13  tff(c_62, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.97/2.13  tff(c_4691, plain, (![A_524, B_525, C_526]: (k1_relset_1(A_524, B_525, C_526)=k1_relat_1(C_526) | ~m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(A_524, B_525))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.97/2.13  tff(c_4706, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_4691])).
% 5.97/2.13  tff(c_4902, plain, (![B_555, A_556, C_557]: (k1_xboole_0=B_555 | k1_relset_1(A_556, B_555, C_557)=A_556 | ~v1_funct_2(C_557, A_556, B_555) | ~m1_subset_1(C_557, k1_zfmisc_1(k2_zfmisc_1(A_556, B_555))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.97/2.13  tff(c_4912, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_4902])).
% 5.97/2.13  tff(c_4923, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4706, c_4912])).
% 5.97/2.13  tff(c_4924, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_112, c_4923])).
% 5.97/2.13  tff(c_32, plain, (![A_19, B_20]: (v1_relat_1(k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.97/2.13  tff(c_4580, plain, (![B_509, A_510]: (v1_relat_1(B_509) | ~m1_subset_1(B_509, k1_zfmisc_1(A_510)) | ~v1_relat_1(A_510))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.97/2.13  tff(c_4586, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_4580])).
% 5.97/2.13  tff(c_4590, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_4586])).
% 5.97/2.13  tff(c_4712, plain, (![A_527, B_528, C_529]: (k2_relset_1(A_527, B_528, C_529)=k2_relat_1(C_529) | ~m1_subset_1(C_529, k1_zfmisc_1(k2_zfmisc_1(A_527, B_528))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.97/2.13  tff(c_4727, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_4712])).
% 5.97/2.13  tff(c_60, plain, (r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.97/2.13  tff(c_4729, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4727, c_60])).
% 5.97/2.13  tff(c_4788, plain, (![C_539, A_540, B_541]: (m1_subset_1(C_539, k1_zfmisc_1(k2_zfmisc_1(A_540, B_541))) | ~r1_tarski(k2_relat_1(C_539), B_541) | ~r1_tarski(k1_relat_1(C_539), A_540) | ~v1_relat_1(C_539))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.97/2.13  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.97/2.13  tff(c_1341, plain, (![A_184, B_185, C_186]: (k1_relset_1(A_184, B_185, C_186)=k1_relat_1(C_186) | ~m1_subset_1(C_186, k1_zfmisc_1(k2_zfmisc_1(A_184, B_185))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.97/2.13  tff(c_1356, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_1341])).
% 5.97/2.13  tff(c_1628, plain, (![B_228, A_229, C_230]: (k1_xboole_0=B_228 | k1_relset_1(A_229, B_228, C_230)=A_229 | ~v1_funct_2(C_230, A_229, B_228) | ~m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_229, B_228))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.97/2.13  tff(c_1638, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_1628])).
% 5.97/2.13  tff(c_1649, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1356, c_1638])).
% 5.97/2.13  tff(c_1650, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_112, c_1649])).
% 5.97/2.13  tff(c_147, plain, (![B_49, A_50]: (v1_relat_1(B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_50)) | ~v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.97/2.13  tff(c_153, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_147])).
% 5.97/2.13  tff(c_157, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_153])).
% 5.97/2.13  tff(c_1295, plain, (![A_179, B_180, C_181]: (k2_relset_1(A_179, B_180, C_181)=k2_relat_1(C_181) | ~m1_subset_1(C_181, k1_zfmisc_1(k2_zfmisc_1(A_179, B_180))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.97/2.13  tff(c_1310, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_1295])).
% 5.97/2.13  tff(c_1312, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_60])).
% 5.97/2.13  tff(c_1473, plain, (![C_205, A_206, B_207]: (m1_subset_1(C_205, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~r1_tarski(k2_relat_1(C_205), B_207) | ~r1_tarski(k1_relat_1(C_205), A_206) | ~v1_relat_1(C_205))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.97/2.13  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.97/2.13  tff(c_1739, plain, (![C_242, A_243, B_244]: (r1_tarski(C_242, k2_zfmisc_1(A_243, B_244)) | ~r1_tarski(k2_relat_1(C_242), B_244) | ~r1_tarski(k1_relat_1(C_242), A_243) | ~v1_relat_1(C_242))), inference(resolution, [status(thm)], [c_1473, c_24])).
% 5.97/2.13  tff(c_1741, plain, (![A_243]: (r1_tarski('#skF_5', k2_zfmisc_1(A_243, '#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_243) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_1312, c_1739])).
% 5.97/2.13  tff(c_1753, plain, (![A_245]: (r1_tarski('#skF_5', k2_zfmisc_1(A_245, '#skF_4')) | ~r1_tarski('#skF_2', A_245))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1650, c_1741])).
% 5.97/2.13  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.97/2.13  tff(c_1355, plain, (![A_184, B_185, A_11]: (k1_relset_1(A_184, B_185, A_11)=k1_relat_1(A_11) | ~r1_tarski(A_11, k2_zfmisc_1(A_184, B_185)))), inference(resolution, [status(thm)], [c_26, c_1341])).
% 5.97/2.13  tff(c_1756, plain, (![A_245]: (k1_relset_1(A_245, '#skF_4', '#skF_5')=k1_relat_1('#skF_5') | ~r1_tarski('#skF_2', A_245))), inference(resolution, [status(thm)], [c_1753, c_1355])).
% 5.97/2.13  tff(c_1780, plain, (![A_246]: (k1_relset_1(A_246, '#skF_4', '#skF_5')='#skF_2' | ~r1_tarski('#skF_2', A_246))), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_1756])).
% 5.97/2.13  tff(c_1785, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_1780])).
% 5.97/2.13  tff(c_1230, plain, (![C_169, B_170, A_171]: (~v1_xboole_0(C_169) | ~m1_subset_1(B_170, k1_zfmisc_1(C_169)) | ~r2_hidden(A_171, B_170))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.97/2.13  tff(c_1272, plain, (![B_174, A_175, A_176]: (~v1_xboole_0(B_174) | ~r2_hidden(A_175, A_176) | ~r1_tarski(A_176, B_174))), inference(resolution, [status(thm)], [c_26, c_1230])).
% 5.97/2.13  tff(c_1276, plain, (![B_177, A_178]: (~v1_xboole_0(B_177) | ~r1_tarski(A_178, B_177) | v1_xboole_0(A_178))), inference(resolution, [status(thm)], [c_4, c_1272])).
% 5.97/2.13  tff(c_1290, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_1276])).
% 5.97/2.13  tff(c_1294, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_1290])).
% 5.97/2.13  tff(c_1749, plain, (![A_243]: (r1_tarski('#skF_5', k2_zfmisc_1(A_243, '#skF_4')) | ~r1_tarski('#skF_2', A_243))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_1650, c_1741])).
% 5.97/2.13  tff(c_2112, plain, (![B_270, A_271, A_272]: (k1_xboole_0=B_270 | k1_relset_1(A_271, B_270, A_272)=A_271 | ~v1_funct_2(A_272, A_271, B_270) | ~r1_tarski(A_272, k2_zfmisc_1(A_271, B_270)))), inference(resolution, [status(thm)], [c_26, c_1628])).
% 5.97/2.13  tff(c_2137, plain, (![A_243]: (k1_xboole_0='#skF_4' | k1_relset_1(A_243, '#skF_4', '#skF_5')=A_243 | ~v1_funct_2('#skF_5', A_243, '#skF_4') | ~r1_tarski('#skF_2', A_243))), inference(resolution, [status(thm)], [c_1749, c_2112])).
% 5.97/2.13  tff(c_2183, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2137])).
% 5.97/2.13  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.97/2.13  tff(c_2222, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2183, c_6])).
% 5.97/2.13  tff(c_2225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1294, c_2222])).
% 5.97/2.13  tff(c_2227, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2137])).
% 5.97/2.13  tff(c_1687, plain, (![B_236, C_237, A_238]: (k1_xboole_0=B_236 | v1_funct_2(C_237, A_238, B_236) | k1_relset_1(A_238, B_236, C_237)!=A_238 | ~m1_subset_1(C_237, k1_zfmisc_1(k2_zfmisc_1(A_238, B_236))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.97/2.13  tff(c_2254, plain, (![B_280, A_281, A_282]: (k1_xboole_0=B_280 | v1_funct_2(A_281, A_282, B_280) | k1_relset_1(A_282, B_280, A_281)!=A_282 | ~r1_tarski(A_281, k2_zfmisc_1(A_282, B_280)))), inference(resolution, [status(thm)], [c_26, c_1687])).
% 5.97/2.13  tff(c_2260, plain, (![A_243]: (k1_xboole_0='#skF_4' | v1_funct_2('#skF_5', A_243, '#skF_4') | k1_relset_1(A_243, '#skF_4', '#skF_5')!=A_243 | ~r1_tarski('#skF_2', A_243))), inference(resolution, [status(thm)], [c_1749, c_2254])).
% 5.97/2.13  tff(c_2317, plain, (![A_285]: (v1_funct_2('#skF_5', A_285, '#skF_4') | k1_relset_1(A_285, '#skF_4', '#skF_5')!=A_285 | ~r1_tarski('#skF_2', A_285))), inference(negUnitSimplification, [status(thm)], [c_2227, c_2260])).
% 5.97/2.13  tff(c_66, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.97/2.13  tff(c_56, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4') | ~v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_127])).
% 5.97/2.13  tff(c_68, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4'))) | ~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_56])).
% 5.97/2.13  tff(c_125, plain, (~v1_funct_2('#skF_5', '#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_68])).
% 5.97/2.13  tff(c_2330, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_5')!='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_2317, c_125])).
% 5.97/2.13  tff(c_2338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1785, c_2330])).
% 5.97/2.13  tff(c_2340, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_1290])).
% 5.97/2.13  tff(c_8, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_36])).
% 5.97/2.13  tff(c_2549, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_2340, c_8])).
% 5.97/2.13  tff(c_2556, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_112])).
% 5.97/2.13  tff(c_16, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.97/2.13  tff(c_2560, plain, (![A_8]: (r1_tarski('#skF_4', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_16])).
% 5.97/2.13  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.97/2.13  tff(c_2557, plain, (![B_10]: (k2_zfmisc_1('#skF_4', B_10)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2549, c_22])).
% 5.97/2.13  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.97/2.13  tff(c_2562, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2549, c_36])).
% 5.97/2.13  tff(c_2605, plain, (![A_302, B_303, C_304]: (k1_relset_1(A_302, B_303, C_304)=k1_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.97/2.13  tff(c_3045, plain, (![A_355, B_356, A_357]: (k1_relset_1(A_355, B_356, A_357)=k1_relat_1(A_357) | ~r1_tarski(A_357, k2_zfmisc_1(A_355, B_356)))), inference(resolution, [status(thm)], [c_26, c_2605])).
% 5.97/2.13  tff(c_3055, plain, (![A_355, B_356]: (k1_relset_1(A_355, B_356, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_2560, c_3045])).
% 5.97/2.13  tff(c_3064, plain, (![A_355, B_356]: (k1_relset_1(A_355, B_356, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_3055])).
% 5.97/2.13  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.97/2.13  tff(c_2558, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2549, c_20])).
% 5.97/2.13  tff(c_2614, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2605])).
% 5.97/2.13  tff(c_54, plain, (![B_31, A_30, C_32]: (k1_xboole_0=B_31 | k1_relset_1(A_30, B_31, C_32)=A_30 | ~v1_funct_2(C_32, A_30, B_31) | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.97/2.13  tff(c_2903, plain, (![B_337, A_338, C_339]: (B_337='#skF_4' | k1_relset_1(A_338, B_337, C_339)=A_338 | ~v1_funct_2(C_339, A_338, B_337) | ~m1_subset_1(C_339, k1_zfmisc_1(k2_zfmisc_1(A_338, B_337))))), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_54])).
% 5.97/2.13  tff(c_2919, plain, ('#skF_3'='#skF_4' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_62, c_2903])).
% 5.97/2.13  tff(c_2925, plain, ('#skF_3'='#skF_4' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2614, c_2919])).
% 5.97/2.13  tff(c_2926, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_2556, c_2925])).
% 5.97/2.13  tff(c_2530, plain, (![A_297, B_298, C_299]: (k2_relset_1(A_297, B_298, C_299)=k2_relat_1(C_299) | ~m1_subset_1(C_299, k1_zfmisc_1(k2_zfmisc_1(A_297, B_298))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 5.97/2.13  tff(c_2545, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_62, c_2530])).
% 5.97/2.13  tff(c_2571, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2545, c_60])).
% 5.97/2.13  tff(c_10, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.13  tff(c_2619, plain, (k2_relat_1('#skF_5')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2571, c_10])).
% 5.97/2.13  tff(c_2628, plain, (k2_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2619])).
% 5.97/2.13  tff(c_2787, plain, (![C_321, A_322, B_323]: (m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))) | ~r1_tarski(k2_relat_1(C_321), B_323) | ~r1_tarski(k1_relat_1(C_321), A_322) | ~v1_relat_1(C_321))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.97/2.13  tff(c_3117, plain, (![C_366, A_367, B_368]: (r1_tarski(C_366, k2_zfmisc_1(A_367, B_368)) | ~r1_tarski(k2_relat_1(C_366), B_368) | ~r1_tarski(k1_relat_1(C_366), A_367) | ~v1_relat_1(C_366))), inference(resolution, [status(thm)], [c_2787, c_24])).
% 5.97/2.13  tff(c_3119, plain, (![A_367, B_368]: (r1_tarski('#skF_5', k2_zfmisc_1(A_367, B_368)) | ~r1_tarski('#skF_4', B_368) | ~r1_tarski(k1_relat_1('#skF_5'), A_367) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2628, c_3117])).
% 5.97/2.13  tff(c_3131, plain, (![A_369, B_370]: (r1_tarski('#skF_5', k2_zfmisc_1(A_369, B_370)) | ~r1_tarski('#skF_2', A_369))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_2926, c_2560, c_3119])).
% 5.97/2.13  tff(c_3151, plain, (![A_9]: (r1_tarski('#skF_5', '#skF_4') | ~r1_tarski('#skF_2', A_9))), inference(superposition, [status(thm), theory('equality')], [c_2558, c_3131])).
% 5.97/2.13  tff(c_3162, plain, (![A_371]: (~r1_tarski('#skF_2', A_371))), inference(splitLeft, [status(thm)], [c_3151])).
% 5.97/2.13  tff(c_3167, plain, $false, inference(resolution, [status(thm)], [c_14, c_3162])).
% 5.97/2.13  tff(c_3168, plain, (r1_tarski('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_3151])).
% 5.97/2.13  tff(c_1201, plain, (![B_166, A_167]: (B_166=A_167 | ~r1_tarski(B_166, A_167) | ~r1_tarski(A_167, B_166))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.13  tff(c_1212, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(resolution, [status(thm)], [c_16, c_1201])).
% 5.97/2.13  tff(c_2553, plain, (![A_8]: (A_8='#skF_4' | ~r1_tarski(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2549, c_1212])).
% 5.97/2.13  tff(c_3196, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3168, c_2553])).
% 5.97/2.13  tff(c_2927, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2926, c_2614])).
% 5.97/2.13  tff(c_3208, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3196, c_2927])).
% 5.97/2.13  tff(c_3221, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3064, c_3208])).
% 5.97/2.13  tff(c_3102, plain, (![C_364, B_365]: (m1_subset_1(C_364, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(C_364), B_365) | ~r1_tarski(k1_relat_1(C_364), '#skF_4') | ~v1_relat_1(C_364))), inference(superposition, [status(thm), theory('equality')], [c_2557, c_2787])).
% 5.97/2.13  tff(c_3105, plain, (![B_365]: (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_4', B_365) | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2628, c_3102])).
% 5.97/2.13  tff(c_3113, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_2926, c_2560, c_3105])).
% 5.97/2.13  tff(c_3130, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(splitLeft, [status(thm)], [c_3113])).
% 5.97/2.13  tff(c_3242, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3221, c_3130])).
% 5.97/2.13  tff(c_3246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2560, c_3242])).
% 5.97/2.13  tff(c_3248, plain, (r1_tarski('#skF_2', '#skF_4')), inference(splitRight, [status(thm)], [c_3113])).
% 5.97/2.13  tff(c_3272, plain, ('#skF_2'='#skF_4'), inference(resolution, [status(thm)], [c_3248, c_2553])).
% 5.97/2.13  tff(c_127, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.97/2.13  tff(c_135, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_62, c_127])).
% 5.97/2.13  tff(c_1210, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_135, c_1201])).
% 5.97/2.13  tff(c_2749, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1210])).
% 5.97/2.13  tff(c_3285, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_3'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_2749])).
% 5.97/2.13  tff(c_3295, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2560, c_2557, c_3285])).
% 5.97/2.13  tff(c_3296, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(splitRight, [status(thm)], [c_1210])).
% 5.97/2.13  tff(c_18, plain, (![B_10, A_9]: (k1_xboole_0=B_10 | k1_xboole_0=A_9 | k2_zfmisc_1(A_9, B_10)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.97/2.13  tff(c_2554, plain, (![B_10, A_9]: (B_10='#skF_4' | A_9='#skF_4' | k2_zfmisc_1(A_9, B_10)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2549, c_2549, c_2549, c_18])).
% 5.97/2.13  tff(c_3305, plain, ('#skF_3'='#skF_4' | '#skF_2'='#skF_4' | '#skF_5'!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3296, c_2554])).
% 5.97/2.13  tff(c_3316, plain, ('#skF_2'='#skF_4' | '#skF_5'!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2556, c_3305])).
% 5.97/2.13  tff(c_3333, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_3316])).
% 5.97/2.13  tff(c_3528, plain, (![C_400, A_401, B_402]: (m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_401, B_402))) | ~r1_tarski(k2_relat_1(C_400), B_402) | ~r1_tarski(k1_relat_1(C_400), A_401) | ~v1_relat_1(C_400))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.97/2.13  tff(c_3781, plain, (![C_430, A_431]: (m1_subset_1(C_430, k1_zfmisc_1('#skF_4')) | ~r1_tarski(k2_relat_1(C_430), '#skF_4') | ~r1_tarski(k1_relat_1(C_430), A_431) | ~v1_relat_1(C_430))), inference(superposition, [status(thm), theory('equality')], [c_2558, c_3528])).
% 5.97/2.13  tff(c_3783, plain, (![A_431]: (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~r1_tarski('#skF_4', '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), A_431) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2628, c_3781])).
% 5.97/2.13  tff(c_3787, plain, (![A_431]: (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | ~r1_tarski(k1_relat_1('#skF_5'), A_431))), inference(demodulation, [status(thm), theory('equality')], [c_157, c_2560, c_3783])).
% 5.97/2.13  tff(c_3813, plain, (![A_435]: (~r1_tarski(k1_relat_1('#skF_5'), A_435))), inference(splitLeft, [status(thm)], [c_3787])).
% 5.97/2.13  tff(c_3818, plain, $false, inference(resolution, [status(thm)], [c_14, c_3813])).
% 5.97/2.13  tff(c_3819, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_3787])).
% 5.97/2.13  tff(c_3851, plain, (r1_tarski('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_3819, c_24])).
% 5.97/2.13  tff(c_3885, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_3851, c_2553])).
% 5.97/2.13  tff(c_3905, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3333, c_3885])).
% 5.97/2.13  tff(c_3907, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_3316])).
% 5.97/2.13  tff(c_1236, plain, (![A_171]: (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3')) | ~r2_hidden(A_171, '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_1230])).
% 5.97/2.13  tff(c_1270, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1236])).
% 5.97/2.13  tff(c_3298, plain, (~v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3296, c_1270])).
% 5.97/2.13  tff(c_3919, plain, (~v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3907, c_3298])).
% 5.97/2.13  tff(c_3926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2340, c_3919])).
% 5.97/2.13  tff(c_3929, plain, (![A_437]: (~r2_hidden(A_437, '#skF_5'))), inference(splitRight, [status(thm)], [c_1236])).
% 5.97/2.13  tff(c_3934, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_4, c_3929])).
% 5.97/2.13  tff(c_3939, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_3934, c_8])).
% 5.97/2.13  tff(c_3946, plain, ('#skF_5'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_112])).
% 5.97/2.13  tff(c_3928, plain, (v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1236])).
% 5.97/2.13  tff(c_3979, plain, (![A_440]: (A_440='#skF_5' | ~v1_xboole_0(A_440))), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_8])).
% 5.97/2.13  tff(c_3986, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_3928, c_3979])).
% 5.97/2.13  tff(c_4109, plain, (![B_455, A_456]: (B_455='#skF_5' | A_456='#skF_5' | k2_zfmisc_1(A_456, B_455)!='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_3939, c_3939, c_18])).
% 5.97/2.13  tff(c_4112, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_3986, c_4109])).
% 5.97/2.13  tff(c_4121, plain, ('#skF_5'='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_3946, c_4112])).
% 5.97/2.13  tff(c_3952, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_3939, c_36])).
% 5.97/2.13  tff(c_4140, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4121, c_4121, c_3952])).
% 5.97/2.13  tff(c_44, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_30, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.97/2.13  tff(c_71, plain, (![A_30]: (v1_funct_2(k1_xboole_0, A_30, k1_xboole_0) | k1_xboole_0=A_30 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_44])).
% 5.97/2.13  tff(c_1237, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_71])).
% 5.97/2.13  tff(c_1240, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_1237])).
% 5.97/2.13  tff(c_1244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_1240])).
% 5.97/2.13  tff(c_1246, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_71])).
% 5.97/2.13  tff(c_3942, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_3939, c_1246])).
% 5.97/2.13  tff(c_4136, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4121, c_4121, c_3942])).
% 5.97/2.13  tff(c_3947, plain, (![B_10]: (k2_zfmisc_1('#skF_5', B_10)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3939, c_3939, c_22])).
% 5.97/2.13  tff(c_4258, plain, (![B_466]: (k2_zfmisc_1('#skF_2', B_466)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4121, c_4121, c_3947])).
% 5.97/2.13  tff(c_38, plain, (![A_21, B_22, C_23]: (k1_relset_1(A_21, B_22, C_23)=k1_relat_1(C_23) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.97/2.13  tff(c_4504, plain, (![B_496, C_497]: (k1_relset_1('#skF_2', B_496, C_497)=k1_relat_1(C_497) | ~m1_subset_1(C_497, k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_4258, c_38])).
% 5.97/2.13  tff(c_4506, plain, (![B_496]: (k1_relset_1('#skF_2', B_496, '#skF_2')=k1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_4136, c_4504])).
% 5.97/2.13  tff(c_4511, plain, (![B_496]: (k1_relset_1('#skF_2', B_496, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4140, c_4506])).
% 5.97/2.13  tff(c_4143, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4121, c_3939])).
% 5.97/2.13  tff(c_48, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_31))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 5.97/2.13  tff(c_70, plain, (![C_32, B_31]: (v1_funct_2(C_32, k1_xboole_0, B_31) | k1_relset_1(k1_xboole_0, B_31, C_32)!=k1_xboole_0 | ~m1_subset_1(C_32, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_48])).
% 5.97/2.13  tff(c_4226, plain, (![C_463, B_464]: (v1_funct_2(C_463, '#skF_2', B_464) | k1_relset_1('#skF_2', B_464, C_463)!='#skF_2' | ~m1_subset_1(C_463, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4143, c_4143, c_4143, c_4143, c_70])).
% 5.97/2.13  tff(c_4325, plain, (![B_473]: (v1_funct_2('#skF_2', '#skF_2', B_473) | k1_relset_1('#skF_2', B_473, '#skF_2')!='#skF_2')), inference(resolution, [status(thm)], [c_4136, c_4226])).
% 5.97/2.13  tff(c_4147, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4121, c_125])).
% 5.97/2.13  tff(c_4334, plain, (k1_relset_1('#skF_2', '#skF_4', '#skF_2')!='#skF_2'), inference(resolution, [status(thm)], [c_4325, c_4147])).
% 5.97/2.13  tff(c_4536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4511, c_4334])).
% 5.97/2.13  tff(c_4537, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_4')))), inference(splitRight, [status(thm)], [c_68])).
% 5.97/2.13  tff(c_4805, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | ~r1_tarski(k1_relat_1('#skF_5'), '#skF_2') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_4788, c_4537])).
% 5.97/2.13  tff(c_4821, plain, (~r1_tarski(k1_relat_1('#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4590, c_4729, c_4805])).
% 5.97/2.13  tff(c_4926, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4924, c_4821])).
% 5.97/2.13  tff(c_4930, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_4926])).
% 5.97/2.13  tff(c_4932, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_58])).
% 5.97/2.13  tff(c_4931, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 5.97/2.13  tff(c_4944, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4932, c_4931])).
% 5.97/2.13  tff(c_4938, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4931, c_4931, c_36])).
% 5.97/2.13  tff(c_4954, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4944, c_4944, c_4938])).
% 5.97/2.13  tff(c_4936, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4931, c_16])).
% 5.97/2.13  tff(c_4959, plain, (![A_8]: (r1_tarski('#skF_3', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_4944, c_4936])).
% 5.97/2.13  tff(c_5160, plain, (![A_590, B_591, C_592]: (k1_relset_1(A_590, B_591, C_592)=k1_relat_1(C_592) | ~m1_subset_1(C_592, k1_zfmisc_1(k2_zfmisc_1(A_590, B_591))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 5.97/2.13  tff(c_5234, plain, (![A_603, B_604, A_605]: (k1_relset_1(A_603, B_604, A_605)=k1_relat_1(A_605) | ~r1_tarski(A_605, k2_zfmisc_1(A_603, B_604)))), inference(resolution, [status(thm)], [c_26, c_5160])).
% 5.97/2.13  tff(c_5244, plain, (![A_603, B_604]: (k1_relset_1(A_603, B_604, '#skF_3')=k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_4959, c_5234])).
% 5.97/2.13  tff(c_5250, plain, (![A_603, B_604]: (k1_relset_1(A_603, B_604, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4954, c_5244])).
% 5.97/2.13  tff(c_4934, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4931, c_4931, c_20])).
% 5.97/2.13  tff(c_4968, plain, (![A_9]: (k2_zfmisc_1(A_9, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4944, c_4944, c_4934])).
% 5.97/2.13  tff(c_5005, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4968, c_4944, c_62])).
% 5.97/2.13  tff(c_5015, plain, (![A_569, B_570]: (r1_tarski(A_569, B_570) | ~m1_subset_1(A_569, k1_zfmisc_1(B_570)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.97/2.13  tff(c_5023, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_5005, c_5015])).
% 5.97/2.13  tff(c_5036, plain, (![B_573, A_574]: (B_573=A_574 | ~r1_tarski(B_573, A_574) | ~r1_tarski(A_574, B_573))), inference(cnfTransformation, [status(thm)], [f_42])).
% 5.97/2.13  tff(c_5038, plain, ('#skF_5'='#skF_3' | ~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_5023, c_5036])).
% 5.97/2.13  tff(c_5047, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4959, c_5038])).
% 5.97/2.13  tff(c_5069, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5047, c_5005])).
% 5.97/2.13  tff(c_5372, plain, (![C_625, B_626]: (v1_funct_2(C_625, '#skF_3', B_626) | k1_relset_1('#skF_3', B_626, C_625)!='#skF_3' | ~m1_subset_1(C_625, k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_4932, c_4932, c_4932, c_4932, c_70])).
% 5.97/2.13  tff(c_5374, plain, (![B_626]: (v1_funct_2('#skF_3', '#skF_3', B_626) | k1_relset_1('#skF_3', B_626, '#skF_3')!='#skF_3')), inference(resolution, [status(thm)], [c_5069, c_5372])).
% 5.97/2.13  tff(c_5380, plain, (![B_626]: (v1_funct_2('#skF_3', '#skF_3', B_626))), inference(demodulation, [status(thm), theory('equality')], [c_5250, c_5374])).
% 5.97/2.13  tff(c_4933, plain, (![B_10]: (k2_zfmisc_1('#skF_2', B_10)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4931, c_4931, c_22])).
% 5.97/2.13  tff(c_4978, plain, (![B_10]: (k2_zfmisc_1('#skF_3', B_10)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4944, c_4944, c_4933])).
% 5.97/2.13  tff(c_5013, plain, (~v1_funct_2('#skF_5', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4944, c_5005, c_4978, c_4944, c_68])).
% 5.97/2.13  tff(c_5067, plain, (~v1_funct_2('#skF_3', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5047, c_5013])).
% 5.97/2.13  tff(c_5385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5380, c_5067])).
% 5.97/2.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.97/2.13  
% 5.97/2.13  Inference rules
% 5.97/2.13  ----------------------
% 5.97/2.13  #Ref     : 0
% 5.97/2.13  #Sup     : 1106
% 5.97/2.13  #Fact    : 0
% 5.97/2.13  #Define  : 0
% 5.97/2.13  #Split   : 38
% 5.97/2.13  #Chain   : 0
% 5.97/2.13  #Close   : 0
% 5.97/2.13  
% 5.97/2.13  Ordering : KBO
% 5.97/2.13  
% 5.97/2.13  Simplification rules
% 5.97/2.13  ----------------------
% 5.97/2.13  #Subsume      : 97
% 5.97/2.13  #Demod        : 1277
% 5.97/2.13  #Tautology    : 677
% 5.97/2.13  #SimpNegUnit  : 22
% 5.97/2.13  #BackRed      : 234
% 5.97/2.13  
% 5.97/2.13  #Partial instantiations: 0
% 5.97/2.13  #Strategies tried      : 1
% 5.97/2.13  
% 5.97/2.13  Timing (in seconds)
% 5.97/2.13  ----------------------
% 5.97/2.13  Preprocessing        : 0.34
% 5.97/2.13  Parsing              : 0.18
% 5.97/2.13  CNF conversion       : 0.02
% 5.97/2.13  Main loop            : 0.96
% 5.97/2.13  Inferencing          : 0.33
% 5.97/2.13  Reduction            : 0.32
% 5.97/2.13  Demodulation         : 0.22
% 5.97/2.13  BG Simplification    : 0.04
% 5.97/2.13  Subsumption          : 0.19
% 5.97/2.13  Abstraction          : 0.04
% 5.97/2.13  MUC search           : 0.00
% 5.97/2.13  Cooper               : 0.00
% 5.97/2.13  Total                : 1.37
% 5.97/2.13  Index Insertion      : 0.00
% 5.97/2.13  Index Deletion       : 0.00
% 5.97/2.13  Index Matching       : 0.00
% 5.97/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
