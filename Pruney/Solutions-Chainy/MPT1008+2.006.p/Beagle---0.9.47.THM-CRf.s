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
% DateTime   : Thu Dec  3 10:14:26 EST 2020

% Result     : Theorem 3.35s
% Output     : CNFRefutation 3.35s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 319 expanded)
%              Number of leaves         :   44 ( 123 expanded)
%              Depth                    :   14
%              Number of atoms          :  177 ( 674 expanded)
%              Number of equality atoms :   85 ( 305 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_122,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_30,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_66,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_28,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_138,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_150,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_funct_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_163,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_171,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_163])).

tff(c_36,plain,(
    ! [A_17] :
      ( k1_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_180,plain,
    ( k1_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_171,c_36])).

tff(c_196,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_180])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_396,plain,(
    ! [B_142,A_143] :
      ( k1_tarski(k1_funct_1(B_142,A_143)) = k2_relat_1(B_142)
      | k1_tarski(A_143) != k1_relat_1(B_142)
      | ~ v1_funct_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_331,plain,(
    ! [A_121,B_122,C_123] :
      ( k2_relset_1(A_121,B_122,C_123) = k2_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_339,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_331])).

tff(c_68,plain,(
    k2_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') != k1_tarski(k1_funct_1('#skF_5','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_349,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_68])).

tff(c_402,plain,
    ( k1_tarski('#skF_3') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_349])).

tff(c_424,plain,(
    k1_tarski('#skF_3') != k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_76,c_402])).

tff(c_221,plain,(
    ! [C_94,A_95,B_96] :
      ( v4_relat_1(C_94,A_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_229,plain,(
    v4_relat_1('#skF_5',k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_221])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k1_relat_1(B_16),A_15)
      | ~ v4_relat_1(B_16,A_15)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_430,plain,(
    ! [B_148,C_149,A_150] :
      ( k2_tarski(B_148,C_149) = A_150
      | k1_tarski(C_149) = A_150
      | k1_tarski(B_148) = A_150
      | k1_xboole_0 = A_150
      | ~ r1_tarski(A_150,k2_tarski(B_148,C_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_446,plain,(
    ! [A_2,A_150] :
      ( k2_tarski(A_2,A_2) = A_150
      | k1_tarski(A_2) = A_150
      | k1_tarski(A_2) = A_150
      | k1_xboole_0 = A_150
      | ~ r1_tarski(A_150,k1_tarski(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_430])).

tff(c_461,plain,(
    ! [A_151,A_152] :
      ( k1_tarski(A_151) = A_152
      | k1_tarski(A_151) = A_152
      | k1_tarski(A_151) = A_152
      | k1_xboole_0 = A_152
      | ~ r1_tarski(A_152,k1_tarski(A_151)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_446])).

tff(c_481,plain,(
    ! [A_153,B_154] :
      ( k1_tarski(A_153) = k1_relat_1(B_154)
      | k1_relat_1(B_154) = k1_xboole_0
      | ~ v4_relat_1(B_154,k1_tarski(A_153))
      | ~ v1_relat_1(B_154) ) ),
    inference(resolution,[status(thm)],[c_28,c_461])).

tff(c_491,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_229,c_481])).

tff(c_502,plain,
    ( k1_tarski('#skF_3') = k1_relat_1('#skF_5')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_491])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_424,c_502])).

tff(c_505,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_180])).

tff(c_30,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_517,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_30])).

tff(c_34,plain,(
    ! [A_17] :
      ( k2_relat_1(A_17) != k1_xboole_0
      | k1_xboole_0 = A_17
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_179,plain,
    ( k2_relat_1('#skF_5') != k1_xboole_0
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_171,c_34])).

tff(c_195,plain,(
    k2_relat_1('#skF_5') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_179])).

tff(c_507,plain,(
    k2_relat_1('#skF_5') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_195])).

tff(c_547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_517,c_507])).

tff(c_548,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_4,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_560,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_4])).

tff(c_32,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_558,plain,(
    k1_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_548,c_32])).

tff(c_549,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_179])).

tff(c_582,plain,(
    k2_relat_1('#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_549])).

tff(c_796,plain,(
    ! [B_216,A_217] :
      ( k1_tarski(k1_funct_1(B_216,A_217)) = k2_relat_1(B_216)
      | k1_tarski(A_217) != k1_relat_1(B_216)
      | ~ v1_funct_1(B_216)
      | ~ v1_relat_1(B_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_22,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_557,plain,(
    ! [A_11] : m1_subset_1('#skF_5',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_22])).

tff(c_776,plain,(
    ! [A_206,B_207,C_208] :
      ( k2_relset_1(A_206,B_207,C_208) = k2_relat_1(C_208)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_206,B_207))) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_780,plain,(
    ! [A_206,B_207] : k2_relset_1(A_206,B_207,'#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_557,c_776])).

tff(c_782,plain,(
    ! [A_206,B_207] : k2_relset_1(A_206,B_207,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_582,c_780])).

tff(c_783,plain,(
    k1_tarski(k1_funct_1('#skF_5','#skF_3')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_68])).

tff(c_802,plain,
    ( k2_relat_1('#skF_5') != '#skF_5'
    | k1_tarski('#skF_3') != k1_relat_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_796,c_783])).

tff(c_823,plain,(
    k1_tarski('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_76,c_558,c_582,c_802])).

tff(c_70,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_562,plain,(
    '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_70])).

tff(c_74,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_60,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_2'(A_40),A_40)
      | k1_xboole_0 = A_40 ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_555,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_2'(A_40),A_40)
      | A_40 = '#skF_5' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_60])).

tff(c_66,plain,(
    ! [D_61,C_60,A_58,B_59] :
      ( r2_hidden(k1_funct_1(D_61,C_60),k2_relset_1(A_58,B_59,D_61))
      | k1_xboole_0 = B_59
      | ~ r2_hidden(C_60,A_58)
      | ~ m1_subset_1(D_61,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59)))
      | ~ v1_funct_2(D_61,A_58,B_59)
      | ~ v1_funct_1(D_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_921,plain,(
    ! [D_232,C_233,A_234,B_235] :
      ( r2_hidden(k1_funct_1(D_232,C_233),k2_relset_1(A_234,B_235,D_232))
      | B_235 = '#skF_5'
      | ~ r2_hidden(C_233,A_234)
      | ~ m1_subset_1(D_232,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_2(D_232,A_234,B_235)
      | ~ v1_funct_1(D_232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_548,c_66])).

tff(c_931,plain,(
    ! [C_233,B_207,A_206] :
      ( r2_hidden(k1_funct_1('#skF_5',C_233),'#skF_5')
      | B_207 = '#skF_5'
      | ~ r2_hidden(C_233,A_206)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_206,B_207)))
      | ~ v1_funct_2('#skF_5',A_206,B_207)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_921])).

tff(c_971,plain,(
    ! [C_239,B_240,A_241] :
      ( r2_hidden(k1_funct_1('#skF_5',C_239),'#skF_5')
      | B_240 = '#skF_5'
      | ~ r2_hidden(C_239,A_241)
      | ~ v1_funct_2('#skF_5',A_241,B_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_557,c_931])).

tff(c_997,plain,(
    ! [A_245,B_246] :
      ( r2_hidden(k1_funct_1('#skF_5','#skF_2'(A_245)),'#skF_5')
      | B_246 = '#skF_5'
      | ~ v1_funct_2('#skF_5',A_245,B_246)
      | A_245 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_555,c_971])).

tff(c_999,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_2'(k1_tarski('#skF_3'))),'#skF_5')
    | '#skF_5' = '#skF_4'
    | k1_tarski('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_74,c_997])).

tff(c_1002,plain,(
    r2_hidden(k1_funct_1('#skF_5','#skF_2'(k1_tarski('#skF_3'))),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_823,c_562,c_999])).

tff(c_50,plain,(
    ! [B_30,A_29] :
      ( ~ r1_tarski(B_30,A_29)
      | ~ r2_hidden(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1013,plain,(
    ~ r1_tarski('#skF_5',k1_funct_1('#skF_5','#skF_2'(k1_tarski('#skF_3')))) ),
    inference(resolution,[status(thm)],[c_1002,c_50])).

tff(c_1023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_560,c_1013])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:25:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.35/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.48  
% 3.35/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.48  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_mcart_1 > k2_enumset1 > k2_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_3 > #skF_4
% 3.35/1.48  
% 3.35/1.48  %Foreground sorts:
% 3.35/1.48  
% 3.35/1.48  
% 3.35/1.48  %Background operators:
% 3.35/1.48  
% 3.35/1.48  
% 3.35/1.48  %Foreground operators:
% 3.35/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.35/1.48  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.35/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.35/1.48  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.35/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.35/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.35/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.35/1.48  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.35/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.35/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.35/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.35/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.35/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.35/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.35/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.35/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.35/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.35/1.48  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.35/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.35/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.35/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.35/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.35/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.35/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.35/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.35/1.48  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.35/1.48  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 3.35/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.35/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.35/1.48  
% 3.35/1.49  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 3.35/1.49  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 3.35/1.49  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.35/1.49  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 3.35/1.49  tff(f_122, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.35/1.49  tff(f_118, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 3.35/1.49  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 3.35/1.49  tff(f_30, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.35/1.49  tff(f_49, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.35/1.49  tff(f_66, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.35/1.49  tff(f_28, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.35/1.49  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.35/1.49  tff(f_138, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_mcart_1)).
% 3.35/1.49  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_funct_2)).
% 3.35/1.49  tff(f_108, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.35/1.49  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.35/1.49  tff(c_163, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.35/1.49  tff(c_171, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_163])).
% 3.35/1.49  tff(c_36, plain, (![A_17]: (k1_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.49  tff(c_180, plain, (k1_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_171, c_36])).
% 3.35/1.49  tff(c_196, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_180])).
% 3.35/1.49  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.35/1.49  tff(c_396, plain, (![B_142, A_143]: (k1_tarski(k1_funct_1(B_142, A_143))=k2_relat_1(B_142) | k1_tarski(A_143)!=k1_relat_1(B_142) | ~v1_funct_1(B_142) | ~v1_relat_1(B_142))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.35/1.49  tff(c_331, plain, (![A_121, B_122, C_123]: (k2_relset_1(A_121, B_122, C_123)=k2_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.35/1.49  tff(c_339, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_331])).
% 3.35/1.49  tff(c_68, plain, (k2_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')!=k1_tarski(k1_funct_1('#skF_5', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.35/1.49  tff(c_349, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_68])).
% 3.35/1.49  tff(c_402, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_396, c_349])).
% 3.35/1.49  tff(c_424, plain, (k1_tarski('#skF_3')!=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_76, c_402])).
% 3.35/1.49  tff(c_221, plain, (![C_94, A_95, B_96]: (v4_relat_1(C_94, A_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_118])).
% 3.35/1.49  tff(c_229, plain, (v4_relat_1('#skF_5', k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_72, c_221])).
% 3.35/1.49  tff(c_28, plain, (![B_16, A_15]: (r1_tarski(k1_relat_1(B_16), A_15) | ~v4_relat_1(B_16, A_15) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.35/1.49  tff(c_6, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.35/1.49  tff(c_430, plain, (![B_148, C_149, A_150]: (k2_tarski(B_148, C_149)=A_150 | k1_tarski(C_149)=A_150 | k1_tarski(B_148)=A_150 | k1_xboole_0=A_150 | ~r1_tarski(A_150, k2_tarski(B_148, C_149)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.35/1.49  tff(c_446, plain, (![A_2, A_150]: (k2_tarski(A_2, A_2)=A_150 | k1_tarski(A_2)=A_150 | k1_tarski(A_2)=A_150 | k1_xboole_0=A_150 | ~r1_tarski(A_150, k1_tarski(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_430])).
% 3.35/1.49  tff(c_461, plain, (![A_151, A_152]: (k1_tarski(A_151)=A_152 | k1_tarski(A_151)=A_152 | k1_tarski(A_151)=A_152 | k1_xboole_0=A_152 | ~r1_tarski(A_152, k1_tarski(A_151)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_446])).
% 3.35/1.49  tff(c_481, plain, (![A_153, B_154]: (k1_tarski(A_153)=k1_relat_1(B_154) | k1_relat_1(B_154)=k1_xboole_0 | ~v4_relat_1(B_154, k1_tarski(A_153)) | ~v1_relat_1(B_154))), inference(resolution, [status(thm)], [c_28, c_461])).
% 3.35/1.49  tff(c_491, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_229, c_481])).
% 3.35/1.49  tff(c_502, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5') | k1_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_171, c_491])).
% 3.35/1.49  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_424, c_502])).
% 3.35/1.49  tff(c_505, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_180])).
% 3.35/1.49  tff(c_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.35/1.49  tff(c_517, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_30])).
% 3.35/1.49  tff(c_34, plain, (![A_17]: (k2_relat_1(A_17)!=k1_xboole_0 | k1_xboole_0=A_17 | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.35/1.49  tff(c_179, plain, (k2_relat_1('#skF_5')!=k1_xboole_0 | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_171, c_34])).
% 3.35/1.49  tff(c_195, plain, (k2_relat_1('#skF_5')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_179])).
% 3.35/1.49  tff(c_507, plain, (k2_relat_1('#skF_5')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_505, c_195])).
% 3.35/1.49  tff(c_547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_517, c_507])).
% 3.35/1.49  tff(c_548, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_179])).
% 3.35/1.49  tff(c_4, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.35/1.49  tff(c_560, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_4])).
% 3.35/1.49  tff(c_32, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.35/1.49  tff(c_558, plain, (k1_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_548, c_548, c_32])).
% 3.35/1.49  tff(c_549, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_179])).
% 3.35/1.49  tff(c_582, plain, (k2_relat_1('#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_548, c_549])).
% 3.35/1.49  tff(c_796, plain, (![B_216, A_217]: (k1_tarski(k1_funct_1(B_216, A_217))=k2_relat_1(B_216) | k1_tarski(A_217)!=k1_relat_1(B_216) | ~v1_funct_1(B_216) | ~v1_relat_1(B_216))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.35/1.49  tff(c_22, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.35/1.49  tff(c_557, plain, (![A_11]: (m1_subset_1('#skF_5', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_22])).
% 3.35/1.49  tff(c_776, plain, (![A_206, B_207, C_208]: (k2_relset_1(A_206, B_207, C_208)=k2_relat_1(C_208) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 3.35/1.49  tff(c_780, plain, (![A_206, B_207]: (k2_relset_1(A_206, B_207, '#skF_5')=k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_557, c_776])).
% 3.35/1.49  tff(c_782, plain, (![A_206, B_207]: (k2_relset_1(A_206, B_207, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_582, c_780])).
% 3.35/1.49  tff(c_783, plain, (k1_tarski(k1_funct_1('#skF_5', '#skF_3'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_782, c_68])).
% 3.35/1.49  tff(c_802, plain, (k2_relat_1('#skF_5')!='#skF_5' | k1_tarski('#skF_3')!=k1_relat_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_796, c_783])).
% 3.35/1.49  tff(c_823, plain, (k1_tarski('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_171, c_76, c_558, c_582, c_802])).
% 3.35/1.49  tff(c_70, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.35/1.49  tff(c_562, plain, ('#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_548, c_70])).
% 3.35/1.49  tff(c_74, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 3.35/1.49  tff(c_60, plain, (![A_40]: (r2_hidden('#skF_2'(A_40), A_40) | k1_xboole_0=A_40)), inference(cnfTransformation, [status(thm)], [f_138])).
% 3.35/1.49  tff(c_555, plain, (![A_40]: (r2_hidden('#skF_2'(A_40), A_40) | A_40='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_548, c_60])).
% 3.35/1.49  tff(c_66, plain, (![D_61, C_60, A_58, B_59]: (r2_hidden(k1_funct_1(D_61, C_60), k2_relset_1(A_58, B_59, D_61)) | k1_xboole_0=B_59 | ~r2_hidden(C_60, A_58) | ~m1_subset_1(D_61, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))) | ~v1_funct_2(D_61, A_58, B_59) | ~v1_funct_1(D_61))), inference(cnfTransformation, [status(thm)], [f_150])).
% 3.35/1.49  tff(c_921, plain, (![D_232, C_233, A_234, B_235]: (r2_hidden(k1_funct_1(D_232, C_233), k2_relset_1(A_234, B_235, D_232)) | B_235='#skF_5' | ~r2_hidden(C_233, A_234) | ~m1_subset_1(D_232, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_2(D_232, A_234, B_235) | ~v1_funct_1(D_232))), inference(demodulation, [status(thm), theory('equality')], [c_548, c_66])).
% 3.35/1.49  tff(c_931, plain, (![C_233, B_207, A_206]: (r2_hidden(k1_funct_1('#skF_5', C_233), '#skF_5') | B_207='#skF_5' | ~r2_hidden(C_233, A_206) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_206, B_207))) | ~v1_funct_2('#skF_5', A_206, B_207) | ~v1_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_782, c_921])).
% 3.35/1.49  tff(c_971, plain, (![C_239, B_240, A_241]: (r2_hidden(k1_funct_1('#skF_5', C_239), '#skF_5') | B_240='#skF_5' | ~r2_hidden(C_239, A_241) | ~v1_funct_2('#skF_5', A_241, B_240))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_557, c_931])).
% 3.35/1.49  tff(c_997, plain, (![A_245, B_246]: (r2_hidden(k1_funct_1('#skF_5', '#skF_2'(A_245)), '#skF_5') | B_246='#skF_5' | ~v1_funct_2('#skF_5', A_245, B_246) | A_245='#skF_5')), inference(resolution, [status(thm)], [c_555, c_971])).
% 3.35/1.49  tff(c_999, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_2'(k1_tarski('#skF_3'))), '#skF_5') | '#skF_5'='#skF_4' | k1_tarski('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_74, c_997])).
% 3.35/1.49  tff(c_1002, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_2'(k1_tarski('#skF_3'))), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_823, c_562, c_999])).
% 3.35/1.49  tff(c_50, plain, (![B_30, A_29]: (~r1_tarski(B_30, A_29) | ~r2_hidden(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.35/1.49  tff(c_1013, plain, (~r1_tarski('#skF_5', k1_funct_1('#skF_5', '#skF_2'(k1_tarski('#skF_3'))))), inference(resolution, [status(thm)], [c_1002, c_50])).
% 3.35/1.49  tff(c_1023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_560, c_1013])).
% 3.35/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.35/1.49  
% 3.35/1.49  Inference rules
% 3.35/1.49  ----------------------
% 3.35/1.49  #Ref     : 0
% 3.35/1.49  #Sup     : 189
% 3.35/1.49  #Fact    : 0
% 3.35/1.49  #Define  : 0
% 3.35/1.49  #Split   : 6
% 3.35/1.49  #Chain   : 0
% 3.35/1.49  #Close   : 0
% 3.35/1.49  
% 3.35/1.49  Ordering : KBO
% 3.35/1.49  
% 3.35/1.49  Simplification rules
% 3.35/1.50  ----------------------
% 3.35/1.50  #Subsume      : 12
% 3.35/1.50  #Demod        : 165
% 3.35/1.50  #Tautology    : 101
% 3.35/1.50  #SimpNegUnit  : 10
% 3.35/1.50  #BackRed      : 29
% 3.35/1.50  
% 3.35/1.50  #Partial instantiations: 0
% 3.35/1.50  #Strategies tried      : 1
% 3.35/1.50  
% 3.35/1.50  Timing (in seconds)
% 3.35/1.50  ----------------------
% 3.35/1.50  Preprocessing        : 0.37
% 3.35/1.50  Parsing              : 0.20
% 3.35/1.50  CNF conversion       : 0.02
% 3.35/1.50  Main loop            : 0.41
% 3.35/1.50  Inferencing          : 0.15
% 3.35/1.50  Reduction            : 0.14
% 3.35/1.50  Demodulation         : 0.10
% 3.35/1.50  BG Simplification    : 0.02
% 3.35/1.50  Subsumption          : 0.07
% 3.35/1.50  Abstraction          : 0.02
% 3.35/1.50  MUC search           : 0.00
% 3.35/1.50  Cooper               : 0.00
% 3.35/1.50  Total                : 0.82
% 3.35/1.50  Index Insertion      : 0.00
% 3.35/1.50  Index Deletion       : 0.00
% 3.35/1.50  Index Matching       : 0.00
% 3.35/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
