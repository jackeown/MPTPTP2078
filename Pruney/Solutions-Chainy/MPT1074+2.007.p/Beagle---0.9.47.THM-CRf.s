%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:07 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 611 expanded)
%              Number of leaves         :   40 ( 230 expanded)
%              Depth                    :   19
%              Number of atoms          :  191 (2013 expanded)
%              Number of equality atoms :   33 ( 380 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k3_funct_2,type,(
    k3_funct_2: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_164,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ v1_xboole_0(B)
       => ! [C] :
            ( ~ v1_xboole_0(C)
           => ! [D] :
                ( ( v1_funct_1(D)
                  & v1_funct_2(D,B,C)
                  & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
               => ( ! [E] :
                      ( m1_subset_1(E,B)
                     => r2_hidden(k3_funct_2(B,C,D,E),A) )
                 => r1_tarski(k2_relset_1(B,C,D),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_82,axiom,(
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

tff(f_142,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( ( k1_relat_1(C) = A
          & ! [D] :
              ( r2_hidden(D,A)
             => r2_hidden(k1_funct_1(C,D),B) ) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( ~ v1_xboole_0(A)
        & v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,A) )
     => k3_funct_2(A,B,C,D) = k1_funct_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_113,axiom,(
    ! [A,B,C] :
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

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_66,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_97,plain,(
    ! [C_65,A_66,B_67] :
      ( v1_relat_1(C_65)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_106,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_97])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_167,plain,(
    ! [A_86,B_87,C_88] :
      ( k2_relset_1(A_86,B_87,C_88) = k2_relat_1(C_88)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_176,plain,(
    k2_relset_1('#skF_4','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_167])).

tff(c_62,plain,(
    ~ r1_tarski(k2_relset_1('#skF_4','#skF_5','#skF_6'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_177,plain,(
    ~ r1_tarski(k2_relat_1('#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_62])).

tff(c_184,plain,
    ( ~ v5_relat_1('#skF_6','#skF_3')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_12,c_177])).

tff(c_187,plain,(
    ~ v5_relat_1('#skF_6','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_184])).

tff(c_70,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_68,plain,(
    v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_245,plain,(
    ! [A_104,B_105,C_106] :
      ( k1_relset_1(A_104,B_105,C_106) = k1_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_254,plain,(
    k1_relset_1('#skF_4','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_245])).

tff(c_601,plain,(
    ! [B_153,A_154,C_155] :
      ( k1_xboole_0 = B_153
      | k1_relset_1(A_154,B_153,C_155) = A_154
      | ~ v1_funct_2(C_155,A_154,B_153)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_154,B_153))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_611,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_4'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_601])).

tff(c_616,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_254,c_611])).

tff(c_617,plain,(
    k1_relat_1('#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_616])).

tff(c_774,plain,(
    ! [C_168,B_169] :
      ( r2_hidden('#skF_2'(k1_relat_1(C_168),B_169,C_168),k1_relat_1(C_168))
      | m1_subset_1(C_168,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_168),B_169)))
      | ~ v1_funct_1(C_168)
      | ~ v1_relat_1(C_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_786,plain,(
    ! [B_169] :
      ( r2_hidden('#skF_2'(k1_relat_1('#skF_6'),B_169,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_169)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_774])).

tff(c_804,plain,(
    ! [B_174] :
      ( r2_hidden('#skF_2'('#skF_4',B_174,'#skF_6'),'#skF_4')
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_174))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_617,c_617,c_786])).

tff(c_18,plain,(
    ! [C_15,B_14,A_13] :
      ( v5_relat_1(C_15,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_845,plain,(
    ! [B_175] :
      ( v5_relat_1('#skF_6',B_175)
      | r2_hidden('#skF_2'('#skF_4',B_175,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_804,c_18])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_853,plain,(
    ! [B_175] :
      ( m1_subset_1('#skF_2'('#skF_4',B_175,'#skF_6'),'#skF_4')
      | v5_relat_1('#skF_6',B_175) ) ),
    inference(resolution,[status(thm)],[c_845,c_4])).

tff(c_74,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1050,plain,(
    ! [A_192,B_193,C_194,D_195] :
      ( k3_funct_2(A_192,B_193,C_194,D_195) = k1_funct_1(C_194,D_195)
      | ~ m1_subset_1(D_195,A_192)
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193)))
      | ~ v1_funct_2(C_194,A_192,B_193)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0(A_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1054,plain,(
    ! [B_193,C_194,B_175] :
      ( k3_funct_2('#skF_4',B_193,C_194,'#skF_2'('#skF_4',B_175,'#skF_6')) = k1_funct_1(C_194,'#skF_2'('#skF_4',B_175,'#skF_6'))
      | ~ m1_subset_1(C_194,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_193)))
      | ~ v1_funct_2(C_194,'#skF_4',B_193)
      | ~ v1_funct_1(C_194)
      | v1_xboole_0('#skF_4')
      | v5_relat_1('#skF_6',B_175) ) ),
    inference(resolution,[status(thm)],[c_853,c_1050])).

tff(c_1082,plain,(
    ! [B_197,C_198,B_199] :
      ( k3_funct_2('#skF_4',B_197,C_198,'#skF_2'('#skF_4',B_199,'#skF_6')) = k1_funct_1(C_198,'#skF_2'('#skF_4',B_199,'#skF_6'))
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_197)))
      | ~ v1_funct_2(C_198,'#skF_4',B_197)
      | ~ v1_funct_1(C_198)
      | v5_relat_1('#skF_6',B_199) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_1054])).

tff(c_1089,plain,(
    ! [B_199] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_199,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_199,'#skF_6'))
      | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
      | ~ v1_funct_1('#skF_6')
      | v5_relat_1('#skF_6',B_199) ) ),
    inference(resolution,[status(thm)],[c_66,c_1082])).

tff(c_1711,plain,(
    ! [B_253] :
      ( k3_funct_2('#skF_4','#skF_5','#skF_6','#skF_2'('#skF_4',B_253,'#skF_6')) = k1_funct_1('#skF_6','#skF_2'('#skF_4',B_253,'#skF_6'))
      | v5_relat_1('#skF_6',B_253) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_1089])).

tff(c_64,plain,(
    ! [E_54] :
      ( r2_hidden(k3_funct_2('#skF_4','#skF_5','#skF_6',E_54),'#skF_3')
      | ~ m1_subset_1(E_54,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1975,plain,(
    ! [B_272] :
      ( r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_272,'#skF_6')),'#skF_3')
      | ~ m1_subset_1('#skF_2'('#skF_4',B_272,'#skF_6'),'#skF_4')
      | v5_relat_1('#skF_6',B_272) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1711,c_64])).

tff(c_658,plain,(
    ! [C_158,B_159] :
      ( ~ r2_hidden(k1_funct_1(C_158,'#skF_2'(k1_relat_1(C_158),B_159,C_158)),B_159)
      | v1_funct_2(C_158,k1_relat_1(C_158),B_159)
      | ~ v1_funct_1(C_158)
      | ~ v1_relat_1(C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_661,plain,(
    ! [B_159] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_159,'#skF_6')),B_159)
      | v1_funct_2('#skF_6',k1_relat_1('#skF_6'),B_159)
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_658])).

tff(c_663,plain,(
    ! [B_159] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_159,'#skF_6')),B_159)
      | v1_funct_2('#skF_6','#skF_4',B_159) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_617,c_661])).

tff(c_1983,plain,
    ( v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1975,c_663])).

tff(c_1995,plain,
    ( v1_funct_2('#skF_6','#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_1983])).

tff(c_2019,plain,(
    ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1995])).

tff(c_2028,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_853,c_2019])).

tff(c_2037,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_2028])).

tff(c_2039,plain,(
    m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_1995])).

tff(c_865,plain,(
    ! [C_179,B_180] :
      ( ~ r2_hidden(k1_funct_1(C_179,'#skF_2'(k1_relat_1(C_179),B_180,C_179)),B_180)
      | m1_subset_1(C_179,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_179),B_180)))
      | ~ v1_funct_1(C_179)
      | ~ v1_relat_1(C_179) ) ),
    inference(cnfTransformation,[status(thm)],[f_142])).

tff(c_868,plain,(
    ! [B_180] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_180,'#skF_6')),B_180)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'),B_180)))
      | ~ v1_funct_1('#skF_6')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_617,c_865])).

tff(c_870,plain,(
    ! [B_180] :
      ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_2'('#skF_4',B_180,'#skF_6')),B_180)
      | m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_180))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_70,c_617,c_868])).

tff(c_1979,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4')
    | v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_1975,c_870])).

tff(c_1992,plain,
    ( m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3')))
    | ~ m1_subset_1('#skF_2'('#skF_4','#skF_3','#skF_6'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_1979])).

tff(c_2078,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2039,c_1992])).

tff(c_2108,plain,(
    v5_relat_1('#skF_6','#skF_3') ),
    inference(resolution,[status(thm)],[c_2078,c_18])).

tff(c_2145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_2108])).

tff(c_2146,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_616])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_2184,plain,(
    ! [A_1] : r1_tarski('#skF_5',A_1) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2146,c_2])).

tff(c_2314,plain,(
    ! [A_292,B_293,C_294] :
      ( r2_hidden('#skF_1'(A_292,B_293,C_294),B_293)
      | k2_relset_1(A_292,B_293,C_294) = B_293
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_292,B_293)))
      | ~ v1_funct_2(C_294,A_292,B_293)
      | ~ v1_funct_1(C_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_2321,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | k2_relset_1('#skF_4','#skF_5','#skF_6') = '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_66,c_2314])).

tff(c_2326,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5')
    | k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_176,c_2321])).

tff(c_2392,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2326])).

tff(c_2393,plain,(
    ~ r1_tarski('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2392,c_177])).

tff(c_2397,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2184,c_2393])).

tff(c_2398,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5','#skF_6'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_2326])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( ~ r1_tarski(B_9,A_8)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2402,plain,(
    ~ r1_tarski('#skF_5','#skF_1'('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_2398,c_14])).

tff(c_2409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2184,c_2402])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.82  
% 4.85/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.82  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_funct_2 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 4.85/1.82  
% 4.85/1.82  %Foreground sorts:
% 4.85/1.82  
% 4.85/1.82  
% 4.85/1.82  %Background operators:
% 4.85/1.82  
% 4.85/1.82  
% 4.85/1.82  %Foreground operators:
% 4.85/1.82  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.85/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.85/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.85/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.85/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.85/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.85/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.85/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.85/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.85/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.85/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.85/1.82  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.85/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.85/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.85/1.82  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 4.85/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.85/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.85/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.85/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.85/1.82  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.85/1.82  tff(k3_funct_2, type, k3_funct_2: ($i * $i * $i * $i) > $i).
% 4.85/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.85/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.85/1.82  
% 4.85/1.84  tff(f_164, negated_conjecture, ~(![A, B]: (~v1_xboole_0(B) => (![C]: (~v1_xboole_0(C) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((![E]: (m1_subset_1(E, B) => r2_hidden(k3_funct_2(B, C, D, E), A))) => r1_tarski(k2_relset_1(B, C, D), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t191_funct_2)).
% 4.85/1.84  tff(f_50, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.85/1.84  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.85/1.84  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.85/1.84  tff(f_60, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.85/1.84  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.85/1.84  tff(f_142, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(C) = A) & (![D]: (r2_hidden(D, A) => r2_hidden(k1_funct_1(C, D), B)))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_funct_2)).
% 4.85/1.84  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.85/1.84  tff(f_31, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 4.85/1.84  tff(f_95, axiom, (![A, B, C, D]: (((((~v1_xboole_0(A) & v1_funct_1(C)) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & m1_subset_1(D, A)) => (k3_funct_2(A, B, C, D) = k1_funct_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k3_funct_2)).
% 4.85/1.84  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.85/1.84  tff(f_113, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((![D]: ~(r2_hidden(D, B) & (![E]: ~(r2_hidden(E, A) & (D = k1_funct_1(C, E)))))) => (k2_relset_1(A, B, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_2)).
% 4.85/1.84  tff(f_46, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 4.85/1.84  tff(c_66, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.85/1.84  tff(c_97, plain, (![C_65, A_66, B_67]: (v1_relat_1(C_65) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_66, B_67))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.85/1.84  tff(c_106, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_97])).
% 4.85/1.84  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.85/1.84  tff(c_167, plain, (![A_86, B_87, C_88]: (k2_relset_1(A_86, B_87, C_88)=k2_relat_1(C_88) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.85/1.84  tff(c_176, plain, (k2_relset_1('#skF_4', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_167])).
% 4.85/1.84  tff(c_62, plain, (~r1_tarski(k2_relset_1('#skF_4', '#skF_5', '#skF_6'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.85/1.84  tff(c_177, plain, (~r1_tarski(k2_relat_1('#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_62])).
% 4.85/1.84  tff(c_184, plain, (~v5_relat_1('#skF_6', '#skF_3') | ~v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_12, c_177])).
% 4.85/1.84  tff(c_187, plain, (~v5_relat_1('#skF_6', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_184])).
% 4.85/1.84  tff(c_70, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.85/1.84  tff(c_68, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.85/1.84  tff(c_245, plain, (![A_104, B_105, C_106]: (k1_relset_1(A_104, B_105, C_106)=k1_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.85/1.84  tff(c_254, plain, (k1_relset_1('#skF_4', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_245])).
% 4.85/1.84  tff(c_601, plain, (![B_153, A_154, C_155]: (k1_xboole_0=B_153 | k1_relset_1(A_154, B_153, C_155)=A_154 | ~v1_funct_2(C_155, A_154, B_153) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_154, B_153))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.85/1.84  tff(c_611, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_4' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_66, c_601])).
% 4.85/1.84  tff(c_616, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_254, c_611])).
% 4.85/1.84  tff(c_617, plain, (k1_relat_1('#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_616])).
% 4.85/1.84  tff(c_774, plain, (![C_168, B_169]: (r2_hidden('#skF_2'(k1_relat_1(C_168), B_169, C_168), k1_relat_1(C_168)) | m1_subset_1(C_168, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_168), B_169))) | ~v1_funct_1(C_168) | ~v1_relat_1(C_168))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.85/1.84  tff(c_786, plain, (![B_169]: (r2_hidden('#skF_2'(k1_relat_1('#skF_6'), B_169, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_169))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_617, c_774])).
% 4.85/1.84  tff(c_804, plain, (![B_174]: (r2_hidden('#skF_2'('#skF_4', B_174, '#skF_6'), '#skF_4') | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_174))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_617, c_617, c_786])).
% 4.85/1.84  tff(c_18, plain, (![C_15, B_14, A_13]: (v5_relat_1(C_15, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.85/1.84  tff(c_845, plain, (![B_175]: (v5_relat_1('#skF_6', B_175) | r2_hidden('#skF_2'('#skF_4', B_175, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_804, c_18])).
% 4.85/1.84  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.85/1.84  tff(c_853, plain, (![B_175]: (m1_subset_1('#skF_2'('#skF_4', B_175, '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', B_175))), inference(resolution, [status(thm)], [c_845, c_4])).
% 4.85/1.84  tff(c_74, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.85/1.84  tff(c_1050, plain, (![A_192, B_193, C_194, D_195]: (k3_funct_2(A_192, B_193, C_194, D_195)=k1_funct_1(C_194, D_195) | ~m1_subset_1(D_195, A_192) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))) | ~v1_funct_2(C_194, A_192, B_193) | ~v1_funct_1(C_194) | v1_xboole_0(A_192))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.85/1.84  tff(c_1054, plain, (![B_193, C_194, B_175]: (k3_funct_2('#skF_4', B_193, C_194, '#skF_2'('#skF_4', B_175, '#skF_6'))=k1_funct_1(C_194, '#skF_2'('#skF_4', B_175, '#skF_6')) | ~m1_subset_1(C_194, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_193))) | ~v1_funct_2(C_194, '#skF_4', B_193) | ~v1_funct_1(C_194) | v1_xboole_0('#skF_4') | v5_relat_1('#skF_6', B_175))), inference(resolution, [status(thm)], [c_853, c_1050])).
% 4.85/1.84  tff(c_1082, plain, (![B_197, C_198, B_199]: (k3_funct_2('#skF_4', B_197, C_198, '#skF_2'('#skF_4', B_199, '#skF_6'))=k1_funct_1(C_198, '#skF_2'('#skF_4', B_199, '#skF_6')) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_197))) | ~v1_funct_2(C_198, '#skF_4', B_197) | ~v1_funct_1(C_198) | v5_relat_1('#skF_6', B_199))), inference(negUnitSimplification, [status(thm)], [c_74, c_1054])).
% 4.85/1.84  tff(c_1089, plain, (![B_199]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_199, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_199, '#skF_6')) | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6') | v5_relat_1('#skF_6', B_199))), inference(resolution, [status(thm)], [c_66, c_1082])).
% 4.85/1.84  tff(c_1711, plain, (![B_253]: (k3_funct_2('#skF_4', '#skF_5', '#skF_6', '#skF_2'('#skF_4', B_253, '#skF_6'))=k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_253, '#skF_6')) | v5_relat_1('#skF_6', B_253))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_1089])).
% 4.85/1.84  tff(c_64, plain, (![E_54]: (r2_hidden(k3_funct_2('#skF_4', '#skF_5', '#skF_6', E_54), '#skF_3') | ~m1_subset_1(E_54, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.85/1.84  tff(c_1975, plain, (![B_272]: (r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_272, '#skF_6')), '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', B_272, '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', B_272))), inference(superposition, [status(thm), theory('equality')], [c_1711, c_64])).
% 4.85/1.84  tff(c_658, plain, (![C_158, B_159]: (~r2_hidden(k1_funct_1(C_158, '#skF_2'(k1_relat_1(C_158), B_159, C_158)), B_159) | v1_funct_2(C_158, k1_relat_1(C_158), B_159) | ~v1_funct_1(C_158) | ~v1_relat_1(C_158))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.85/1.84  tff(c_661, plain, (![B_159]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_159, '#skF_6')), B_159) | v1_funct_2('#skF_6', k1_relat_1('#skF_6'), B_159) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_617, c_658])).
% 4.85/1.84  tff(c_663, plain, (![B_159]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_159, '#skF_6')), B_159) | v1_funct_2('#skF_6', '#skF_4', B_159))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_617, c_661])).
% 4.85/1.84  tff(c_1983, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1975, c_663])).
% 4.85/1.84  tff(c_1995, plain, (v1_funct_2('#skF_6', '#skF_4', '#skF_3') | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_187, c_1983])).
% 4.85/1.84  tff(c_2019, plain, (~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1995])).
% 4.85/1.84  tff(c_2028, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_853, c_2019])).
% 4.85/1.84  tff(c_2037, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_2028])).
% 4.85/1.84  tff(c_2039, plain, (m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(splitRight, [status(thm)], [c_1995])).
% 4.85/1.84  tff(c_865, plain, (![C_179, B_180]: (~r2_hidden(k1_funct_1(C_179, '#skF_2'(k1_relat_1(C_179), B_180, C_179)), B_180) | m1_subset_1(C_179, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(C_179), B_180))) | ~v1_funct_1(C_179) | ~v1_relat_1(C_179))), inference(cnfTransformation, [status(thm)], [f_142])).
% 4.85/1.84  tff(c_868, plain, (![B_180]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_180, '#skF_6')), B_180) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_6'), B_180))) | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_617, c_865])).
% 4.85/1.84  tff(c_870, plain, (![B_180]: (~r2_hidden(k1_funct_1('#skF_6', '#skF_2'('#skF_4', B_180, '#skF_6')), B_180) | m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_180))))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_70, c_617, c_868])).
% 4.85/1.84  tff(c_1979, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4') | v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_1975, c_870])).
% 4.85/1.84  tff(c_1992, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3'))) | ~m1_subset_1('#skF_2'('#skF_4', '#skF_3', '#skF_6'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_187, c_1979])).
% 4.85/1.84  tff(c_2078, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2039, c_1992])).
% 4.85/1.84  tff(c_2108, plain, (v5_relat_1('#skF_6', '#skF_3')), inference(resolution, [status(thm)], [c_2078, c_18])).
% 4.85/1.84  tff(c_2145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_2108])).
% 4.85/1.84  tff(c_2146, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_616])).
% 4.85/1.84  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.85/1.84  tff(c_2184, plain, (![A_1]: (r1_tarski('#skF_5', A_1))), inference(demodulation, [status(thm), theory('equality')], [c_2146, c_2])).
% 4.85/1.84  tff(c_2314, plain, (![A_292, B_293, C_294]: (r2_hidden('#skF_1'(A_292, B_293, C_294), B_293) | k2_relset_1(A_292, B_293, C_294)=B_293 | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_292, B_293))) | ~v1_funct_2(C_294, A_292, B_293) | ~v1_funct_1(C_294))), inference(cnfTransformation, [status(thm)], [f_113])).
% 4.85/1.84  tff(c_2321, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | k2_relset_1('#skF_4', '#skF_5', '#skF_6')='#skF_5' | ~v1_funct_2('#skF_6', '#skF_4', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_66, c_2314])).
% 4.85/1.84  tff(c_2326, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_5') | k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_176, c_2321])).
% 4.85/1.84  tff(c_2392, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_2326])).
% 4.85/1.84  tff(c_2393, plain, (~r1_tarski('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2392, c_177])).
% 4.85/1.84  tff(c_2397, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2184, c_2393])).
% 4.85/1.84  tff(c_2398, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5', '#skF_6'), '#skF_5')), inference(splitRight, [status(thm)], [c_2326])).
% 4.85/1.84  tff(c_14, plain, (![B_9, A_8]: (~r1_tarski(B_9, A_8) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.85/1.84  tff(c_2402, plain, (~r1_tarski('#skF_5', '#skF_1'('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_2398, c_14])).
% 4.85/1.84  tff(c_2409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2184, c_2402])).
% 4.85/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.85/1.84  
% 4.85/1.84  Inference rules
% 4.85/1.84  ----------------------
% 4.85/1.84  #Ref     : 0
% 4.85/1.84  #Sup     : 423
% 4.85/1.84  #Fact    : 0
% 4.85/1.84  #Define  : 0
% 4.85/1.84  #Split   : 9
% 4.85/1.84  #Chain   : 0
% 4.85/1.84  #Close   : 0
% 4.85/1.84  
% 4.85/1.84  Ordering : KBO
% 4.85/1.84  
% 4.85/1.84  Simplification rules
% 4.85/1.84  ----------------------
% 4.85/1.84  #Subsume      : 64
% 4.85/1.84  #Demod        : 398
% 4.85/1.84  #Tautology    : 137
% 4.85/1.84  #SimpNegUnit  : 10
% 4.85/1.84  #BackRed      : 53
% 4.85/1.84  
% 4.85/1.84  #Partial instantiations: 0
% 4.85/1.84  #Strategies tried      : 1
% 4.85/1.84  
% 4.85/1.84  Timing (in seconds)
% 4.85/1.84  ----------------------
% 4.85/1.84  Preprocessing        : 0.34
% 4.85/1.84  Parsing              : 0.17
% 4.85/1.84  CNF conversion       : 0.02
% 4.85/1.84  Main loop            : 0.70
% 5.00/1.84  Inferencing          : 0.24
% 5.00/1.84  Reduction            : 0.25
% 5.00/1.84  Demodulation         : 0.18
% 5.00/1.84  BG Simplification    : 0.03
% 5.00/1.84  Subsumption          : 0.11
% 5.00/1.84  Abstraction          : 0.03
% 5.00/1.84  MUC search           : 0.00
% 5.00/1.84  Cooper               : 0.00
% 5.00/1.84  Total                : 1.07
% 5.00/1.84  Index Insertion      : 0.00
% 5.00/1.84  Index Deletion       : 0.00
% 5.00/1.84  Index Matching       : 0.00
% 5.00/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
