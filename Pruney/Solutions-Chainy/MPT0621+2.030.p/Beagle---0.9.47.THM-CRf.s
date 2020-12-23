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
% DateTime   : Thu Dec  3 10:03:02 EST 2020

% Result     : Theorem 8.50s
% Output     : CNFRefutation 8.95s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 774 expanded)
%              Number of leaves         :   32 ( 283 expanded)
%              Depth                    :   16
%              Number of atoms          :  264 (2329 expanded)
%              Number of equality atoms :  113 ( 907 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_7 > #skF_4 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_7',type,(
    '#skF_7': $i > $i )).

tff(np__1,type,(
    np__1: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_101,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

tff(f_77,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_120,negated_conjecture,(
    ~ ! [A] :
        ( ! [B] :
            ( ( v1_relat_1(B)
              & v1_funct_1(B) )
           => ! [C] :
                ( ( v1_relat_1(C)
                  & v1_funct_1(C) )
               => ( ( k1_relat_1(B) = A
                    & k1_relat_1(C) = A )
                 => B = C ) ) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_65,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

tff(f_89,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(c_18,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_58,plain,(
    ! [A_60] : v1_funct_1('#skF_7'(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    ! [A_60] : k1_relat_1('#skF_7'(A_60)) = A_60 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_60,plain,(
    ! [A_60] : v1_relat_1('#skF_7'(A_60)) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_40,plain,(
    ! [A_47,B_48] : k1_relat_1('#skF_5'(A_47,B_48)) = A_47 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,(
    ! [A_47,B_48] : v1_funct_1('#skF_5'(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_120,plain,(
    ! [A_84,B_85] : v1_relat_1('#skF_5'(A_84,B_85)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_64,plain,(
    ! [C_71,B_69] :
      ( C_71 = B_69
      | k1_relat_1(C_71) != '#skF_8'
      | k1_relat_1(B_69) != '#skF_8'
      | ~ v1_funct_1(C_71)
      | ~ v1_relat_1(C_71)
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_122,plain,(
    ! [B_69,A_84,B_85] :
      ( B_69 = '#skF_5'(A_84,B_85)
      | k1_relat_1('#skF_5'(A_84,B_85)) != '#skF_8'
      | k1_relat_1(B_69) != '#skF_8'
      | ~ v1_funct_1('#skF_5'(A_84,B_85))
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(resolution,[status(thm)],[c_120,c_64])).

tff(c_125,plain,(
    ! [B_69,A_84,B_85] :
      ( B_69 = '#skF_5'(A_84,B_85)
      | k1_relat_1('#skF_5'(A_84,B_85)) != '#skF_8'
      | k1_relat_1(B_69) != '#skF_8'
      | ~ v1_funct_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_122])).

tff(c_487,plain,(
    ! [B_113,A_114,B_115] :
      ( B_113 = '#skF_5'(A_114,B_115)
      | A_114 != '#skF_8'
      | k1_relat_1(B_113) != '#skF_8'
      | ~ v1_funct_1(B_113)
      | ~ v1_relat_1(B_113) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_125])).

tff(c_495,plain,(
    ! [A_60,A_114,B_115] :
      ( '#skF_7'(A_60) = '#skF_5'(A_114,B_115)
      | A_114 != '#skF_8'
      | k1_relat_1('#skF_7'(A_60)) != '#skF_8'
      | ~ v1_funct_1('#skF_7'(A_60)) ) ),
    inference(resolution,[status(thm)],[c_60,c_487])).

tff(c_1363,plain,(
    ! [A_153,A_154,B_155] :
      ( '#skF_7'(A_153) = '#skF_5'(A_154,B_155)
      | A_154 != '#skF_8'
      | A_153 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_495])).

tff(c_44,plain,(
    ! [A_47,B_48] : v1_relat_1('#skF_5'(A_47,B_48)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_176,plain,(
    ! [A_94] :
      ( ~ v1_xboole_0(k1_relat_1(A_94))
      | ~ v1_relat_1(A_94)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_179,plain,(
    ! [A_47,B_48] :
      ( ~ v1_xboole_0(A_47)
      | ~ v1_relat_1('#skF_5'(A_47,B_48))
      | v1_xboole_0('#skF_5'(A_47,B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_176])).

tff(c_190,plain,(
    ! [A_47,B_48] :
      ( ~ v1_xboole_0(A_47)
      | v1_xboole_0('#skF_5'(A_47,B_48)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_179])).

tff(c_1433,plain,(
    ! [A_154,A_153] :
      ( ~ v1_xboole_0(A_154)
      | v1_xboole_0('#skF_7'(A_153))
      | A_154 != '#skF_8'
      | A_153 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1363,c_190])).

tff(c_1503,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1433])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_141,plain,(
    ! [A_87,B_88] : ~ r2_hidden(A_87,k2_zfmisc_1(A_87,B_88)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [A_2] : ~ r2_hidden(A_2,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_141])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_182,plain,(
    ! [A_60] :
      ( ~ v1_xboole_0(A_60)
      | ~ v1_relat_1('#skF_7'(A_60))
      | v1_xboole_0('#skF_7'(A_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_176])).

tff(c_197,plain,(
    ! [A_95] :
      ( ~ v1_xboole_0(A_95)
      | v1_xboole_0('#skF_7'(A_95)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_182])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_207,plain,(
    ! [A_97] :
      ( '#skF_7'(A_97) = k1_xboole_0
      | ~ v1_xboole_0(A_97) ) ),
    inference(resolution,[status(thm)],[c_197,c_4])).

tff(c_219,plain,(
    '#skF_7'(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_207])).

tff(c_239,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_60])).

tff(c_241,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_58])).

tff(c_16,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2140,plain,(
    ! [A_181,B_182] :
      ( r2_hidden('#skF_2'(A_181,B_182),k1_relat_1(A_181))
      | r2_hidden('#skF_3'(A_181,B_182),B_182)
      | k2_relat_1(A_181) = B_182
      | ~ v1_funct_1(A_181)
      | ~ v1_relat_1(A_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2170,plain,(
    ! [B_182] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_182),k1_xboole_0)
      | r2_hidden('#skF_3'(k1_xboole_0,B_182),B_182)
      | k2_relat_1(k1_xboole_0) = B_182
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2140])).

tff(c_2185,plain,(
    ! [B_182] :
      ( r2_hidden('#skF_2'(k1_xboole_0,B_182),k1_xboole_0)
      | r2_hidden('#skF_3'(k1_xboole_0,B_182),B_182)
      | k1_xboole_0 = B_182 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_241,c_16,c_2170])).

tff(c_2187,plain,(
    ! [B_183] :
      ( r2_hidden('#skF_3'(k1_xboole_0,B_183),B_183)
      | k1_xboole_0 = B_183 ) ),
    inference(negUnitSimplification,[status(thm)],[c_144,c_2185])).

tff(c_54,plain,(
    ! [A_60,C_65] :
      ( k1_funct_1('#skF_7'(A_60),C_65) = np__1
      | ~ r2_hidden(C_65,A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1328,plain,(
    ! [A_144,D_145] :
      ( r2_hidden(k1_funct_1(A_144,D_145),k2_relat_1(A_144))
      | ~ r2_hidden(D_145,k1_relat_1(A_144))
      | ~ v1_funct_1(A_144)
      | ~ v1_relat_1(A_144) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1334,plain,(
    ! [A_60,C_65] :
      ( r2_hidden(np__1,k2_relat_1('#skF_7'(A_60)))
      | ~ r2_hidden(C_65,k1_relat_1('#skF_7'(A_60)))
      | ~ v1_funct_1('#skF_7'(A_60))
      | ~ v1_relat_1('#skF_7'(A_60))
      | ~ r2_hidden(C_65,A_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1328])).

tff(c_1344,plain,(
    ! [A_60,C_65] :
      ( r2_hidden(np__1,k2_relat_1('#skF_7'(A_60)))
      | ~ r2_hidden(C_65,A_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_56,c_1334])).

tff(c_2205,plain,(
    ! [B_183] :
      ( r2_hidden(np__1,k2_relat_1('#skF_7'(B_183)))
      | k1_xboole_0 = B_183 ) ),
    inference(resolution,[status(thm)],[c_2187,c_1344])).

tff(c_50,plain,(
    ! [A_54] : v1_funct_1('#skF_6'(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_48,plain,(
    ! [A_54] : k1_relat_1('#skF_6'(A_54)) = A_54 ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_52,plain,(
    ! [A_54] : v1_relat_1('#skF_6'(A_54)) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_84,plain,(
    ! [C_77,B_78] :
      ( C_77 = B_78
      | k1_relat_1(C_77) != '#skF_8'
      | k1_relat_1(B_78) != '#skF_8'
      | ~ v1_funct_1(C_77)
      | ~ v1_relat_1(C_77)
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_88,plain,(
    ! [B_78,A_60] :
      ( B_78 = '#skF_7'(A_60)
      | k1_relat_1('#skF_7'(A_60)) != '#skF_8'
      | k1_relat_1(B_78) != '#skF_8'
      | ~ v1_funct_1('#skF_7'(A_60))
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_60,c_84])).

tff(c_94,plain,(
    ! [B_78,A_60] :
      ( B_78 = '#skF_7'(A_60)
      | k1_relat_1('#skF_7'(A_60)) != '#skF_8'
      | k1_relat_1(B_78) != '#skF_8'
      | ~ v1_funct_1(B_78)
      | ~ v1_relat_1(B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_88])).

tff(c_258,plain,(
    ! [B_100,A_101] :
      ( B_100 = '#skF_7'(A_101)
      | A_101 != '#skF_8'
      | k1_relat_1(B_100) != '#skF_8'
      | ~ v1_funct_1(B_100)
      | ~ v1_relat_1(B_100) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_94])).

tff(c_264,plain,(
    ! [A_101,A_54] :
      ( '#skF_7'(A_101) = '#skF_6'(A_54)
      | A_101 != '#skF_8'
      | k1_relat_1('#skF_6'(A_54)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_54)) ) ),
    inference(resolution,[status(thm)],[c_52,c_258])).

tff(c_275,plain,(
    ! [A_101,A_54] :
      ( '#skF_7'(A_101) = '#skF_6'(A_54)
      | A_101 != '#skF_8'
      | A_54 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_264])).

tff(c_2055,plain,(
    ! [A_175,C_176] :
      ( r2_hidden('#skF_4'(A_175,k2_relat_1(A_175),C_176),k1_relat_1(A_175))
      | ~ r2_hidden(C_176,k2_relat_1(A_175))
      | ~ v1_funct_1(A_175)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2070,plain,(
    ! [A_54,C_176] :
      ( r2_hidden('#skF_4'('#skF_6'(A_54),k2_relat_1('#skF_6'(A_54)),C_176),A_54)
      | ~ r2_hidden(C_176,k2_relat_1('#skF_6'(A_54)))
      | ~ v1_funct_1('#skF_6'(A_54))
      | ~ v1_relat_1('#skF_6'(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_2055])).

tff(c_2085,plain,(
    ! [A_54,C_176] :
      ( r2_hidden('#skF_4'('#skF_6'(A_54),k2_relat_1('#skF_6'(A_54)),C_176),A_54)
      | ~ r2_hidden(C_176,k2_relat_1('#skF_6'(A_54))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_2070])).

tff(c_46,plain,(
    ! [A_54,C_59] :
      ( k1_funct_1('#skF_6'(A_54),C_59) = k1_xboole_0
      | ~ r2_hidden(C_59,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1557,plain,(
    ! [A_159,C_160] :
      ( k1_funct_1(A_159,'#skF_4'(A_159,k2_relat_1(A_159),C_160)) = C_160
      | ~ r2_hidden(C_160,k2_relat_1(A_159))
      | ~ v1_funct_1(A_159)
      | ~ v1_relat_1(A_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1590,plain,(
    ! [C_160,A_54] :
      ( k1_xboole_0 = C_160
      | ~ r2_hidden(C_160,k2_relat_1('#skF_6'(A_54)))
      | ~ v1_funct_1('#skF_6'(A_54))
      | ~ v1_relat_1('#skF_6'(A_54))
      | ~ r2_hidden('#skF_4'('#skF_6'(A_54),k2_relat_1('#skF_6'(A_54)),C_160),A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_1557])).

tff(c_4232,plain,(
    ! [C_244,A_245] :
      ( k1_xboole_0 = C_244
      | ~ r2_hidden(C_244,k2_relat_1('#skF_6'(A_245)))
      | ~ r2_hidden('#skF_4'('#skF_6'(A_245),k2_relat_1('#skF_6'(A_245)),C_244),A_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1590])).

tff(c_4299,plain,(
    ! [C_246,A_247] :
      ( k1_xboole_0 = C_246
      | ~ r2_hidden(C_246,k2_relat_1('#skF_6'(A_247))) ) ),
    inference(resolution,[status(thm)],[c_2085,c_4232])).

tff(c_4353,plain,(
    ! [C_246,A_101,A_54] :
      ( k1_xboole_0 = C_246
      | ~ r2_hidden(C_246,k2_relat_1('#skF_7'(A_101)))
      | A_101 != '#skF_8'
      | A_54 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_275,c_4299])).

tff(c_5617,plain,(
    ! [A_54] : A_54 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4353])).

tff(c_5621,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_5617])).

tff(c_5624,plain,(
    ! [C_267,A_268] :
      ( k1_xboole_0 = C_267
      | ~ r2_hidden(C_267,k2_relat_1('#skF_7'(A_268)))
      | A_268 != '#skF_8' ) ),
    inference(splitRight,[status(thm)],[c_4353])).

tff(c_5729,plain,(
    ! [B_183] :
      ( np__1 = k1_xboole_0
      | B_183 != '#skF_8'
      | k1_xboole_0 = B_183 ) ),
    inference(resolution,[status(thm)],[c_2205,c_5624])).

tff(c_5740,plain,(
    np__1 = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5729])).

tff(c_5747,plain,(
    ! [B_183] :
      ( r2_hidden(k1_xboole_0,k2_relat_1('#skF_7'(B_183)))
      | k1_xboole_0 = B_183 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5740,c_2205])).

tff(c_507,plain,(
    ! [A_60,A_114,B_115] :
      ( '#skF_7'(A_60) = '#skF_5'(A_114,B_115)
      | A_114 != '#skF_8'
      | A_60 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_56,c_495])).

tff(c_2064,plain,(
    ! [A_47,B_48,C_176] :
      ( r2_hidden('#skF_4'('#skF_5'(A_47,B_48),k2_relat_1('#skF_5'(A_47,B_48)),C_176),A_47)
      | ~ r2_hidden(C_176,k2_relat_1('#skF_5'(A_47,B_48)))
      | ~ v1_funct_1('#skF_5'(A_47,B_48))
      | ~ v1_relat_1('#skF_5'(A_47,B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_2055])).

tff(c_2081,plain,(
    ! [A_47,B_48,C_176] :
      ( r2_hidden('#skF_4'('#skF_5'(A_47,B_48),k2_relat_1('#skF_5'(A_47,B_48)),C_176),A_47)
      | ~ r2_hidden(C_176,k2_relat_1('#skF_5'(A_47,B_48))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_2064])).

tff(c_38,plain,(
    ! [A_47,B_48,D_53] :
      ( k1_funct_1('#skF_5'(A_47,B_48),D_53) = B_48
      | ~ r2_hidden(D_53,A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1567,plain,(
    ! [C_160,B_48,A_47] :
      ( C_160 = B_48
      | ~ r2_hidden('#skF_4'('#skF_5'(A_47,B_48),k2_relat_1('#skF_5'(A_47,B_48)),C_160),A_47)
      | ~ r2_hidden(C_160,k2_relat_1('#skF_5'(A_47,B_48)))
      | ~ v1_funct_1('#skF_5'(A_47,B_48))
      | ~ v1_relat_1('#skF_5'(A_47,B_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1557,c_38])).

tff(c_11400,plain,(
    ! [C_361,B_362,A_363] :
      ( C_361 = B_362
      | ~ r2_hidden('#skF_4'('#skF_5'(A_363,B_362),k2_relat_1('#skF_5'(A_363,B_362)),C_361),A_363)
      | ~ r2_hidden(C_361,k2_relat_1('#skF_5'(A_363,B_362))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_1567])).

tff(c_11467,plain,(
    ! [C_364,B_365,A_366] :
      ( C_364 = B_365
      | ~ r2_hidden(C_364,k2_relat_1('#skF_5'(A_366,B_365))) ) ),
    inference(resolution,[status(thm)],[c_2081,c_11400])).

tff(c_11560,plain,(
    ! [C_364,B_115,A_60,A_114] :
      ( C_364 = B_115
      | ~ r2_hidden(C_364,k2_relat_1('#skF_7'(A_60)))
      | A_114 != '#skF_8'
      | A_60 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_507,c_11467])).

tff(c_11908,plain,(
    ! [A_114] : A_114 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_11560])).

tff(c_11912,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_11908])).

tff(c_11915,plain,(
    ! [C_371,B_372,A_373] :
      ( C_371 = B_372
      | ~ r2_hidden(C_371,k2_relat_1('#skF_7'(A_373)))
      | A_373 != '#skF_8' ) ),
    inference(splitRight,[status(thm)],[c_11560])).

tff(c_12023,plain,(
    ! [B_372,B_183] :
      ( k1_xboole_0 = B_372
      | B_183 != '#skF_8'
      | k1_xboole_0 = B_183 ) ),
    inference(resolution,[status(thm)],[c_5747,c_11915])).

tff(c_12041,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_12023])).

tff(c_12125,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12041,c_2])).

tff(c_12129,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1503,c_12125])).

tff(c_12488,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_12023])).

tff(c_12489,plain,(
    v1_xboole_0('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_12488,c_2])).

tff(c_12510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1503,c_12489])).

tff(c_12586,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5729])).

tff(c_12641,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12586,c_2])).

tff(c_12645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1503,c_12641])).

tff(c_12648,plain,(
    ! [A_2101] :
      ( v1_xboole_0('#skF_7'(A_2101))
      | A_2101 != '#skF_8' ) ),
    inference(splitRight,[status(thm)],[c_1433])).

tff(c_12848,plain,(
    ! [A_2106] :
      ( '#skF_7'(A_2106) = k1_xboole_0
      | A_2106 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_12648,c_4])).

tff(c_12896,plain,(
    ! [A_2106] :
      ( k1_relat_1(k1_xboole_0) = A_2106
      | A_2106 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12848,c_56])).

tff(c_12944,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_12896])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_12975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12944,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:37:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.50/2.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.95/2.87  
% 8.95/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.95/2.88  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_7 > #skF_4 > #skF_3 > #skF_8 > #skF_2 > #skF_1 > #skF_5 > #skF_6
% 8.95/2.88  
% 8.95/2.88  %Foreground sorts:
% 8.95/2.88  
% 8.95/2.88  
% 8.95/2.88  %Background operators:
% 8.95/2.88  
% 8.95/2.88  
% 8.95/2.88  %Foreground operators:
% 8.95/2.88  tff('#skF_7', type, '#skF_7': $i > $i).
% 8.95/2.88  tff(np__1, type, np__1: $i).
% 8.95/2.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.95/2.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.95/2.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.95/2.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.95/2.88  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 8.95/2.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 8.95/2.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.95/2.88  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 8.95/2.88  tff('#skF_8', type, '#skF_8': $i).
% 8.95/2.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.95/2.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.95/2.88  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.95/2.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.95/2.88  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 8.95/2.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.95/2.88  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.95/2.88  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.95/2.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.95/2.88  tff('#skF_6', type, '#skF_6': $i > $i).
% 8.95/2.88  
% 8.95/2.90  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 8.95/2.90  tff(f_101, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = np__1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 8.95/2.90  tff(f_77, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 8.95/2.90  tff(f_120, negated_conjecture, ~(![A]: ((![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((k1_relat_1(B) = A) & (k1_relat_1(C) = A)) => (B = C)))))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 8.95/2.90  tff(f_47, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 8.95/2.90  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.95/2.90  tff(f_39, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 8.95/2.90  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.95/2.90  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.95/2.90  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 8.95/2.90  tff(f_89, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 8.95/2.90  tff(c_18, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.95/2.90  tff(c_58, plain, (![A_60]: (v1_funct_1('#skF_7'(A_60)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.95/2.90  tff(c_56, plain, (![A_60]: (k1_relat_1('#skF_7'(A_60))=A_60)), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.95/2.90  tff(c_60, plain, (![A_60]: (v1_relat_1('#skF_7'(A_60)))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.95/2.90  tff(c_40, plain, (![A_47, B_48]: (k1_relat_1('#skF_5'(A_47, B_48))=A_47)), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.95/2.90  tff(c_42, plain, (![A_47, B_48]: (v1_funct_1('#skF_5'(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.95/2.90  tff(c_120, plain, (![A_84, B_85]: (v1_relat_1('#skF_5'(A_84, B_85)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.95/2.90  tff(c_64, plain, (![C_71, B_69]: (C_71=B_69 | k1_relat_1(C_71)!='#skF_8' | k1_relat_1(B_69)!='#skF_8' | ~v1_funct_1(C_71) | ~v1_relat_1(C_71) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.95/2.90  tff(c_122, plain, (![B_69, A_84, B_85]: (B_69='#skF_5'(A_84, B_85) | k1_relat_1('#skF_5'(A_84, B_85))!='#skF_8' | k1_relat_1(B_69)!='#skF_8' | ~v1_funct_1('#skF_5'(A_84, B_85)) | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(resolution, [status(thm)], [c_120, c_64])).
% 8.95/2.90  tff(c_125, plain, (![B_69, A_84, B_85]: (B_69='#skF_5'(A_84, B_85) | k1_relat_1('#skF_5'(A_84, B_85))!='#skF_8' | k1_relat_1(B_69)!='#skF_8' | ~v1_funct_1(B_69) | ~v1_relat_1(B_69))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_122])).
% 8.95/2.90  tff(c_487, plain, (![B_113, A_114, B_115]: (B_113='#skF_5'(A_114, B_115) | A_114!='#skF_8' | k1_relat_1(B_113)!='#skF_8' | ~v1_funct_1(B_113) | ~v1_relat_1(B_113))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_125])).
% 8.95/2.90  tff(c_495, plain, (![A_60, A_114, B_115]: ('#skF_7'(A_60)='#skF_5'(A_114, B_115) | A_114!='#skF_8' | k1_relat_1('#skF_7'(A_60))!='#skF_8' | ~v1_funct_1('#skF_7'(A_60)))), inference(resolution, [status(thm)], [c_60, c_487])).
% 8.95/2.90  tff(c_1363, plain, (![A_153, A_154, B_155]: ('#skF_7'(A_153)='#skF_5'(A_154, B_155) | A_154!='#skF_8' | A_153!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_495])).
% 8.95/2.90  tff(c_44, plain, (![A_47, B_48]: (v1_relat_1('#skF_5'(A_47, B_48)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.95/2.90  tff(c_176, plain, (![A_94]: (~v1_xboole_0(k1_relat_1(A_94)) | ~v1_relat_1(A_94) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.95/2.90  tff(c_179, plain, (![A_47, B_48]: (~v1_xboole_0(A_47) | ~v1_relat_1('#skF_5'(A_47, B_48)) | v1_xboole_0('#skF_5'(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_176])).
% 8.95/2.90  tff(c_190, plain, (![A_47, B_48]: (~v1_xboole_0(A_47) | v1_xboole_0('#skF_5'(A_47, B_48)))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_179])).
% 8.95/2.90  tff(c_1433, plain, (![A_154, A_153]: (~v1_xboole_0(A_154) | v1_xboole_0('#skF_7'(A_153)) | A_154!='#skF_8' | A_153!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1363, c_190])).
% 8.95/2.90  tff(c_1503, plain, (~v1_xboole_0('#skF_8')), inference(splitLeft, [status(thm)], [c_1433])).
% 8.95/2.90  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 8.95/2.90  tff(c_141, plain, (![A_87, B_88]: (~r2_hidden(A_87, k2_zfmisc_1(A_87, B_88)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.95/2.90  tff(c_144, plain, (![A_2]: (~r2_hidden(A_2, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_141])).
% 8.95/2.90  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 8.95/2.90  tff(c_182, plain, (![A_60]: (~v1_xboole_0(A_60) | ~v1_relat_1('#skF_7'(A_60)) | v1_xboole_0('#skF_7'(A_60)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_176])).
% 8.95/2.90  tff(c_197, plain, (![A_95]: (~v1_xboole_0(A_95) | v1_xboole_0('#skF_7'(A_95)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_182])).
% 8.95/2.90  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.95/2.90  tff(c_207, plain, (![A_97]: ('#skF_7'(A_97)=k1_xboole_0 | ~v1_xboole_0(A_97))), inference(resolution, [status(thm)], [c_197, c_4])).
% 8.95/2.90  tff(c_219, plain, ('#skF_7'(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_207])).
% 8.95/2.90  tff(c_239, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_219, c_60])).
% 8.95/2.90  tff(c_241, plain, (v1_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_219, c_58])).
% 8.95/2.90  tff(c_16, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 8.95/2.90  tff(c_2140, plain, (![A_181, B_182]: (r2_hidden('#skF_2'(A_181, B_182), k1_relat_1(A_181)) | r2_hidden('#skF_3'(A_181, B_182), B_182) | k2_relat_1(A_181)=B_182 | ~v1_funct_1(A_181) | ~v1_relat_1(A_181))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.95/2.90  tff(c_2170, plain, (![B_182]: (r2_hidden('#skF_2'(k1_xboole_0, B_182), k1_xboole_0) | r2_hidden('#skF_3'(k1_xboole_0, B_182), B_182) | k2_relat_1(k1_xboole_0)=B_182 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2140])).
% 8.95/2.90  tff(c_2185, plain, (![B_182]: (r2_hidden('#skF_2'(k1_xboole_0, B_182), k1_xboole_0) | r2_hidden('#skF_3'(k1_xboole_0, B_182), B_182) | k1_xboole_0=B_182)), inference(demodulation, [status(thm), theory('equality')], [c_239, c_241, c_16, c_2170])).
% 8.95/2.90  tff(c_2187, plain, (![B_183]: (r2_hidden('#skF_3'(k1_xboole_0, B_183), B_183) | k1_xboole_0=B_183)), inference(negUnitSimplification, [status(thm)], [c_144, c_2185])).
% 8.95/2.90  tff(c_54, plain, (![A_60, C_65]: (k1_funct_1('#skF_7'(A_60), C_65)=np__1 | ~r2_hidden(C_65, A_60))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.95/2.90  tff(c_1328, plain, (![A_144, D_145]: (r2_hidden(k1_funct_1(A_144, D_145), k2_relat_1(A_144)) | ~r2_hidden(D_145, k1_relat_1(A_144)) | ~v1_funct_1(A_144) | ~v1_relat_1(A_144))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.95/2.90  tff(c_1334, plain, (![A_60, C_65]: (r2_hidden(np__1, k2_relat_1('#skF_7'(A_60))) | ~r2_hidden(C_65, k1_relat_1('#skF_7'(A_60))) | ~v1_funct_1('#skF_7'(A_60)) | ~v1_relat_1('#skF_7'(A_60)) | ~r2_hidden(C_65, A_60))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1328])).
% 8.95/2.90  tff(c_1344, plain, (![A_60, C_65]: (r2_hidden(np__1, k2_relat_1('#skF_7'(A_60))) | ~r2_hidden(C_65, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_56, c_1334])).
% 8.95/2.90  tff(c_2205, plain, (![B_183]: (r2_hidden(np__1, k2_relat_1('#skF_7'(B_183))) | k1_xboole_0=B_183)), inference(resolution, [status(thm)], [c_2187, c_1344])).
% 8.95/2.90  tff(c_50, plain, (![A_54]: (v1_funct_1('#skF_6'(A_54)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.95/2.90  tff(c_48, plain, (![A_54]: (k1_relat_1('#skF_6'(A_54))=A_54)), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.95/2.90  tff(c_52, plain, (![A_54]: (v1_relat_1('#skF_6'(A_54)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.95/2.90  tff(c_84, plain, (![C_77, B_78]: (C_77=B_78 | k1_relat_1(C_77)!='#skF_8' | k1_relat_1(B_78)!='#skF_8' | ~v1_funct_1(C_77) | ~v1_relat_1(C_77) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.95/2.90  tff(c_88, plain, (![B_78, A_60]: (B_78='#skF_7'(A_60) | k1_relat_1('#skF_7'(A_60))!='#skF_8' | k1_relat_1(B_78)!='#skF_8' | ~v1_funct_1('#skF_7'(A_60)) | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_60, c_84])).
% 8.95/2.90  tff(c_94, plain, (![B_78, A_60]: (B_78='#skF_7'(A_60) | k1_relat_1('#skF_7'(A_60))!='#skF_8' | k1_relat_1(B_78)!='#skF_8' | ~v1_funct_1(B_78) | ~v1_relat_1(B_78))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_88])).
% 8.95/2.90  tff(c_258, plain, (![B_100, A_101]: (B_100='#skF_7'(A_101) | A_101!='#skF_8' | k1_relat_1(B_100)!='#skF_8' | ~v1_funct_1(B_100) | ~v1_relat_1(B_100))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_94])).
% 8.95/2.90  tff(c_264, plain, (![A_101, A_54]: ('#skF_7'(A_101)='#skF_6'(A_54) | A_101!='#skF_8' | k1_relat_1('#skF_6'(A_54))!='#skF_8' | ~v1_funct_1('#skF_6'(A_54)))), inference(resolution, [status(thm)], [c_52, c_258])).
% 8.95/2.90  tff(c_275, plain, (![A_101, A_54]: ('#skF_7'(A_101)='#skF_6'(A_54) | A_101!='#skF_8' | A_54!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_264])).
% 8.95/2.90  tff(c_2055, plain, (![A_175, C_176]: (r2_hidden('#skF_4'(A_175, k2_relat_1(A_175), C_176), k1_relat_1(A_175)) | ~r2_hidden(C_176, k2_relat_1(A_175)) | ~v1_funct_1(A_175) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.95/2.90  tff(c_2070, plain, (![A_54, C_176]: (r2_hidden('#skF_4'('#skF_6'(A_54), k2_relat_1('#skF_6'(A_54)), C_176), A_54) | ~r2_hidden(C_176, k2_relat_1('#skF_6'(A_54))) | ~v1_funct_1('#skF_6'(A_54)) | ~v1_relat_1('#skF_6'(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_2055])).
% 8.95/2.90  tff(c_2085, plain, (![A_54, C_176]: (r2_hidden('#skF_4'('#skF_6'(A_54), k2_relat_1('#skF_6'(A_54)), C_176), A_54) | ~r2_hidden(C_176, k2_relat_1('#skF_6'(A_54))))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_2070])).
% 8.95/2.90  tff(c_46, plain, (![A_54, C_59]: (k1_funct_1('#skF_6'(A_54), C_59)=k1_xboole_0 | ~r2_hidden(C_59, A_54))), inference(cnfTransformation, [status(thm)], [f_89])).
% 8.95/2.90  tff(c_1557, plain, (![A_159, C_160]: (k1_funct_1(A_159, '#skF_4'(A_159, k2_relat_1(A_159), C_160))=C_160 | ~r2_hidden(C_160, k2_relat_1(A_159)) | ~v1_funct_1(A_159) | ~v1_relat_1(A_159))), inference(cnfTransformation, [status(thm)], [f_65])).
% 8.95/2.90  tff(c_1590, plain, (![C_160, A_54]: (k1_xboole_0=C_160 | ~r2_hidden(C_160, k2_relat_1('#skF_6'(A_54))) | ~v1_funct_1('#skF_6'(A_54)) | ~v1_relat_1('#skF_6'(A_54)) | ~r2_hidden('#skF_4'('#skF_6'(A_54), k2_relat_1('#skF_6'(A_54)), C_160), A_54))), inference(superposition, [status(thm), theory('equality')], [c_46, c_1557])).
% 8.95/2.90  tff(c_4232, plain, (![C_244, A_245]: (k1_xboole_0=C_244 | ~r2_hidden(C_244, k2_relat_1('#skF_6'(A_245))) | ~r2_hidden('#skF_4'('#skF_6'(A_245), k2_relat_1('#skF_6'(A_245)), C_244), A_245))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1590])).
% 8.95/2.90  tff(c_4299, plain, (![C_246, A_247]: (k1_xboole_0=C_246 | ~r2_hidden(C_246, k2_relat_1('#skF_6'(A_247))))), inference(resolution, [status(thm)], [c_2085, c_4232])).
% 8.95/2.90  tff(c_4353, plain, (![C_246, A_101, A_54]: (k1_xboole_0=C_246 | ~r2_hidden(C_246, k2_relat_1('#skF_7'(A_101))) | A_101!='#skF_8' | A_54!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_275, c_4299])).
% 8.95/2.90  tff(c_5617, plain, (![A_54]: (A_54!='#skF_8')), inference(splitLeft, [status(thm)], [c_4353])).
% 8.95/2.90  tff(c_5621, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_5617])).
% 8.95/2.90  tff(c_5624, plain, (![C_267, A_268]: (k1_xboole_0=C_267 | ~r2_hidden(C_267, k2_relat_1('#skF_7'(A_268))) | A_268!='#skF_8')), inference(splitRight, [status(thm)], [c_4353])).
% 8.95/2.90  tff(c_5729, plain, (![B_183]: (np__1=k1_xboole_0 | B_183!='#skF_8' | k1_xboole_0=B_183)), inference(resolution, [status(thm)], [c_2205, c_5624])).
% 8.95/2.90  tff(c_5740, plain, (np__1=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5729])).
% 8.95/2.90  tff(c_5747, plain, (![B_183]: (r2_hidden(k1_xboole_0, k2_relat_1('#skF_7'(B_183))) | k1_xboole_0=B_183)), inference(demodulation, [status(thm), theory('equality')], [c_5740, c_2205])).
% 8.95/2.90  tff(c_507, plain, (![A_60, A_114, B_115]: ('#skF_7'(A_60)='#skF_5'(A_114, B_115) | A_114!='#skF_8' | A_60!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_56, c_495])).
% 8.95/2.90  tff(c_2064, plain, (![A_47, B_48, C_176]: (r2_hidden('#skF_4'('#skF_5'(A_47, B_48), k2_relat_1('#skF_5'(A_47, B_48)), C_176), A_47) | ~r2_hidden(C_176, k2_relat_1('#skF_5'(A_47, B_48))) | ~v1_funct_1('#skF_5'(A_47, B_48)) | ~v1_relat_1('#skF_5'(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_2055])).
% 8.95/2.90  tff(c_2081, plain, (![A_47, B_48, C_176]: (r2_hidden('#skF_4'('#skF_5'(A_47, B_48), k2_relat_1('#skF_5'(A_47, B_48)), C_176), A_47) | ~r2_hidden(C_176, k2_relat_1('#skF_5'(A_47, B_48))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_2064])).
% 8.95/2.90  tff(c_38, plain, (![A_47, B_48, D_53]: (k1_funct_1('#skF_5'(A_47, B_48), D_53)=B_48 | ~r2_hidden(D_53, A_47))), inference(cnfTransformation, [status(thm)], [f_77])).
% 8.95/2.90  tff(c_1567, plain, (![C_160, B_48, A_47]: (C_160=B_48 | ~r2_hidden('#skF_4'('#skF_5'(A_47, B_48), k2_relat_1('#skF_5'(A_47, B_48)), C_160), A_47) | ~r2_hidden(C_160, k2_relat_1('#skF_5'(A_47, B_48))) | ~v1_funct_1('#skF_5'(A_47, B_48)) | ~v1_relat_1('#skF_5'(A_47, B_48)))), inference(superposition, [status(thm), theory('equality')], [c_1557, c_38])).
% 8.95/2.90  tff(c_11400, plain, (![C_361, B_362, A_363]: (C_361=B_362 | ~r2_hidden('#skF_4'('#skF_5'(A_363, B_362), k2_relat_1('#skF_5'(A_363, B_362)), C_361), A_363) | ~r2_hidden(C_361, k2_relat_1('#skF_5'(A_363, B_362))))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_1567])).
% 8.95/2.90  tff(c_11467, plain, (![C_364, B_365, A_366]: (C_364=B_365 | ~r2_hidden(C_364, k2_relat_1('#skF_5'(A_366, B_365))))), inference(resolution, [status(thm)], [c_2081, c_11400])).
% 8.95/2.90  tff(c_11560, plain, (![C_364, B_115, A_60, A_114]: (C_364=B_115 | ~r2_hidden(C_364, k2_relat_1('#skF_7'(A_60))) | A_114!='#skF_8' | A_60!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_507, c_11467])).
% 8.95/2.90  tff(c_11908, plain, (![A_114]: (A_114!='#skF_8')), inference(splitLeft, [status(thm)], [c_11560])).
% 8.95/2.90  tff(c_11912, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_11908])).
% 8.95/2.90  tff(c_11915, plain, (![C_371, B_372, A_373]: (C_371=B_372 | ~r2_hidden(C_371, k2_relat_1('#skF_7'(A_373))) | A_373!='#skF_8')), inference(splitRight, [status(thm)], [c_11560])).
% 8.95/2.90  tff(c_12023, plain, (![B_372, B_183]: (k1_xboole_0=B_372 | B_183!='#skF_8' | k1_xboole_0=B_183)), inference(resolution, [status(thm)], [c_5747, c_11915])).
% 8.95/2.90  tff(c_12041, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_12023])).
% 8.95/2.90  tff(c_12125, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12041, c_2])).
% 8.95/2.90  tff(c_12129, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1503, c_12125])).
% 8.95/2.90  tff(c_12488, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_12023])).
% 8.95/2.90  tff(c_12489, plain, (v1_xboole_0('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_12488, c_2])).
% 8.95/2.90  tff(c_12510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1503, c_12489])).
% 8.95/2.90  tff(c_12586, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_5729])).
% 8.95/2.90  tff(c_12641, plain, (v1_xboole_0('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_12586, c_2])).
% 8.95/2.90  tff(c_12645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1503, c_12641])).
% 8.95/2.90  tff(c_12648, plain, (![A_2101]: (v1_xboole_0('#skF_7'(A_2101)) | A_2101!='#skF_8')), inference(splitRight, [status(thm)], [c_1433])).
% 8.95/2.90  tff(c_12848, plain, (![A_2106]: ('#skF_7'(A_2106)=k1_xboole_0 | A_2106!='#skF_8')), inference(resolution, [status(thm)], [c_12648, c_4])).
% 8.95/2.90  tff(c_12896, plain, (![A_2106]: (k1_relat_1(k1_xboole_0)=A_2106 | A_2106!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_12848, c_56])).
% 8.95/2.90  tff(c_12944, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_12896])).
% 8.95/2.90  tff(c_62, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.95/2.90  tff(c_12975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12944, c_62])).
% 8.95/2.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.95/2.90  
% 8.95/2.90  Inference rules
% 8.95/2.90  ----------------------
% 8.95/2.90  #Ref     : 3
% 8.95/2.90  #Sup     : 3397
% 8.95/2.90  #Fact    : 0
% 8.95/2.90  #Define  : 0
% 8.95/2.90  #Split   : 5
% 8.95/2.90  #Chain   : 0
% 8.95/2.90  #Close   : 0
% 8.95/2.90  
% 8.95/2.90  Ordering : KBO
% 8.95/2.90  
% 8.95/2.90  Simplification rules
% 8.95/2.90  ----------------------
% 8.95/2.90  #Subsume      : 1747
% 8.95/2.90  #Demod        : 2085
% 8.95/2.90  #Tautology    : 429
% 8.95/2.90  #SimpNegUnit  : 324
% 8.95/2.90  #BackRed      : 179
% 8.95/2.90  
% 8.95/2.90  #Partial instantiations: 89
% 8.95/2.90  #Strategies tried      : 1
% 8.95/2.90  
% 8.95/2.90  Timing (in seconds)
% 8.95/2.90  ----------------------
% 8.95/2.90  Preprocessing        : 0.33
% 8.95/2.90  Parsing              : 0.17
% 8.95/2.90  CNF conversion       : 0.03
% 8.95/2.90  Main loop            : 1.80
% 8.95/2.90  Inferencing          : 0.52
% 8.95/2.90  Reduction            : 0.62
% 8.95/2.90  Demodulation         : 0.44
% 8.95/2.90  BG Simplification    : 0.06
% 8.95/2.90  Subsumption          : 0.47
% 8.95/2.90  Abstraction          : 0.09
% 8.95/2.90  MUC search           : 0.00
% 8.95/2.90  Cooper               : 0.00
% 8.95/2.90  Total                : 2.17
% 8.95/2.90  Index Insertion      : 0.00
% 8.95/2.90  Index Deletion       : 0.00
% 8.95/2.90  Index Matching       : 0.00
% 8.95/2.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
