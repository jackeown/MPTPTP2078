%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:40 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 272 expanded)
%              Number of leaves         :   40 ( 107 expanded)
%              Depth                    :    9
%              Number of atoms          :  179 ( 680 expanded)
%              Number of equality atoms :   18 ( 116 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_10 > #skF_3 > #skF_13 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_12 > #skF_4

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

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i ) > $i )).

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_143,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(C,k1_funct_2(A,B))
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_2)).

tff(f_124,axiom,(
    ! [A,B,C] :
      ( C = k1_funct_2(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E] :
              ( v1_relat_1(E)
              & v1_funct_1(E)
              & D = E
              & k1_relat_1(E) = A
              & r1_tarski(k2_relat_1(E),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
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

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(f_134,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_108,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(c_96,plain,(
    r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_275,plain,(
    ! [A_146,B_147,D_148] :
      ( '#skF_10'(A_146,B_147,k1_funct_2(A_146,B_147),D_148) = D_148
      | ~ r2_hidden(D_148,k1_funct_2(A_146,B_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_286,plain,(
    '#skF_10'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_96,c_275])).

tff(c_297,plain,(
    ! [A_152,B_153,D_154] :
      ( v1_relat_1('#skF_10'(A_152,B_153,k1_funct_2(A_152,B_153),D_154))
      | ~ r2_hidden(D_154,k1_funct_2(A_152,B_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_300,plain,
    ( v1_relat_1('#skF_13')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_297])).

tff(c_302,plain,(
    v1_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_300])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_311,plain,(
    ! [A_157,B_158,D_159] :
      ( k1_relat_1('#skF_10'(A_157,B_158,k1_funct_2(A_157,B_158),D_159)) = A_157
      | ~ r2_hidden(D_159,k1_funct_2(A_157,B_158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_335,plain,
    ( k1_relat_1('#skF_13') = '#skF_11'
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_311])).

tff(c_339,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_335])).

tff(c_523,plain,(
    ! [A_179,B_180,D_181] :
      ( r1_tarski(k2_relat_1('#skF_10'(A_179,B_180,k1_funct_2(A_179,B_180),D_181)),B_180)
      | ~ r2_hidden(D_181,k1_funct_2(A_179,B_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_539,plain,
    ( r1_tarski(k2_relat_1('#skF_13'),'#skF_12')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_523])).

tff(c_545,plain,(
    r1_tarski(k2_relat_1('#skF_13'),'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_539])).

tff(c_698,plain,(
    ! [C_206,A_207,B_208] :
      ( m1_subset_1(C_206,k1_zfmisc_1(k2_zfmisc_1(A_207,B_208)))
      | ~ r1_tarski(k2_relat_1(C_206),B_208)
      | ~ r1_tarski(k1_relat_1(C_206),A_207)
      | ~ v1_relat_1(C_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_94,plain,
    ( ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12')))
    | ~ v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_funct_1('#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_122,plain,(
    ~ v1_funct_1('#skF_13') ),
    inference(splitLeft,[status(thm)],[c_94])).

tff(c_184,plain,(
    ! [A_124,B_125,D_126] :
      ( '#skF_10'(A_124,B_125,k1_funct_2(A_124,B_125),D_126) = D_126
      | ~ r2_hidden(D_126,k1_funct_2(A_124,B_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_195,plain,(
    '#skF_10'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_96,c_184])).

tff(c_60,plain,(
    ! [A_68,B_69,D_84] :
      ( v1_funct_1('#skF_10'(A_68,B_69,k1_funct_2(A_68,B_69),D_84))
      | ~ r2_hidden(D_84,k1_funct_2(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_199,plain,
    ( v1_funct_1('#skF_13')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_60])).

tff(c_206,plain,(
    v1_funct_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_199])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_206])).

tff(c_209,plain,
    ( ~ v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_221,plain,(
    ~ m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_707,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_13'),'#skF_12')
    | ~ r1_tarski(k1_relat_1('#skF_13'),'#skF_11')
    | ~ v1_relat_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_698,c_221])).

tff(c_716,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_10,c_339,c_545,c_707])).

tff(c_717,plain,(
    ~ v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_210,plain,(
    v1_funct_1('#skF_13') ),
    inference(splitRight,[status(thm)],[c_94])).

tff(c_718,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11','#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_738,plain,(
    ! [C_214,A_215,B_216] :
      ( v1_partfun1(C_214,A_215)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_215,B_216)))
      | ~ v1_xboole_0(A_215) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_750,plain,
    ( v1_partfun1('#skF_13','#skF_11')
    | ~ v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_718,c_738])).

tff(c_753,plain,(
    ~ v1_xboole_0('#skF_11') ),
    inference(splitLeft,[status(thm)],[c_750])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_786,plain,(
    ! [A_229,B_230,D_231] :
      ( '#skF_10'(A_229,B_230,k1_funct_2(A_229,B_230),D_231) = D_231
      | ~ r2_hidden(D_231,k1_funct_2(A_229,B_230)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_797,plain,(
    '#skF_10'('#skF_11','#skF_12',k1_funct_2('#skF_11','#skF_12'),'#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_96,c_786])).

tff(c_62,plain,(
    ! [A_68,B_69,D_84] :
      ( v1_relat_1('#skF_10'(A_68,B_69,k1_funct_2(A_68,B_69),D_84))
      | ~ r2_hidden(D_84,k1_funct_2(A_68,B_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_801,plain,
    ( v1_relat_1('#skF_13')
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_62])).

tff(c_805,plain,(
    v1_relat_1('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_801])).

tff(c_827,plain,(
    ! [A_241,B_242,D_243] :
      ( k1_relat_1('#skF_10'(A_241,B_242,k1_funct_2(A_241,B_242),D_243)) = A_241
      | ~ r2_hidden(D_243,k1_funct_2(A_241,B_242)) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_854,plain,
    ( k1_relat_1('#skF_13') = '#skF_11'
    | ~ r2_hidden('#skF_13',k1_funct_2('#skF_11','#skF_12')) ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_827])).

tff(c_858,plain,(
    k1_relat_1('#skF_13') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_854])).

tff(c_822,plain,(
    ! [A_239,D_240] :
      ( r2_hidden(k1_funct_1(A_239,D_240),k2_relat_1(A_239))
      | ~ r2_hidden(D_240,k1_relat_1(A_239))
      | ~ v1_funct_1(A_239)
      | ~ v1_relat_1(A_239) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_937,plain,(
    ! [A_249,D_250] :
      ( ~ v1_xboole_0(k2_relat_1(A_249))
      | ~ r2_hidden(D_250,k1_relat_1(A_249))
      | ~ v1_funct_1(A_249)
      | ~ v1_relat_1(A_249) ) ),
    inference(resolution,[status(thm)],[c_822,c_2])).

tff(c_944,plain,(
    ! [D_250] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_13'))
      | ~ r2_hidden(D_250,'#skF_11')
      | ~ v1_funct_1('#skF_13')
      | ~ v1_relat_1('#skF_13') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_937])).

tff(c_958,plain,(
    ! [D_250] :
      ( ~ v1_xboole_0(k2_relat_1('#skF_13'))
      | ~ r2_hidden(D_250,'#skF_11') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_210,c_944])).

tff(c_961,plain,(
    ~ v1_xboole_0(k2_relat_1('#skF_13')) ),
    inference(splitLeft,[status(thm)],[c_958])).

tff(c_1036,plain,(
    ! [C_265,A_266,B_267] :
      ( v1_funct_2(C_265,A_266,B_267)
      | ~ v1_partfun1(C_265,A_266)
      | ~ v1_funct_1(C_265)
      | ~ m1_subset_1(C_265,k1_zfmisc_1(k2_zfmisc_1(A_266,B_267))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1045,plain,
    ( v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_partfun1('#skF_13','#skF_11')
    | ~ v1_funct_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_718,c_1036])).

tff(c_1060,plain,
    ( v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_partfun1('#skF_13','#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1045])).

tff(c_1061,plain,(
    ~ v1_partfun1('#skF_13','#skF_11') ),
    inference(negUnitSimplification,[status(thm)],[c_717,c_1060])).

tff(c_90,plain,(
    ! [A_88] :
      ( v1_funct_2(A_88,k1_relat_1(A_88),k2_relat_1(A_88))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_874,plain,
    ( v1_funct_2('#skF_13','#skF_11',k2_relat_1('#skF_13'))
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_90])).

tff(c_889,plain,(
    v1_funct_2('#skF_13','#skF_11',k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_210,c_874])).

tff(c_88,plain,(
    ! [A_88] :
      ( m1_subset_1(A_88,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_88),k2_relat_1(A_88))))
      | ~ v1_funct_1(A_88)
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_871,plain,
    ( m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',k2_relat_1('#skF_13'))))
    | ~ v1_funct_1('#skF_13')
    | ~ v1_relat_1('#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_858,c_88])).

tff(c_887,plain,(
    m1_subset_1('#skF_13',k1_zfmisc_1(k2_zfmisc_1('#skF_11',k2_relat_1('#skF_13')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_805,c_210,c_871])).

tff(c_1367,plain,(
    ! [C_310,A_311,B_312] :
      ( v1_partfun1(C_310,A_311)
      | ~ v1_funct_2(C_310,A_311,B_312)
      | ~ v1_funct_1(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_311,B_312)))
      | v1_xboole_0(B_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1373,plain,
    ( v1_partfun1('#skF_13','#skF_11')
    | ~ v1_funct_2('#skF_13','#skF_11',k2_relat_1('#skF_13'))
    | ~ v1_funct_1('#skF_13')
    | v1_xboole_0(k2_relat_1('#skF_13')) ),
    inference(resolution,[status(thm)],[c_887,c_1367])).

tff(c_1391,plain,
    ( v1_partfun1('#skF_13','#skF_11')
    | v1_xboole_0(k2_relat_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_889,c_1373])).

tff(c_1393,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_961,c_1061,c_1391])).

tff(c_1396,plain,(
    ! [D_313] : ~ r2_hidden(D_313,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_958])).

tff(c_1408,plain,(
    v1_xboole_0('#skF_11') ),
    inference(resolution,[status(thm)],[c_4,c_1396])).

tff(c_1416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_753,c_1408])).

tff(c_1417,plain,(
    v1_partfun1('#skF_13','#skF_11') ),
    inference(splitRight,[status(thm)],[c_750])).

tff(c_1636,plain,(
    ! [C_352,A_353,B_354] :
      ( v1_funct_2(C_352,A_353,B_354)
      | ~ v1_partfun1(C_352,A_353)
      | ~ v1_funct_1(C_352)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_353,B_354))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1645,plain,
    ( v1_funct_2('#skF_13','#skF_11','#skF_12')
    | ~ v1_partfun1('#skF_13','#skF_11')
    | ~ v1_funct_1('#skF_13') ),
    inference(resolution,[status(thm)],[c_718,c_1636])).

tff(c_1660,plain,(
    v1_funct_2('#skF_13','#skF_11','#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_1417,c_1645])).

tff(c_1662,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_717,c_1660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:36:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.63  
% 3.65/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.63  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_11 > #skF_6 > #skF_1 > #skF_10 > #skF_3 > #skF_13 > #skF_7 > #skF_9 > #skF_8 > #skF_5 > #skF_12 > #skF_4
% 3.65/1.63  
% 3.65/1.63  %Foreground sorts:
% 3.65/1.63  
% 3.65/1.63  
% 3.65/1.63  %Background operators:
% 3.65/1.63  
% 3.65/1.63  
% 3.65/1.63  %Foreground operators:
% 3.65/1.63  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.65/1.63  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.65/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.65/1.63  tff('#skF_11', type, '#skF_11': $i).
% 3.65/1.63  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.65/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.65/1.63  tff('#skF_10', type, '#skF_10': ($i * $i * $i * $i) > $i).
% 3.65/1.63  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.65/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.63  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.65/1.63  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.65/1.63  tff('#skF_13', type, '#skF_13': $i).
% 3.65/1.63  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.65/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.63  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 3.65/1.63  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.65/1.63  tff('#skF_9', type, '#skF_9': ($i * $i * $i) > $i).
% 3.65/1.63  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 3.65/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.65/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.65/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.63  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 3.65/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.65/1.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.65/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.65/1.63  tff('#skF_12', type, '#skF_12': $i).
% 3.65/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.65/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.63  
% 3.65/1.64  tff(f_143, negated_conjecture, ~(![A, B, C]: (r2_hidden(C, k1_funct_2(A, B)) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_2)).
% 3.65/1.64  tff(f_124, axiom, (![A, B, C]: ((C = k1_funct_2(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: ((((v1_relat_1(E) & v1_funct_1(E)) & (D = E)) & (k1_relat_1(E) = A)) & r1_tarski(k2_relat_1(E), B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_funct_2)).
% 3.65/1.64  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.65/1.64  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 3.65/1.64  tff(f_94, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.65/1.65  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.65/1.65  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_funct_1)).
% 3.65/1.65  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 3.65/1.65  tff(f_134, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.65/1.65  tff(f_108, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.65/1.65  tff(c_96, plain, (r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.65/1.65  tff(c_275, plain, (![A_146, B_147, D_148]: ('#skF_10'(A_146, B_147, k1_funct_2(A_146, B_147), D_148)=D_148 | ~r2_hidden(D_148, k1_funct_2(A_146, B_147)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_286, plain, ('#skF_10'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_96, c_275])).
% 3.65/1.65  tff(c_297, plain, (![A_152, B_153, D_154]: (v1_relat_1('#skF_10'(A_152, B_153, k1_funct_2(A_152, B_153), D_154)) | ~r2_hidden(D_154, k1_funct_2(A_152, B_153)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_300, plain, (v1_relat_1('#skF_13') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_297])).
% 3.65/1.65  tff(c_302, plain, (v1_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_300])).
% 3.65/1.65  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.65/1.65  tff(c_311, plain, (![A_157, B_158, D_159]: (k1_relat_1('#skF_10'(A_157, B_158, k1_funct_2(A_157, B_158), D_159))=A_157 | ~r2_hidden(D_159, k1_funct_2(A_157, B_158)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_335, plain, (k1_relat_1('#skF_13')='#skF_11' | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_311])).
% 3.65/1.65  tff(c_339, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_335])).
% 3.65/1.65  tff(c_523, plain, (![A_179, B_180, D_181]: (r1_tarski(k2_relat_1('#skF_10'(A_179, B_180, k1_funct_2(A_179, B_180), D_181)), B_180) | ~r2_hidden(D_181, k1_funct_2(A_179, B_180)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_539, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_523])).
% 3.65/1.65  tff(c_545, plain, (r1_tarski(k2_relat_1('#skF_13'), '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_539])).
% 3.65/1.65  tff(c_698, plain, (![C_206, A_207, B_208]: (m1_subset_1(C_206, k1_zfmisc_1(k2_zfmisc_1(A_207, B_208))) | ~r1_tarski(k2_relat_1(C_206), B_208) | ~r1_tarski(k1_relat_1(C_206), A_207) | ~v1_relat_1(C_206))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.65/1.65  tff(c_94, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12'))) | ~v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_funct_1('#skF_13')), inference(cnfTransformation, [status(thm)], [f_143])).
% 3.65/1.65  tff(c_122, plain, (~v1_funct_1('#skF_13')), inference(splitLeft, [status(thm)], [c_94])).
% 3.65/1.65  tff(c_184, plain, (![A_124, B_125, D_126]: ('#skF_10'(A_124, B_125, k1_funct_2(A_124, B_125), D_126)=D_126 | ~r2_hidden(D_126, k1_funct_2(A_124, B_125)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_195, plain, ('#skF_10'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_96, c_184])).
% 3.65/1.65  tff(c_60, plain, (![A_68, B_69, D_84]: (v1_funct_1('#skF_10'(A_68, B_69, k1_funct_2(A_68, B_69), D_84)) | ~r2_hidden(D_84, k1_funct_2(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_199, plain, (v1_funct_1('#skF_13') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_195, c_60])).
% 3.65/1.65  tff(c_206, plain, (v1_funct_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_199])).
% 3.65/1.65  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_122, c_206])).
% 3.65/1.65  tff(c_209, plain, (~v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitRight, [status(thm)], [c_94])).
% 3.65/1.65  tff(c_221, plain, (~m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitLeft, [status(thm)], [c_209])).
% 3.65/1.65  tff(c_707, plain, (~r1_tarski(k2_relat_1('#skF_13'), '#skF_12') | ~r1_tarski(k1_relat_1('#skF_13'), '#skF_11') | ~v1_relat_1('#skF_13')), inference(resolution, [status(thm)], [c_698, c_221])).
% 3.65/1.65  tff(c_716, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_302, c_10, c_339, c_545, c_707])).
% 3.65/1.65  tff(c_717, plain, (~v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(splitRight, [status(thm)], [c_209])).
% 3.65/1.65  tff(c_210, plain, (v1_funct_1('#skF_13')), inference(splitRight, [status(thm)], [c_94])).
% 3.65/1.65  tff(c_718, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', '#skF_12')))), inference(splitRight, [status(thm)], [c_209])).
% 3.65/1.65  tff(c_738, plain, (![C_214, A_215, B_216]: (v1_partfun1(C_214, A_215) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_215, B_216))) | ~v1_xboole_0(A_215))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.65/1.65  tff(c_750, plain, (v1_partfun1('#skF_13', '#skF_11') | ~v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_718, c_738])).
% 3.65/1.65  tff(c_753, plain, (~v1_xboole_0('#skF_11')), inference(splitLeft, [status(thm)], [c_750])).
% 3.65/1.65  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.65  tff(c_786, plain, (![A_229, B_230, D_231]: ('#skF_10'(A_229, B_230, k1_funct_2(A_229, B_230), D_231)=D_231 | ~r2_hidden(D_231, k1_funct_2(A_229, B_230)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_797, plain, ('#skF_10'('#skF_11', '#skF_12', k1_funct_2('#skF_11', '#skF_12'), '#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_96, c_786])).
% 3.65/1.65  tff(c_62, plain, (![A_68, B_69, D_84]: (v1_relat_1('#skF_10'(A_68, B_69, k1_funct_2(A_68, B_69), D_84)) | ~r2_hidden(D_84, k1_funct_2(A_68, B_69)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_801, plain, (v1_relat_1('#skF_13') | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_797, c_62])).
% 3.65/1.65  tff(c_805, plain, (v1_relat_1('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_801])).
% 3.65/1.65  tff(c_827, plain, (![A_241, B_242, D_243]: (k1_relat_1('#skF_10'(A_241, B_242, k1_funct_2(A_241, B_242), D_243))=A_241 | ~r2_hidden(D_243, k1_funct_2(A_241, B_242)))), inference(cnfTransformation, [status(thm)], [f_124])).
% 3.65/1.65  tff(c_854, plain, (k1_relat_1('#skF_13')='#skF_11' | ~r2_hidden('#skF_13', k1_funct_2('#skF_11', '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_797, c_827])).
% 3.65/1.65  tff(c_858, plain, (k1_relat_1('#skF_13')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_854])).
% 3.65/1.65  tff(c_822, plain, (![A_239, D_240]: (r2_hidden(k1_funct_1(A_239, D_240), k2_relat_1(A_239)) | ~r2_hidden(D_240, k1_relat_1(A_239)) | ~v1_funct_1(A_239) | ~v1_relat_1(A_239))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.65/1.65  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.65  tff(c_937, plain, (![A_249, D_250]: (~v1_xboole_0(k2_relat_1(A_249)) | ~r2_hidden(D_250, k1_relat_1(A_249)) | ~v1_funct_1(A_249) | ~v1_relat_1(A_249))), inference(resolution, [status(thm)], [c_822, c_2])).
% 3.65/1.65  tff(c_944, plain, (![D_250]: (~v1_xboole_0(k2_relat_1('#skF_13')) | ~r2_hidden(D_250, '#skF_11') | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13'))), inference(superposition, [status(thm), theory('equality')], [c_858, c_937])).
% 3.65/1.65  tff(c_958, plain, (![D_250]: (~v1_xboole_0(k2_relat_1('#skF_13')) | ~r2_hidden(D_250, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_805, c_210, c_944])).
% 3.65/1.65  tff(c_961, plain, (~v1_xboole_0(k2_relat_1('#skF_13'))), inference(splitLeft, [status(thm)], [c_958])).
% 3.65/1.65  tff(c_1036, plain, (![C_265, A_266, B_267]: (v1_funct_2(C_265, A_266, B_267) | ~v1_partfun1(C_265, A_266) | ~v1_funct_1(C_265) | ~m1_subset_1(C_265, k1_zfmisc_1(k2_zfmisc_1(A_266, B_267))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.65/1.65  tff(c_1045, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_partfun1('#skF_13', '#skF_11') | ~v1_funct_1('#skF_13')), inference(resolution, [status(thm)], [c_718, c_1036])).
% 3.65/1.65  tff(c_1060, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_partfun1('#skF_13', '#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1045])).
% 3.65/1.65  tff(c_1061, plain, (~v1_partfun1('#skF_13', '#skF_11')), inference(negUnitSimplification, [status(thm)], [c_717, c_1060])).
% 3.65/1.65  tff(c_90, plain, (![A_88]: (v1_funct_2(A_88, k1_relat_1(A_88), k2_relat_1(A_88)) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.65/1.65  tff(c_874, plain, (v1_funct_2('#skF_13', '#skF_11', k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_858, c_90])).
% 3.65/1.65  tff(c_889, plain, (v1_funct_2('#skF_13', '#skF_11', k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_805, c_210, c_874])).
% 3.65/1.65  tff(c_88, plain, (![A_88]: (m1_subset_1(A_88, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_88), k2_relat_1(A_88)))) | ~v1_funct_1(A_88) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_134])).
% 3.65/1.65  tff(c_871, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', k2_relat_1('#skF_13')))) | ~v1_funct_1('#skF_13') | ~v1_relat_1('#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_858, c_88])).
% 3.65/1.65  tff(c_887, plain, (m1_subset_1('#skF_13', k1_zfmisc_1(k2_zfmisc_1('#skF_11', k2_relat_1('#skF_13'))))), inference(demodulation, [status(thm), theory('equality')], [c_805, c_210, c_871])).
% 3.65/1.65  tff(c_1367, plain, (![C_310, A_311, B_312]: (v1_partfun1(C_310, A_311) | ~v1_funct_2(C_310, A_311, B_312) | ~v1_funct_1(C_310) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_311, B_312))) | v1_xboole_0(B_312))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.65/1.65  tff(c_1373, plain, (v1_partfun1('#skF_13', '#skF_11') | ~v1_funct_2('#skF_13', '#skF_11', k2_relat_1('#skF_13')) | ~v1_funct_1('#skF_13') | v1_xboole_0(k2_relat_1('#skF_13'))), inference(resolution, [status(thm)], [c_887, c_1367])).
% 3.65/1.65  tff(c_1391, plain, (v1_partfun1('#skF_13', '#skF_11') | v1_xboole_0(k2_relat_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_889, c_1373])).
% 3.65/1.65  tff(c_1393, plain, $false, inference(negUnitSimplification, [status(thm)], [c_961, c_1061, c_1391])).
% 3.65/1.65  tff(c_1396, plain, (![D_313]: (~r2_hidden(D_313, '#skF_11'))), inference(splitRight, [status(thm)], [c_958])).
% 3.65/1.65  tff(c_1408, plain, (v1_xboole_0('#skF_11')), inference(resolution, [status(thm)], [c_4, c_1396])).
% 3.65/1.65  tff(c_1416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_753, c_1408])).
% 3.65/1.65  tff(c_1417, plain, (v1_partfun1('#skF_13', '#skF_11')), inference(splitRight, [status(thm)], [c_750])).
% 3.65/1.65  tff(c_1636, plain, (![C_352, A_353, B_354]: (v1_funct_2(C_352, A_353, B_354) | ~v1_partfun1(C_352, A_353) | ~v1_funct_1(C_352) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_353, B_354))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.65/1.65  tff(c_1645, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12') | ~v1_partfun1('#skF_13', '#skF_11') | ~v1_funct_1('#skF_13')), inference(resolution, [status(thm)], [c_718, c_1636])).
% 3.65/1.65  tff(c_1660, plain, (v1_funct_2('#skF_13', '#skF_11', '#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_1417, c_1645])).
% 3.65/1.65  tff(c_1662, plain, $false, inference(negUnitSimplification, [status(thm)], [c_717, c_1660])).
% 3.65/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.65/1.65  
% 3.65/1.65  Inference rules
% 3.65/1.65  ----------------------
% 3.65/1.65  #Ref     : 0
% 3.65/1.65  #Sup     : 341
% 3.65/1.65  #Fact    : 0
% 3.65/1.65  #Define  : 0
% 3.65/1.65  #Split   : 15
% 3.65/1.65  #Chain   : 0
% 3.65/1.65  #Close   : 0
% 3.65/1.65  
% 3.65/1.65  Ordering : KBO
% 3.65/1.65  
% 3.65/1.65  Simplification rules
% 3.65/1.65  ----------------------
% 3.65/1.65  #Subsume      : 56
% 3.65/1.65  #Demod        : 121
% 3.65/1.65  #Tautology    : 67
% 3.65/1.65  #SimpNegUnit  : 7
% 3.65/1.65  #BackRed      : 0
% 3.65/1.65  
% 3.65/1.65  #Partial instantiations: 0
% 3.65/1.65  #Strategies tried      : 1
% 3.65/1.65  
% 3.65/1.65  Timing (in seconds)
% 3.65/1.65  ----------------------
% 3.65/1.65  Preprocessing        : 0.37
% 3.65/1.65  Parsing              : 0.18
% 3.65/1.65  CNF conversion       : 0.03
% 3.65/1.65  Main loop            : 0.49
% 3.65/1.65  Inferencing          : 0.19
% 3.65/1.65  Reduction            : 0.14
% 3.65/1.65  Demodulation         : 0.09
% 3.65/1.65  BG Simplification    : 0.03
% 3.65/1.65  Subsumption          : 0.08
% 3.65/1.65  Abstraction          : 0.03
% 3.65/1.65  MUC search           : 0.00
% 3.65/1.65  Cooper               : 0.00
% 3.65/1.65  Total                : 0.91
% 3.65/1.65  Index Insertion      : 0.00
% 3.65/1.65  Index Deletion       : 0.00
% 3.65/1.65  Index Matching       : 0.00
% 3.65/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
