%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:10 EST 2020

% Result     : Theorem 9.55s
% Output     : CNFRefutation 9.55s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 498 expanded)
%              Number of leaves         :   36 ( 171 expanded)
%              Depth                    :   15
%              Number of atoms          :  220 (1275 expanded)
%              Number of equality atoms :  120 ( 733 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_8',type,(
    '#skF_8': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_112,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_81,axiom,(
    ! [A] :
    ? [B] :
      ( v1_relat_1(B)
      & v1_funct_1(B)
      & k1_relat_1(B) = A
      & ! [C] :
          ( r2_hidden(C,A)
         => k1_funct_1(B,C) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_94,axiom,(
    ! [A] :
      ( A != k1_xboole_0
     => ! [B] :
        ? [C] :
          ( v1_relat_1(C)
          & v1_funct_1(C)
          & k1_relat_1(C) = A
          & k2_relat_1(C) = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_61,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_11'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_90,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_52,plain,(
    ! [A_36] : k1_relat_1('#skF_8'(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1241,plain,(
    ! [A_187,B_188] :
      ( r2_hidden(k4_tarski('#skF_4'(A_187,B_188),'#skF_5'(A_187,B_188)),A_187)
      | r2_hidden('#skF_6'(A_187,B_188),B_188)
      | k1_relat_1(A_187) = B_188 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,(
    ! [C_31,A_16,D_34] :
      ( r2_hidden(C_31,k1_relat_1(A_16))
      | ~ r2_hidden(k4_tarski(C_31,D_34),A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_2028,plain,(
    ! [A_230,B_231] :
      ( r2_hidden('#skF_4'(A_230,B_231),k1_relat_1(A_230))
      | r2_hidden('#skF_6'(A_230,B_231),B_231)
      | k1_relat_1(A_230) = B_231 ) ),
    inference(resolution,[status(thm)],[c_1241,c_32])).

tff(c_2099,plain,(
    ! [A_36,B_231] :
      ( r2_hidden('#skF_4'('#skF_8'(A_36),B_231),A_36)
      | r2_hidden('#skF_6'('#skF_8'(A_36),B_231),B_231)
      | k1_relat_1('#skF_8'(A_36)) = B_231 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_2028])).

tff(c_17106,plain,(
    ! [A_6587,B_6588] :
      ( r2_hidden('#skF_4'('#skF_8'(A_6587),B_6588),A_6587)
      | r2_hidden('#skF_6'('#skF_8'(A_6587),B_6588),B_6588)
      | B_6588 = A_6587 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2099])).

tff(c_24,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_119,plain,(
    ! [A_58,B_59] : ~ r2_hidden(A_58,k2_zfmisc_1(A_58,B_59)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_125,plain,(
    ! [A_12] : ~ r2_hidden(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_119])).

tff(c_17319,plain,(
    ! [A_6587] :
      ( r2_hidden('#skF_4'('#skF_8'(A_6587),k1_xboole_0),A_6587)
      | k1_xboole_0 = A_6587 ) ),
    inference(resolution,[status(thm)],[c_17106,c_125])).

tff(c_60,plain,(
    ! [A_42,B_46] :
      ( k1_relat_1('#skF_9'(A_42,B_46)) = A_42
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_62,plain,(
    ! [A_42,B_46] :
      ( v1_funct_1('#skF_9'(A_42,B_46))
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_64,plain,(
    ! [A_42,B_46] :
      ( v1_relat_1('#skF_9'(A_42,B_46))
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_281,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_1'(A_78,B_79),A_78)
      | r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_354,plain,(
    ! [A_101,B_102] :
      ( '#skF_1'(k1_tarski(A_101),B_102) = A_101
      | r1_tarski(k1_tarski(A_101),B_102) ) ),
    inference(resolution,[status(thm)],[c_281,c_10])).

tff(c_269,plain,(
    ! [A_76,B_77] :
      ( k2_relat_1('#skF_9'(A_76,B_77)) = k1_tarski(B_77)
      | k1_xboole_0 = A_76 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_66,plain,(
    ! [C_49] :
      ( ~ r1_tarski(k2_relat_1(C_49),'#skF_10')
      | k1_relat_1(C_49) != '#skF_11'
      | ~ v1_funct_1(C_49)
      | ~ v1_relat_1(C_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_275,plain,(
    ! [B_77,A_76] :
      ( ~ r1_tarski(k1_tarski(B_77),'#skF_10')
      | k1_relat_1('#skF_9'(A_76,B_77)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_76,B_77))
      | ~ v1_relat_1('#skF_9'(A_76,B_77))
      | k1_xboole_0 = A_76 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_66])).

tff(c_379,plain,(
    ! [A_105,A_106] :
      ( k1_relat_1('#skF_9'(A_105,A_106)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_105,A_106))
      | ~ v1_relat_1('#skF_9'(A_105,A_106))
      | k1_xboole_0 = A_105
      | '#skF_1'(k1_tarski(A_106),'#skF_10') = A_106 ) ),
    inference(resolution,[status(thm)],[c_354,c_275])).

tff(c_479,plain,(
    ! [A_127,B_128] :
      ( k1_relat_1('#skF_9'(A_127,B_128)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_127,B_128))
      | '#skF_1'(k1_tarski(B_128),'#skF_10') = B_128
      | k1_xboole_0 = A_127 ) ),
    inference(resolution,[status(thm)],[c_64,c_379])).

tff(c_864,plain,(
    ! [A_158,B_159] :
      ( k1_relat_1('#skF_9'(A_158,B_159)) != '#skF_11'
      | '#skF_1'(k1_tarski(B_159),'#skF_10') = B_159
      | k1_xboole_0 = A_158 ) ),
    inference(resolution,[status(thm)],[c_62,c_479])).

tff(c_867,plain,(
    ! [A_42,B_46] :
      ( A_42 != '#skF_11'
      | '#skF_1'(k1_tarski(B_46),'#skF_10') = B_46
      | k1_xboole_0 = A_42
      | k1_xboole_0 = A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_864])).

tff(c_869,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_867])).

tff(c_44,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_91,plain,(
    ! [C_55] :
      ( ~ r1_tarski(k2_relat_1(C_55),'#skF_10')
      | k1_relat_1(C_55) != '#skF_11'
      | ~ v1_funct_1(C_55)
      | ~ v1_relat_1(C_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_94,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_10')
    | k1_relat_1(k1_xboole_0) != '#skF_11'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_91])).

tff(c_96,plain,
    ( k1_xboole_0 != '#skF_11'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_8,c_94])).

tff(c_135,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_96])).

tff(c_56,plain,(
    ! [A_36] : v1_relat_1('#skF_8'(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_145,plain,(
    ! [A_68] :
      ( k1_relat_1(A_68) != k1_xboole_0
      | k1_xboole_0 = A_68
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_151,plain,(
    ! [A_36] :
      ( k1_relat_1('#skF_8'(A_36)) != k1_xboole_0
      | '#skF_8'(A_36) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_56,c_145])).

tff(c_156,plain,(
    ! [A_69] :
      ( k1_xboole_0 != A_69
      | '#skF_8'(A_69) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_151])).

tff(c_166,plain,(
    ! [A_69] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_69 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_56])).

tff(c_172,plain,(
    ! [A_69] : k1_xboole_0 != A_69 ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_166])).

tff(c_26,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_26])).

tff(c_184,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | k1_xboole_0 != '#skF_11' ),
    inference(splitRight,[status(thm)],[c_96])).

tff(c_202,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_905,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_202])).

tff(c_908,plain,(
    ! [B_160] : '#skF_1'(k1_tarski(B_160),'#skF_10') = B_160 ),
    inference(splitRight,[status(thm)],[c_867])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_942,plain,(
    ! [B_161] :
      ( ~ r2_hidden(B_161,'#skF_10')
      | r1_tarski(k1_tarski(B_161),'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_908,c_4])).

tff(c_1097,plain,(
    ! [A_176,B_177] :
      ( k1_relat_1('#skF_9'(A_176,B_177)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_176,B_177))
      | ~ v1_relat_1('#skF_9'(A_176,B_177))
      | k1_xboole_0 = A_176
      | ~ r2_hidden(B_177,'#skF_10') ) ),
    inference(resolution,[status(thm)],[c_942,c_275])).

tff(c_2816,plain,(
    ! [A_254,B_255] :
      ( k1_relat_1('#skF_9'(A_254,B_255)) != '#skF_11'
      | ~ v1_funct_1('#skF_9'(A_254,B_255))
      | ~ r2_hidden(B_255,'#skF_10')
      | k1_xboole_0 = A_254 ) ),
    inference(resolution,[status(thm)],[c_64,c_1097])).

tff(c_18501,plain,(
    ! [A_7081,B_7082] :
      ( k1_relat_1('#skF_9'(A_7081,B_7082)) != '#skF_11'
      | ~ r2_hidden(B_7082,'#skF_10')
      | k1_xboole_0 = A_7081 ) ),
    inference(resolution,[status(thm)],[c_62,c_2816])).

tff(c_18527,plain,(
    ! [A_42,B_46] :
      ( A_42 != '#skF_11'
      | ~ r2_hidden(B_46,'#skF_10')
      | k1_xboole_0 = A_42
      | k1_xboole_0 = A_42 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_18501])).

tff(c_18771,plain,(
    ! [B_7169] : ~ r2_hidden(B_7169,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_18527])).

tff(c_18775,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_17319,c_18771])).

tff(c_18843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_18775])).

tff(c_18845,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_18527])).

tff(c_19027,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18845,c_202])).

tff(c_19029,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_19028,plain,(
    ~ v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_19030,plain,(
    ~ v1_funct_1('#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19029,c_19028])).

tff(c_48,plain,(
    ! [A_35] :
      ( k1_relat_1(A_35) != k1_xboole_0
      | k1_xboole_0 = A_35
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_19083,plain,(
    ! [A_7202] :
      ( k1_relat_1(A_7202) != '#skF_11'
      | A_7202 = '#skF_11'
      | ~ v1_relat_1(A_7202) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19029,c_19029,c_48])).

tff(c_19089,plain,(
    ! [A_36] :
      ( k1_relat_1('#skF_8'(A_36)) != '#skF_11'
      | '#skF_8'(A_36) = '#skF_11' ) ),
    inference(resolution,[status(thm)],[c_56,c_19083])).

tff(c_19115,plain,(
    ! [A_7204] :
      ( A_7204 != '#skF_11'
      | '#skF_8'(A_7204) = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_19089])).

tff(c_54,plain,(
    ! [A_36] : v1_funct_1('#skF_8'(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_19123,plain,(
    ! [A_7204] :
      ( v1_funct_1('#skF_11')
      | A_7204 != '#skF_11' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19115,c_54])).

tff(c_19131,plain,(
    ! [A_7204] : A_7204 != '#skF_11' ),
    inference(negUnitSimplification,[status(thm)],[c_19030,c_19123])).

tff(c_19036,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_11',B_13) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19029,c_19029,c_26])).

tff(c_19142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19131,c_19036])).

tff(c_19144,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_19143,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_19152,plain,(
    '#skF_11' = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19144,c_19143])).

tff(c_19147,plain,(
    k1_relat_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_19143,c_44])).

tff(c_19161,plain,(
    k1_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19152,c_19152,c_19147])).

tff(c_19145,plain,(
    ! [A_6] : r1_tarski('#skF_11',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_8])).

tff(c_19171,plain,(
    ! [A_6] : r1_tarski('#skF_10',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19152,c_19145])).

tff(c_19146,plain,(
    k2_relat_1('#skF_11') = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19143,c_19143,c_42])).

tff(c_19166,plain,(
    k2_relat_1('#skF_10') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19152,c_19152,c_19146])).

tff(c_19174,plain,(
    ! [C_7206] :
      ( ~ r1_tarski(k2_relat_1(C_7206),'#skF_10')
      | k1_relat_1(C_7206) != '#skF_10'
      | ~ v1_funct_1(C_7206)
      | ~ v1_relat_1(C_7206) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19152,c_66])).

tff(c_19177,plain,
    ( ~ r1_tarski('#skF_10','#skF_10')
    | k1_relat_1('#skF_10') != '#skF_10'
    | ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(superposition,[status(thm),theory(equality)],[c_19166,c_19174])).

tff(c_19179,plain,
    ( ~ v1_funct_1('#skF_10')
    | ~ v1_relat_1('#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19161,c_19171,c_19177])).

tff(c_19204,plain,(
    ~ v1_relat_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_19179])).

tff(c_19245,plain,(
    ! [A_7221] :
      ( k1_relat_1(A_7221) != '#skF_10'
      | A_7221 = '#skF_10'
      | ~ v1_relat_1(A_7221) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19144,c_19144,c_48])).

tff(c_19251,plain,(
    ! [A_36] :
      ( k1_relat_1('#skF_8'(A_36)) != '#skF_10'
      | '#skF_8'(A_36) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_56,c_19245])).

tff(c_19256,plain,(
    ! [A_7222] :
      ( A_7222 != '#skF_10'
      | '#skF_8'(A_7222) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_19251])).

tff(c_19266,plain,(
    ! [A_7222] :
      ( v1_relat_1('#skF_10')
      | A_7222 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19256,c_56])).

tff(c_19272,plain,(
    ! [A_7222] : A_7222 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_19204,c_19266])).

tff(c_19188,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_10',B_13) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19144,c_19144,c_26])).

tff(c_19286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19272,c_19188])).

tff(c_19287,plain,(
    ~ v1_funct_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_19179])).

tff(c_19308,plain,(
    ! [A_7232] :
      ( k1_relat_1(A_7232) != '#skF_10'
      | A_7232 = '#skF_10'
      | ~ v1_relat_1(A_7232) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19144,c_19144,c_48])).

tff(c_19317,plain,(
    ! [A_36] :
      ( k1_relat_1('#skF_8'(A_36)) != '#skF_10'
      | '#skF_8'(A_36) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_56,c_19308])).

tff(c_19326,plain,(
    ! [A_7233] :
      ( A_7233 != '#skF_10'
      | '#skF_8'(A_7233) = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_19317])).

tff(c_19334,plain,(
    ! [A_7233] :
      ( v1_funct_1('#skF_10')
      | A_7233 != '#skF_10' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_19326,c_54])).

tff(c_19342,plain,(
    ! [A_7233] : A_7233 != '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_19287,c_19334])).

tff(c_19367,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19342,c_19188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.55/3.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.51  
% 9.55/3.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.51  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_11 > #skF_8 > #skF_3 > #skF_10 > #skF_7 > #skF_2 > #skF_1 > #skF_9 > #skF_5 > #skF_4
% 9.55/3.51  
% 9.55/3.51  %Foreground sorts:
% 9.55/3.51  
% 9.55/3.51  
% 9.55/3.51  %Background operators:
% 9.55/3.51  
% 9.55/3.51  
% 9.55/3.51  %Foreground operators:
% 9.55/3.51  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 9.55/3.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.55/3.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.55/3.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.55/3.51  tff('#skF_11', type, '#skF_11': $i).
% 9.55/3.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.55/3.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.55/3.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.55/3.51  tff('#skF_8', type, '#skF_8': $i > $i).
% 9.55/3.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 9.55/3.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.55/3.51  tff('#skF_10', type, '#skF_10': $i).
% 9.55/3.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.55/3.51  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 9.55/3.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 9.55/3.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.55/3.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.55/3.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.55/3.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.55/3.51  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 9.55/3.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.55/3.51  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 9.55/3.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 9.55/3.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.55/3.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 9.55/3.51  
% 9.55/3.53  tff(f_112, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_funct_1)).
% 9.55/3.53  tff(f_81, axiom, (![A]: (?[B]: (((v1_relat_1(B) & v1_funct_1(B)) & (k1_relat_1(B) = A)) & (![C]: (r2_hidden(C, A) => (k1_funct_1(B, C) = k1_xboole_0)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 9.55/3.53  tff(f_58, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 9.55/3.53  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.55/3.53  tff(f_50, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 9.55/3.53  tff(f_94, axiom, (![A]: (~(A = k1_xboole_0) => (![B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (k2_relat_1(C) = k1_tarski(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_funct_1)).
% 9.55/3.53  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.55/3.53  tff(f_41, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 9.55/3.53  tff(f_61, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 9.55/3.53  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.55/3.53  tff(f_69, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 9.55/3.53  tff(c_68, plain, (k1_xboole_0='#skF_11' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.55/3.53  tff(c_90, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_68])).
% 9.55/3.53  tff(c_52, plain, (![A_36]: (k1_relat_1('#skF_8'(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.55/3.53  tff(c_1241, plain, (![A_187, B_188]: (r2_hidden(k4_tarski('#skF_4'(A_187, B_188), '#skF_5'(A_187, B_188)), A_187) | r2_hidden('#skF_6'(A_187, B_188), B_188) | k1_relat_1(A_187)=B_188)), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.55/3.53  tff(c_32, plain, (![C_31, A_16, D_34]: (r2_hidden(C_31, k1_relat_1(A_16)) | ~r2_hidden(k4_tarski(C_31, D_34), A_16))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.55/3.53  tff(c_2028, plain, (![A_230, B_231]: (r2_hidden('#skF_4'(A_230, B_231), k1_relat_1(A_230)) | r2_hidden('#skF_6'(A_230, B_231), B_231) | k1_relat_1(A_230)=B_231)), inference(resolution, [status(thm)], [c_1241, c_32])).
% 9.55/3.53  tff(c_2099, plain, (![A_36, B_231]: (r2_hidden('#skF_4'('#skF_8'(A_36), B_231), A_36) | r2_hidden('#skF_6'('#skF_8'(A_36), B_231), B_231) | k1_relat_1('#skF_8'(A_36))=B_231)), inference(superposition, [status(thm), theory('equality')], [c_52, c_2028])).
% 9.55/3.53  tff(c_17106, plain, (![A_6587, B_6588]: (r2_hidden('#skF_4'('#skF_8'(A_6587), B_6588), A_6587) | r2_hidden('#skF_6'('#skF_8'(A_6587), B_6588), B_6588) | B_6588=A_6587)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2099])).
% 9.55/3.53  tff(c_24, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.55/3.53  tff(c_119, plain, (![A_58, B_59]: (~r2_hidden(A_58, k2_zfmisc_1(A_58, B_59)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.55/3.53  tff(c_125, plain, (![A_12]: (~r2_hidden(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_119])).
% 9.55/3.53  tff(c_17319, plain, (![A_6587]: (r2_hidden('#skF_4'('#skF_8'(A_6587), k1_xboole_0), A_6587) | k1_xboole_0=A_6587)), inference(resolution, [status(thm)], [c_17106, c_125])).
% 9.55/3.53  tff(c_60, plain, (![A_42, B_46]: (k1_relat_1('#skF_9'(A_42, B_46))=A_42 | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.55/3.53  tff(c_62, plain, (![A_42, B_46]: (v1_funct_1('#skF_9'(A_42, B_46)) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.55/3.53  tff(c_64, plain, (![A_42, B_46]: (v1_relat_1('#skF_9'(A_42, B_46)) | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.55/3.53  tff(c_281, plain, (![A_78, B_79]: (r2_hidden('#skF_1'(A_78, B_79), A_78) | r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.55/3.53  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.55/3.53  tff(c_354, plain, (![A_101, B_102]: ('#skF_1'(k1_tarski(A_101), B_102)=A_101 | r1_tarski(k1_tarski(A_101), B_102))), inference(resolution, [status(thm)], [c_281, c_10])).
% 9.55/3.53  tff(c_269, plain, (![A_76, B_77]: (k2_relat_1('#skF_9'(A_76, B_77))=k1_tarski(B_77) | k1_xboole_0=A_76)), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.55/3.53  tff(c_66, plain, (![C_49]: (~r1_tarski(k2_relat_1(C_49), '#skF_10') | k1_relat_1(C_49)!='#skF_11' | ~v1_funct_1(C_49) | ~v1_relat_1(C_49))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.55/3.53  tff(c_275, plain, (![B_77, A_76]: (~r1_tarski(k1_tarski(B_77), '#skF_10') | k1_relat_1('#skF_9'(A_76, B_77))!='#skF_11' | ~v1_funct_1('#skF_9'(A_76, B_77)) | ~v1_relat_1('#skF_9'(A_76, B_77)) | k1_xboole_0=A_76)), inference(superposition, [status(thm), theory('equality')], [c_269, c_66])).
% 9.55/3.53  tff(c_379, plain, (![A_105, A_106]: (k1_relat_1('#skF_9'(A_105, A_106))!='#skF_11' | ~v1_funct_1('#skF_9'(A_105, A_106)) | ~v1_relat_1('#skF_9'(A_105, A_106)) | k1_xboole_0=A_105 | '#skF_1'(k1_tarski(A_106), '#skF_10')=A_106)), inference(resolution, [status(thm)], [c_354, c_275])).
% 9.55/3.53  tff(c_479, plain, (![A_127, B_128]: (k1_relat_1('#skF_9'(A_127, B_128))!='#skF_11' | ~v1_funct_1('#skF_9'(A_127, B_128)) | '#skF_1'(k1_tarski(B_128), '#skF_10')=B_128 | k1_xboole_0=A_127)), inference(resolution, [status(thm)], [c_64, c_379])).
% 9.55/3.53  tff(c_864, plain, (![A_158, B_159]: (k1_relat_1('#skF_9'(A_158, B_159))!='#skF_11' | '#skF_1'(k1_tarski(B_159), '#skF_10')=B_159 | k1_xboole_0=A_158)), inference(resolution, [status(thm)], [c_62, c_479])).
% 9.55/3.53  tff(c_867, plain, (![A_42, B_46]: (A_42!='#skF_11' | '#skF_1'(k1_tarski(B_46), '#skF_10')=B_46 | k1_xboole_0=A_42 | k1_xboole_0=A_42)), inference(superposition, [status(thm), theory('equality')], [c_60, c_864])).
% 9.55/3.53  tff(c_869, plain, (k1_xboole_0='#skF_11'), inference(splitLeft, [status(thm)], [c_867])).
% 9.55/3.53  tff(c_44, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.55/3.53  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.55/3.53  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.55/3.53  tff(c_91, plain, (![C_55]: (~r1_tarski(k2_relat_1(C_55), '#skF_10') | k1_relat_1(C_55)!='#skF_11' | ~v1_funct_1(C_55) | ~v1_relat_1(C_55))), inference(cnfTransformation, [status(thm)], [f_112])).
% 9.55/3.53  tff(c_94, plain, (~r1_tarski(k1_xboole_0, '#skF_10') | k1_relat_1(k1_xboole_0)!='#skF_11' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_91])).
% 9.55/3.53  tff(c_96, plain, (k1_xboole_0!='#skF_11' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_8, c_94])).
% 9.55/3.53  tff(c_135, plain, (~v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_96])).
% 9.55/3.53  tff(c_56, plain, (![A_36]: (v1_relat_1('#skF_8'(A_36)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.55/3.53  tff(c_145, plain, (![A_68]: (k1_relat_1(A_68)!=k1_xboole_0 | k1_xboole_0=A_68 | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.55/3.53  tff(c_151, plain, (![A_36]: (k1_relat_1('#skF_8'(A_36))!=k1_xboole_0 | '#skF_8'(A_36)=k1_xboole_0)), inference(resolution, [status(thm)], [c_56, c_145])).
% 9.55/3.53  tff(c_156, plain, (![A_69]: (k1_xboole_0!=A_69 | '#skF_8'(A_69)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_151])).
% 9.55/3.53  tff(c_166, plain, (![A_69]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_69)), inference(superposition, [status(thm), theory('equality')], [c_156, c_56])).
% 9.55/3.53  tff(c_172, plain, (![A_69]: (k1_xboole_0!=A_69)), inference(negUnitSimplification, [status(thm)], [c_135, c_166])).
% 9.55/3.53  tff(c_26, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.55/3.53  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_26])).
% 9.55/3.53  tff(c_184, plain, (~v1_funct_1(k1_xboole_0) | k1_xboole_0!='#skF_11'), inference(splitRight, [status(thm)], [c_96])).
% 9.55/3.53  tff(c_202, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_184])).
% 9.55/3.53  tff(c_905, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_869, c_202])).
% 9.55/3.53  tff(c_908, plain, (![B_160]: ('#skF_1'(k1_tarski(B_160), '#skF_10')=B_160)), inference(splitRight, [status(thm)], [c_867])).
% 9.55/3.53  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.55/3.53  tff(c_942, plain, (![B_161]: (~r2_hidden(B_161, '#skF_10') | r1_tarski(k1_tarski(B_161), '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_908, c_4])).
% 9.55/3.53  tff(c_1097, plain, (![A_176, B_177]: (k1_relat_1('#skF_9'(A_176, B_177))!='#skF_11' | ~v1_funct_1('#skF_9'(A_176, B_177)) | ~v1_relat_1('#skF_9'(A_176, B_177)) | k1_xboole_0=A_176 | ~r2_hidden(B_177, '#skF_10'))), inference(resolution, [status(thm)], [c_942, c_275])).
% 9.55/3.53  tff(c_2816, plain, (![A_254, B_255]: (k1_relat_1('#skF_9'(A_254, B_255))!='#skF_11' | ~v1_funct_1('#skF_9'(A_254, B_255)) | ~r2_hidden(B_255, '#skF_10') | k1_xboole_0=A_254)), inference(resolution, [status(thm)], [c_64, c_1097])).
% 9.55/3.53  tff(c_18501, plain, (![A_7081, B_7082]: (k1_relat_1('#skF_9'(A_7081, B_7082))!='#skF_11' | ~r2_hidden(B_7082, '#skF_10') | k1_xboole_0=A_7081)), inference(resolution, [status(thm)], [c_62, c_2816])).
% 9.55/3.53  tff(c_18527, plain, (![A_42, B_46]: (A_42!='#skF_11' | ~r2_hidden(B_46, '#skF_10') | k1_xboole_0=A_42 | k1_xboole_0=A_42)), inference(superposition, [status(thm), theory('equality')], [c_60, c_18501])).
% 9.55/3.53  tff(c_18771, plain, (![B_7169]: (~r2_hidden(B_7169, '#skF_10'))), inference(splitLeft, [status(thm)], [c_18527])).
% 9.55/3.53  tff(c_18775, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_17319, c_18771])).
% 9.55/3.53  tff(c_18843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_90, c_18775])).
% 9.55/3.53  tff(c_18845, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_18527])).
% 9.55/3.53  tff(c_19027, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18845, c_202])).
% 9.55/3.53  tff(c_19029, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_184])).
% 9.55/3.53  tff(c_19028, plain, (~v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_184])).
% 9.55/3.53  tff(c_19030, plain, (~v1_funct_1('#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_19029, c_19028])).
% 9.55/3.53  tff(c_48, plain, (![A_35]: (k1_relat_1(A_35)!=k1_xboole_0 | k1_xboole_0=A_35 | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 9.55/3.53  tff(c_19083, plain, (![A_7202]: (k1_relat_1(A_7202)!='#skF_11' | A_7202='#skF_11' | ~v1_relat_1(A_7202))), inference(demodulation, [status(thm), theory('equality')], [c_19029, c_19029, c_48])).
% 9.55/3.53  tff(c_19089, plain, (![A_36]: (k1_relat_1('#skF_8'(A_36))!='#skF_11' | '#skF_8'(A_36)='#skF_11')), inference(resolution, [status(thm)], [c_56, c_19083])).
% 9.55/3.53  tff(c_19115, plain, (![A_7204]: (A_7204!='#skF_11' | '#skF_8'(A_7204)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_19089])).
% 9.55/3.53  tff(c_54, plain, (![A_36]: (v1_funct_1('#skF_8'(A_36)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.55/3.53  tff(c_19123, plain, (![A_7204]: (v1_funct_1('#skF_11') | A_7204!='#skF_11')), inference(superposition, [status(thm), theory('equality')], [c_19115, c_54])).
% 9.55/3.53  tff(c_19131, plain, (![A_7204]: (A_7204!='#skF_11')), inference(negUnitSimplification, [status(thm)], [c_19030, c_19123])).
% 9.55/3.53  tff(c_19036, plain, (![B_13]: (k2_zfmisc_1('#skF_11', B_13)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_19029, c_19029, c_26])).
% 9.55/3.53  tff(c_19142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19131, c_19036])).
% 9.55/3.53  tff(c_19144, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_68])).
% 9.55/3.53  tff(c_19143, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_68])).
% 9.55/3.53  tff(c_19152, plain, ('#skF_11'='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_19144, c_19143])).
% 9.55/3.53  tff(c_19147, plain, (k1_relat_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_19143, c_44])).
% 9.55/3.53  tff(c_19161, plain, (k1_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_19152, c_19152, c_19147])).
% 9.55/3.53  tff(c_19145, plain, (![A_6]: (r1_tarski('#skF_11', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_8])).
% 9.55/3.53  tff(c_19171, plain, (![A_6]: (r1_tarski('#skF_10', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_19152, c_19145])).
% 9.55/3.53  tff(c_19146, plain, (k2_relat_1('#skF_11')='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_19143, c_19143, c_42])).
% 9.55/3.53  tff(c_19166, plain, (k2_relat_1('#skF_10')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_19152, c_19152, c_19146])).
% 9.55/3.53  tff(c_19174, plain, (![C_7206]: (~r1_tarski(k2_relat_1(C_7206), '#skF_10') | k1_relat_1(C_7206)!='#skF_10' | ~v1_funct_1(C_7206) | ~v1_relat_1(C_7206))), inference(demodulation, [status(thm), theory('equality')], [c_19152, c_66])).
% 9.55/3.53  tff(c_19177, plain, (~r1_tarski('#skF_10', '#skF_10') | k1_relat_1('#skF_10')!='#skF_10' | ~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_19166, c_19174])).
% 9.55/3.53  tff(c_19179, plain, (~v1_funct_1('#skF_10') | ~v1_relat_1('#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_19161, c_19171, c_19177])).
% 9.55/3.53  tff(c_19204, plain, (~v1_relat_1('#skF_10')), inference(splitLeft, [status(thm)], [c_19179])).
% 9.55/3.53  tff(c_19245, plain, (![A_7221]: (k1_relat_1(A_7221)!='#skF_10' | A_7221='#skF_10' | ~v1_relat_1(A_7221))), inference(demodulation, [status(thm), theory('equality')], [c_19144, c_19144, c_48])).
% 9.55/3.53  tff(c_19251, plain, (![A_36]: (k1_relat_1('#skF_8'(A_36))!='#skF_10' | '#skF_8'(A_36)='#skF_10')), inference(resolution, [status(thm)], [c_56, c_19245])).
% 9.55/3.53  tff(c_19256, plain, (![A_7222]: (A_7222!='#skF_10' | '#skF_8'(A_7222)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_19251])).
% 9.55/3.53  tff(c_19266, plain, (![A_7222]: (v1_relat_1('#skF_10') | A_7222!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_19256, c_56])).
% 9.55/3.53  tff(c_19272, plain, (![A_7222]: (A_7222!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_19204, c_19266])).
% 9.55/3.53  tff(c_19188, plain, (![B_13]: (k2_zfmisc_1('#skF_10', B_13)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_19144, c_19144, c_26])).
% 9.55/3.53  tff(c_19286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19272, c_19188])).
% 9.55/3.53  tff(c_19287, plain, (~v1_funct_1('#skF_10')), inference(splitRight, [status(thm)], [c_19179])).
% 9.55/3.53  tff(c_19308, plain, (![A_7232]: (k1_relat_1(A_7232)!='#skF_10' | A_7232='#skF_10' | ~v1_relat_1(A_7232))), inference(demodulation, [status(thm), theory('equality')], [c_19144, c_19144, c_48])).
% 9.55/3.53  tff(c_19317, plain, (![A_36]: (k1_relat_1('#skF_8'(A_36))!='#skF_10' | '#skF_8'(A_36)='#skF_10')), inference(resolution, [status(thm)], [c_56, c_19308])).
% 9.55/3.53  tff(c_19326, plain, (![A_7233]: (A_7233!='#skF_10' | '#skF_8'(A_7233)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_19317])).
% 9.55/3.53  tff(c_19334, plain, (![A_7233]: (v1_funct_1('#skF_10') | A_7233!='#skF_10')), inference(superposition, [status(thm), theory('equality')], [c_19326, c_54])).
% 9.55/3.53  tff(c_19342, plain, (![A_7233]: (A_7233!='#skF_10')), inference(negUnitSimplification, [status(thm)], [c_19287, c_19334])).
% 9.55/3.53  tff(c_19367, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19342, c_19188])).
% 9.55/3.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.55/3.53  
% 9.55/3.53  Inference rules
% 9.55/3.53  ----------------------
% 9.55/3.53  #Ref     : 5
% 9.55/3.53  #Sup     : 4481
% 9.55/3.53  #Fact    : 0
% 9.55/3.53  #Define  : 0
% 9.55/3.53  #Split   : 7
% 9.55/3.53  #Chain   : 0
% 9.55/3.53  #Close   : 0
% 9.55/3.53  
% 9.55/3.53  Ordering : KBO
% 9.55/3.53  
% 9.55/3.53  Simplification rules
% 9.55/3.53  ----------------------
% 9.55/3.53  #Subsume      : 2179
% 9.55/3.53  #Demod        : 1979
% 9.55/3.53  #Tautology    : 1505
% 9.55/3.53  #SimpNegUnit  : 134
% 9.55/3.53  #BackRed      : 268
% 9.55/3.53  
% 9.55/3.53  #Partial instantiations: 4410
% 9.55/3.53  #Strategies tried      : 1
% 9.55/3.53  
% 9.55/3.53  Timing (in seconds)
% 9.55/3.53  ----------------------
% 9.55/3.54  Preprocessing        : 0.34
% 9.55/3.54  Parsing              : 0.18
% 9.55/3.54  CNF conversion       : 0.03
% 9.55/3.54  Main loop            : 2.37
% 9.55/3.54  Inferencing          : 0.70
% 9.55/3.54  Reduction            : 0.69
% 9.55/3.54  Demodulation         : 0.47
% 9.55/3.54  BG Simplification    : 0.06
% 9.55/3.54  Subsumption          : 0.80
% 9.55/3.54  Abstraction          : 0.09
% 9.55/3.54  MUC search           : 0.00
% 9.55/3.54  Cooper               : 0.00
% 9.55/3.54  Total                : 2.76
% 9.55/3.54  Index Insertion      : 0.00
% 9.55/3.54  Index Deletion       : 0.00
% 9.55/3.54  Index Matching       : 0.00
% 9.55/3.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
