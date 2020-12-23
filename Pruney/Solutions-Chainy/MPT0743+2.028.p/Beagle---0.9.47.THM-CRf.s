%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:12 EST 2020

% Result     : Theorem 22.36s
% Output     : CNFRefutation 22.36s
% Verified   : 
% Statistics : Number of formulae       :  169 (1781 expanded)
%              Number of leaves         :   23 ( 567 expanded)
%              Depth                    :   21
%              Number of atoms          :  305 (4389 expanded)
%              Number of equality atoms :   24 ( 320 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ( r2_hidden(A,B)
            <=> r1_ordinal1(k1_ordinal1(A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

tff(f_67,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => v3_ordinal1(k1_ordinal1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r2_hidden(A,k1_ordinal1(B))
    <=> ( r2_hidden(A,B)
        | A = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_38,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(c_36,plain,(
    v3_ordinal1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [A_17] :
      ( v3_ordinal1(k1_ordinal1(A_17))
      | ~ v3_ordinal1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_44,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_65,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_38,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_90,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_38])).

tff(c_34,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_193,plain,(
    ! [A_48,B_49] :
      ( r1_tarski(A_48,B_49)
      | ~ r1_ordinal1(A_48,B_49)
      | ~ v3_ordinal1(B_49)
      | ~ v3_ordinal1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    ! [B_16] : r2_hidden(B_16,k1_ordinal1(B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_122,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_134,plain,(
    ! [B_16,B_39] :
      ( r2_hidden(B_16,B_39)
      | ~ r1_tarski(k1_ordinal1(B_16),B_39) ) ),
    inference(resolution,[status(thm)],[c_28,c_122])).

tff(c_1397,plain,(
    ! [B_136,B_137] :
      ( r2_hidden(B_136,B_137)
      | ~ r1_ordinal1(k1_ordinal1(B_136),B_137)
      | ~ v3_ordinal1(B_137)
      | ~ v3_ordinal1(k1_ordinal1(B_136)) ) ),
    inference(resolution,[status(thm)],[c_193,c_134])).

tff(c_1408,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_65,c_1397])).

tff(c_1415,plain,
    ( r2_hidden('#skF_3','#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1408])).

tff(c_1416,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_90,c_1415])).

tff(c_1474,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_1416])).

tff(c_1478,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1474])).

tff(c_1480,plain,(
    ~ r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1483,plain,(
    ! [A_140] :
      ( v3_ordinal1(k1_ordinal1(A_140))
      | ~ v3_ordinal1(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_6] :
      ( v1_ordinal1(A_6)
      | ~ v3_ordinal1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1490,plain,(
    ! [A_140] :
      ( v1_ordinal1(k1_ordinal1(A_140))
      | ~ v3_ordinal1(A_140) ) ),
    inference(resolution,[status(thm)],[c_1483,c_10])).

tff(c_1507,plain,(
    ! [B_150,A_151] :
      ( r1_tarski(B_150,A_151)
      | ~ r2_hidden(B_150,A_151)
      | ~ v1_ordinal1(A_151) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1529,plain,(
    ! [B_16] :
      ( r1_tarski(B_16,k1_ordinal1(B_16))
      | ~ v1_ordinal1(k1_ordinal1(B_16)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1507])).

tff(c_1563,plain,(
    ! [C_158,B_159,A_160] :
      ( r2_hidden(C_158,B_159)
      | ~ r2_hidden(C_158,A_160)
      | ~ r1_tarski(A_160,B_159) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1615,plain,(
    ! [B_166,B_167] :
      ( r2_hidden(B_166,B_167)
      | ~ r1_tarski(k1_ordinal1(B_166),B_167) ) ),
    inference(resolution,[status(thm)],[c_28,c_1563])).

tff(c_1661,plain,(
    ! [B_173] :
      ( r2_hidden(B_173,k1_ordinal1(k1_ordinal1(B_173)))
      | ~ v1_ordinal1(k1_ordinal1(k1_ordinal1(B_173))) ) ),
    inference(resolution,[status(thm)],[c_1529,c_1615])).

tff(c_14,plain,(
    ! [B_11,A_8] :
      ( r1_tarski(B_11,A_8)
      | ~ r2_hidden(B_11,A_8)
      | ~ v1_ordinal1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1698,plain,(
    ! [B_176] :
      ( r1_tarski(B_176,k1_ordinal1(k1_ordinal1(B_176)))
      | ~ v1_ordinal1(k1_ordinal1(k1_ordinal1(B_176))) ) ),
    inference(resolution,[status(thm)],[c_1661,c_14])).

tff(c_1479,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_1595,plain,(
    ! [B_164] :
      ( r2_hidden('#skF_3',B_164)
      | ~ r1_tarski('#skF_4',B_164) ) ),
    inference(resolution,[status(thm)],[c_1479,c_1563])).

tff(c_26,plain,(
    ! [B_16,A_15] :
      ( B_16 = A_15
      | r2_hidden(A_15,B_16)
      | ~ r2_hidden(A_15,k1_ordinal1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1606,plain,(
    ! [B_16] :
      ( B_16 = '#skF_3'
      | r2_hidden('#skF_3',B_16)
      | ~ r1_tarski('#skF_4',k1_ordinal1(B_16)) ) ),
    inference(resolution,[status(thm)],[c_1595,c_26])).

tff(c_1713,plain,
    ( k1_ordinal1('#skF_4') = '#skF_3'
    | r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | ~ v1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_1698,c_1606])).

tff(c_1890,plain,(
    ~ v1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1713])).

tff(c_1894,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1490,c_1890])).

tff(c_1897,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_1894])).

tff(c_1901,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1897])).

tff(c_1902,plain,
    ( r2_hidden('#skF_3',k1_ordinal1('#skF_4'))
    | k1_ordinal1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1713])).

tff(c_1904,plain,(
    k1_ordinal1('#skF_4') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1902])).

tff(c_1903,plain,(
    v1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1713])).

tff(c_1905,plain,(
    v1_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1904,c_1903])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_30,plain,(
    ! [A_15,B_16] :
      ( ~ r2_hidden(A_15,B_16)
      | r2_hidden(A_15,k1_ordinal1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1531,plain,(
    ! [A_153,B_154] :
      ( ~ r2_hidden('#skF_1'(A_153,B_154),B_154)
      | r1_tarski(A_153,B_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1724,plain,(
    ! [A_179,B_180] :
      ( r1_tarski(A_179,k1_ordinal1(B_180))
      | ~ r2_hidden('#skF_1'(A_179,k1_ordinal1(B_180)),B_180) ) ),
    inference(resolution,[status(thm)],[c_30,c_1531])).

tff(c_1748,plain,(
    ! [A_182] : r1_tarski(A_182,k1_ordinal1(A_182)) ),
    inference(resolution,[status(thm)],[c_6,c_1724])).

tff(c_1578,plain,(
    ! [B_16,B_159] :
      ( r2_hidden(B_16,B_159)
      | ~ r1_tarski(k1_ordinal1(B_16),B_159) ) ),
    inference(resolution,[status(thm)],[c_28,c_1563])).

tff(c_1765,plain,(
    ! [B_16] : r2_hidden(B_16,k1_ordinal1(k1_ordinal1(B_16))) ),
    inference(resolution,[status(thm)],[c_1748,c_1578])).

tff(c_1929,plain,(
    r2_hidden('#skF_4',k1_ordinal1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1904,c_1765])).

tff(c_2100,plain,
    ( r1_tarski('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v1_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1929,c_14])).

tff(c_2106,plain,(
    r1_tarski('#skF_4',k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1905,c_2100])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_ordinal1(A_12,B_13)
      | ~ r1_tarski(A_12,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2114,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2106,c_20])).

tff(c_2123,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2114])).

tff(c_2602,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2123])).

tff(c_2605,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_2602])).

tff(c_2609,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2605])).

tff(c_2611,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2123])).

tff(c_1543,plain,(
    ! [B_156,A_157] :
      ( B_156 = A_157
      | r2_hidden(A_157,B_156)
      | ~ r2_hidden(A_157,k1_ordinal1(B_156)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2470,plain,(
    ! [B_216,B_217] :
      ( '#skF_1'(k1_ordinal1(B_216),B_217) = B_216
      | r2_hidden('#skF_1'(k1_ordinal1(B_216),B_217),B_216)
      | r1_tarski(k1_ordinal1(B_216),B_217) ) ),
    inference(resolution,[status(thm)],[c_6,c_1543])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2501,plain,(
    ! [B_216] :
      ( '#skF_1'(k1_ordinal1(B_216),B_216) = B_216
      | r1_tarski(k1_ordinal1(B_216),B_216) ) ),
    inference(resolution,[status(thm)],[c_2470,c_4])).

tff(c_56,plain,(
    ! [A_21] :
      ( v1_ordinal1(A_21)
      | ~ v3_ordinal1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_63,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_56])).

tff(c_1519,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1479,c_1507])).

tff(c_1528,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_1519])).

tff(c_2070,plain,(
    ! [A_199,B_200,B_201] :
      ( r2_hidden('#skF_1'(A_199,B_200),B_201)
      | ~ r1_tarski(A_199,B_201)
      | r1_tarski(A_199,B_200) ) ),
    inference(resolution,[status(thm)],[c_6,c_1563])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5921,plain,(
    ! [A_324,B_325,B_326,B_327] :
      ( r2_hidden('#skF_1'(A_324,B_325),B_326)
      | ~ r1_tarski(B_327,B_326)
      | ~ r1_tarski(A_324,B_327)
      | r1_tarski(A_324,B_325) ) ),
    inference(resolution,[status(thm)],[c_2070,c_2])).

tff(c_6187,plain,(
    ! [A_332,B_333] :
      ( r2_hidden('#skF_1'(A_332,B_333),'#skF_4')
      | ~ r1_tarski(A_332,'#skF_3')
      | r1_tarski(A_332,B_333) ) ),
    inference(resolution,[status(thm)],[c_1528,c_5921])).

tff(c_6408,plain,(
    ! [A_337] :
      ( ~ r1_tarski(A_337,'#skF_3')
      | r1_tarski(A_337,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6187,c_4])).

tff(c_6461,plain,
    ( r1_tarski(k1_ordinal1('#skF_3'),'#skF_4')
    | '#skF_1'(k1_ordinal1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2501,c_6408])).

tff(c_6852,plain,(
    '#skF_1'(k1_ordinal1('#skF_3'),'#skF_3') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6461])).

tff(c_1541,plain,(
    ! [A_153,B_16] :
      ( r1_tarski(A_153,k1_ordinal1(B_16))
      | ~ r2_hidden('#skF_1'(A_153,k1_ordinal1(B_16)),B_16) ) ),
    inference(resolution,[status(thm)],[c_30,c_1531])).

tff(c_1935,plain,(
    ! [A_153] :
      ( r1_tarski(A_153,k1_ordinal1('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_153,'#skF_3'),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1904,c_1541])).

tff(c_1969,plain,(
    ! [A_153] :
      ( r1_tarski(A_153,'#skF_3')
      | ~ r2_hidden('#skF_1'(A_153,'#skF_3'),'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1904,c_1935])).

tff(c_6864,plain,
    ( r1_tarski(k1_ordinal1('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6852,c_1969])).

tff(c_6895,plain,(
    r1_tarski(k1_ordinal1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_6864])).

tff(c_6233,plain,(
    ! [A_332] :
      ( ~ r1_tarski(A_332,'#skF_3')
      | r1_tarski(A_332,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6187,c_4])).

tff(c_6938,plain,(
    r1_tarski(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6895,c_6233])).

tff(c_7021,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6938,c_20])).

tff(c_7050,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2611,c_34,c_7021])).

tff(c_7052,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1480,c_7050])).

tff(c_7053,plain,(
    r1_tarski(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_6461])).

tff(c_7086,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_7053,c_20])).

tff(c_7115,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2611,c_34,c_7086])).

tff(c_7117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1480,c_7115])).

tff(c_7118,plain,(
    r2_hidden('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1902])).

tff(c_7131,plain,
    ( r1_tarski('#skF_3',k1_ordinal1('#skF_4'))
    | ~ v1_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_7118,c_14])).

tff(c_7233,plain,(
    ~ v1_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7131])).

tff(c_7236,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1490,c_7233])).

tff(c_7240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7236])).

tff(c_7241,plain,(
    r1_tarski('#skF_3',k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7131])).

tff(c_7252,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7241,c_20])).

tff(c_7257,plain,
    ( r1_ordinal1('#skF_3',k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7252])).

tff(c_7258,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7257])).

tff(c_7284,plain,(
    ~ v3_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_7258])).

tff(c_7288,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_7284])).

tff(c_7290,plain,(
    v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7257])).

tff(c_22,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ r1_ordinal1(A_12,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v3_ordinal1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_7939,plain,(
    ! [B_390,B_391] :
      ( '#skF_1'(k1_ordinal1(B_390),B_391) = B_390
      | r2_hidden('#skF_1'(k1_ordinal1(B_390),B_391),B_390)
      | r1_tarski(k1_ordinal1(B_390),B_391) ) ),
    inference(resolution,[status(thm)],[c_6,c_1543])).

tff(c_7964,plain,(
    ! [B_390] :
      ( '#skF_1'(k1_ordinal1(B_390),B_390) = B_390
      | r1_tarski(k1_ordinal1(B_390),B_390) ) ),
    inference(resolution,[status(thm)],[c_7939,c_4])).

tff(c_7502,plain,(
    ! [A_365,B_366,B_367] :
      ( r2_hidden('#skF_1'(A_365,B_366),B_367)
      | ~ r1_tarski(A_365,B_367)
      | r1_tarski(A_365,B_366) ) ),
    inference(resolution,[status(thm)],[c_6,c_1563])).

tff(c_10879,plain,(
    ! [A_513,B_514,B_515,B_516] :
      ( r2_hidden('#skF_1'(A_513,B_514),B_515)
      | ~ r1_tarski(B_516,B_515)
      | ~ r1_tarski(A_513,B_516)
      | r1_tarski(A_513,B_514) ) ),
    inference(resolution,[status(thm)],[c_7502,c_2])).

tff(c_10943,plain,(
    ! [A_517,B_518] :
      ( r2_hidden('#skF_1'(A_517,B_518),'#skF_4')
      | ~ r1_tarski(A_517,'#skF_3')
      | r1_tarski(A_517,B_518) ) ),
    inference(resolution,[status(thm)],[c_1528,c_10879])).

tff(c_11039,plain,(
    ! [A_520] :
      ( ~ r1_tarski(A_520,'#skF_3')
      | r1_tarski(A_520,k1_ordinal1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10943,c_1541])).

tff(c_11497,plain,(
    ! [B_522] :
      ( r2_hidden(B_522,k1_ordinal1('#skF_4'))
      | ~ r1_tarski(k1_ordinal1(B_522),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_11039,c_1578])).

tff(c_13889,plain,(
    ! [B_569,B_570] :
      ( r2_hidden(B_569,B_570)
      | ~ r1_tarski(k1_ordinal1('#skF_4'),B_570)
      | ~ r1_tarski(k1_ordinal1(B_569),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_11497,c_2])).

tff(c_13952,plain,(
    ! [B_569] :
      ( r2_hidden(B_569,'#skF_4')
      | ~ r1_tarski(k1_ordinal1(B_569),'#skF_3')
      | '#skF_1'(k1_ordinal1('#skF_4'),'#skF_4') = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_7964,c_13889])).

tff(c_25124,plain,(
    '#skF_1'(k1_ordinal1('#skF_4'),'#skF_4') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13952])).

tff(c_25183,plain,
    ( ~ r2_hidden('#skF_4','#skF_4')
    | r1_tarski(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25124,c_4])).

tff(c_25223,plain,(
    ~ r2_hidden('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_25183])).

tff(c_7242,plain,(
    v1_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_7131])).

tff(c_1716,plain,(
    ! [A_177,B_178] :
      ( r1_tarski('#skF_1'(A_177,B_178),A_177)
      | ~ v1_ordinal1(A_177)
      | r1_tarski(A_177,B_178) ) ),
    inference(resolution,[status(thm)],[c_6,c_1507])).

tff(c_1723,plain,(
    ! [A_177,B_178] :
      ( r1_ordinal1('#skF_1'(A_177,B_178),A_177)
      | ~ v3_ordinal1(A_177)
      | ~ v3_ordinal1('#skF_1'(A_177,B_178))
      | ~ v1_ordinal1(A_177)
      | r1_tarski(A_177,B_178) ) ),
    inference(resolution,[status(thm)],[c_1716,c_20])).

tff(c_25150,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_4'))
    | ~ v3_ordinal1('#skF_1'(k1_ordinal1('#skF_4'),'#skF_4'))
    | ~ v1_ordinal1(k1_ordinal1('#skF_4'))
    | r1_tarski(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25124,c_1723])).

tff(c_25207,plain,
    ( r1_ordinal1('#skF_4',k1_ordinal1('#skF_4'))
    | r1_tarski(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7242,c_34,c_25124,c_7290,c_25150])).

tff(c_25224,plain,(
    r1_tarski(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_25207])).

tff(c_25326,plain,(
    r2_hidden('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_25224,c_1578])).

tff(c_25389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25223,c_25326])).

tff(c_25391,plain,(
    ~ r1_tarski(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_25207])).

tff(c_13960,plain,(
    ! [B_571,A_572,B_573] :
      ( B_571 = '#skF_1'(A_572,B_573)
      | r2_hidden('#skF_1'(A_572,B_573),B_571)
      | ~ r1_tarski(A_572,k1_ordinal1(B_571))
      | r1_tarski(A_572,B_573) ) ),
    inference(resolution,[status(thm)],[c_7502,c_26])).

tff(c_55281,plain,(
    ! [A_1068,B_1069,B_1070,B_1071] :
      ( r2_hidden('#skF_1'(A_1068,B_1069),B_1070)
      | ~ r1_tarski(B_1071,B_1070)
      | B_1071 = '#skF_1'(A_1068,B_1069)
      | ~ r1_tarski(A_1068,k1_ordinal1(B_1071))
      | r1_tarski(A_1068,B_1069) ) ),
    inference(resolution,[status(thm)],[c_13960,c_2])).

tff(c_56090,plain,(
    ! [A_1075,B_1076] :
      ( r2_hidden('#skF_1'(A_1075,B_1076),'#skF_4')
      | '#skF_1'(A_1075,B_1076) = '#skF_3'
      | ~ r1_tarski(A_1075,k1_ordinal1('#skF_3'))
      | r1_tarski(A_1075,B_1076) ) ),
    inference(resolution,[status(thm)],[c_1528,c_55281])).

tff(c_56155,plain,
    ( r2_hidden('#skF_4','#skF_4')
    | '#skF_1'(k1_ordinal1('#skF_4'),'#skF_4') = '#skF_3'
    | ~ r1_tarski(k1_ordinal1('#skF_4'),k1_ordinal1('#skF_3'))
    | r1_tarski(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25124,c_56090])).

tff(c_56210,plain,
    ( r2_hidden('#skF_4','#skF_4')
    | '#skF_3' = '#skF_4'
    | ~ r1_tarski(k1_ordinal1('#skF_4'),k1_ordinal1('#skF_3'))
    | r1_tarski(k1_ordinal1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25124,c_56155])).

tff(c_56211,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski(k1_ordinal1('#skF_4'),k1_ordinal1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_25391,c_25223,c_56210])).

tff(c_56214,plain,(
    ~ r1_tarski(k1_ordinal1('#skF_4'),k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56211])).

tff(c_56235,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_4'),k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_22,c_56214])).

tff(c_56248,plain,
    ( ~ r1_ordinal1(k1_ordinal1('#skF_4'),k1_ordinal1('#skF_3'))
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7290,c_56235])).

tff(c_56309,plain,(
    ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56248])).

tff(c_56312,plain,(
    ~ v3_ordinal1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_56309])).

tff(c_56316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_56312])).

tff(c_56318,plain,(
    v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_56248])).

tff(c_1540,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_1531])).

tff(c_56773,plain,(
    ! [A_1088] :
      ( '#skF_1'(A_1088,'#skF_4') = '#skF_3'
      | ~ r1_tarski(A_1088,k1_ordinal1('#skF_3'))
      | r1_tarski(A_1088,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_56090,c_4])).

tff(c_56961,plain,
    ( '#skF_1'(k1_ordinal1('#skF_3'),'#skF_4') = '#skF_3'
    | r1_tarski(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1540,c_56773])).

tff(c_56962,plain,(
    r1_tarski(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56961])).

tff(c_57041,plain,
    ( r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4')
    | ~ v3_ordinal1('#skF_4')
    | ~ v3_ordinal1(k1_ordinal1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_56962,c_20])).

tff(c_57113,plain,(
    r1_ordinal1(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56318,c_34,c_57041])).

tff(c_57115,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1480,c_57113])).

tff(c_57117,plain,(
    ~ r1_tarski(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_56961])).

tff(c_57116,plain,(
    '#skF_1'(k1_ordinal1('#skF_3'),'#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_56961])).

tff(c_57315,plain,
    ( ~ r2_hidden('#skF_3','#skF_4')
    | r1_tarski(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_57116,c_4])).

tff(c_57384,plain,(
    r1_tarski(k1_ordinal1('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_57315])).

tff(c_57386,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57117,c_57384])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:26:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.36/13.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.36/13.41  
% 22.36/13.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.36/13.41  %$ r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 22.36/13.41  
% 22.36/13.41  %Foreground sorts:
% 22.36/13.41  
% 22.36/13.41  
% 22.36/13.41  %Background operators:
% 22.36/13.41  
% 22.36/13.41  
% 22.36/13.41  %Foreground operators:
% 22.36/13.41  tff('#skF_2', type, '#skF_2': $i > $i).
% 22.36/13.41  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 22.36/13.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 22.36/13.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 22.36/13.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 22.36/13.41  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 22.36/13.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 22.36/13.41  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 22.36/13.41  tff('#skF_3', type, '#skF_3': $i).
% 22.36/13.41  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 22.36/13.41  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 22.36/13.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 22.36/13.41  tff('#skF_4', type, '#skF_4': $i).
% 22.36/13.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 22.36/13.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 22.36/13.41  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 22.36/13.41  
% 22.36/13.43  tff(f_77, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_hidden(A, B) <=> r1_ordinal1(k1_ordinal1(A), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_ordinal1)).
% 22.36/13.43  tff(f_67, axiom, (![A]: (v3_ordinal1(A) => v3_ordinal1(k1_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_ordinal1)).
% 22.36/13.43  tff(f_55, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 22.36/13.43  tff(f_63, axiom, (![A, B]: (r2_hidden(A, k1_ordinal1(B)) <=> (r2_hidden(A, B) | (A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_ordinal1)).
% 22.36/13.43  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 22.36/13.43  tff(f_38, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 22.36/13.43  tff(f_47, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 22.36/13.43  tff(c_36, plain, (v3_ordinal1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.36/13.43  tff(c_32, plain, (![A_17]: (v3_ordinal1(k1_ordinal1(A_17)) | ~v3_ordinal1(A_17))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.36/13.43  tff(c_44, plain, (r2_hidden('#skF_3', '#skF_4') | r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.36/13.43  tff(c_65, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_44])).
% 22.36/13.43  tff(c_38, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.36/13.43  tff(c_90, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_65, c_38])).
% 22.36/13.43  tff(c_34, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 22.36/13.43  tff(c_193, plain, (![A_48, B_49]: (r1_tarski(A_48, B_49) | ~r1_ordinal1(A_48, B_49) | ~v3_ordinal1(B_49) | ~v3_ordinal1(A_48))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.36/13.43  tff(c_28, plain, (![B_16]: (r2_hidden(B_16, k1_ordinal1(B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.36/13.43  tff(c_122, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.36/13.43  tff(c_134, plain, (![B_16, B_39]: (r2_hidden(B_16, B_39) | ~r1_tarski(k1_ordinal1(B_16), B_39))), inference(resolution, [status(thm)], [c_28, c_122])).
% 22.36/13.43  tff(c_1397, plain, (![B_136, B_137]: (r2_hidden(B_136, B_137) | ~r1_ordinal1(k1_ordinal1(B_136), B_137) | ~v3_ordinal1(B_137) | ~v3_ordinal1(k1_ordinal1(B_136)))), inference(resolution, [status(thm)], [c_193, c_134])).
% 22.36/13.43  tff(c_1408, plain, (r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_65, c_1397])).
% 22.36/13.43  tff(c_1415, plain, (r2_hidden('#skF_3', '#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1408])).
% 22.36/13.43  tff(c_1416, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_90, c_1415])).
% 22.36/13.43  tff(c_1474, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_1416])).
% 22.36/13.43  tff(c_1478, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_1474])).
% 22.36/13.43  tff(c_1480, plain, (~r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 22.36/13.43  tff(c_1483, plain, (![A_140]: (v3_ordinal1(k1_ordinal1(A_140)) | ~v3_ordinal1(A_140))), inference(cnfTransformation, [status(thm)], [f_67])).
% 22.36/13.43  tff(c_10, plain, (![A_6]: (v1_ordinal1(A_6) | ~v3_ordinal1(A_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.36/13.43  tff(c_1490, plain, (![A_140]: (v1_ordinal1(k1_ordinal1(A_140)) | ~v3_ordinal1(A_140))), inference(resolution, [status(thm)], [c_1483, c_10])).
% 22.36/13.43  tff(c_1507, plain, (![B_150, A_151]: (r1_tarski(B_150, A_151) | ~r2_hidden(B_150, A_151) | ~v1_ordinal1(A_151))), inference(cnfTransformation, [status(thm)], [f_47])).
% 22.36/13.43  tff(c_1529, plain, (![B_16]: (r1_tarski(B_16, k1_ordinal1(B_16)) | ~v1_ordinal1(k1_ordinal1(B_16)))), inference(resolution, [status(thm)], [c_28, c_1507])).
% 22.36/13.43  tff(c_1563, plain, (![C_158, B_159, A_160]: (r2_hidden(C_158, B_159) | ~r2_hidden(C_158, A_160) | ~r1_tarski(A_160, B_159))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.36/13.43  tff(c_1615, plain, (![B_166, B_167]: (r2_hidden(B_166, B_167) | ~r1_tarski(k1_ordinal1(B_166), B_167))), inference(resolution, [status(thm)], [c_28, c_1563])).
% 22.36/13.43  tff(c_1661, plain, (![B_173]: (r2_hidden(B_173, k1_ordinal1(k1_ordinal1(B_173))) | ~v1_ordinal1(k1_ordinal1(k1_ordinal1(B_173))))), inference(resolution, [status(thm)], [c_1529, c_1615])).
% 22.36/13.43  tff(c_14, plain, (![B_11, A_8]: (r1_tarski(B_11, A_8) | ~r2_hidden(B_11, A_8) | ~v1_ordinal1(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 22.36/13.43  tff(c_1698, plain, (![B_176]: (r1_tarski(B_176, k1_ordinal1(k1_ordinal1(B_176))) | ~v1_ordinal1(k1_ordinal1(k1_ordinal1(B_176))))), inference(resolution, [status(thm)], [c_1661, c_14])).
% 22.36/13.43  tff(c_1479, plain, (r2_hidden('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_44])).
% 22.36/13.43  tff(c_1595, plain, (![B_164]: (r2_hidden('#skF_3', B_164) | ~r1_tarski('#skF_4', B_164))), inference(resolution, [status(thm)], [c_1479, c_1563])).
% 22.36/13.43  tff(c_26, plain, (![B_16, A_15]: (B_16=A_15 | r2_hidden(A_15, B_16) | ~r2_hidden(A_15, k1_ordinal1(B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.36/13.43  tff(c_1606, plain, (![B_16]: (B_16='#skF_3' | r2_hidden('#skF_3', B_16) | ~r1_tarski('#skF_4', k1_ordinal1(B_16)))), inference(resolution, [status(thm)], [c_1595, c_26])).
% 22.36/13.43  tff(c_1713, plain, (k1_ordinal1('#skF_4')='#skF_3' | r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | ~v1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_4')))), inference(resolution, [status(thm)], [c_1698, c_1606])).
% 22.36/13.43  tff(c_1890, plain, (~v1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_4')))), inference(splitLeft, [status(thm)], [c_1713])).
% 22.36/13.43  tff(c_1894, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_1490, c_1890])).
% 22.36/13.43  tff(c_1897, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_1894])).
% 22.36/13.43  tff(c_1901, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_1897])).
% 22.36/13.43  tff(c_1902, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4')) | k1_ordinal1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_1713])).
% 22.36/13.43  tff(c_1904, plain, (k1_ordinal1('#skF_4')='#skF_3'), inference(splitLeft, [status(thm)], [c_1902])).
% 22.36/13.43  tff(c_1903, plain, (v1_ordinal1(k1_ordinal1(k1_ordinal1('#skF_4')))), inference(splitRight, [status(thm)], [c_1713])).
% 22.36/13.43  tff(c_1905, plain, (v1_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1904, c_1903])).
% 22.36/13.43  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.36/13.43  tff(c_30, plain, (![A_15, B_16]: (~r2_hidden(A_15, B_16) | r2_hidden(A_15, k1_ordinal1(B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.36/13.43  tff(c_1531, plain, (![A_153, B_154]: (~r2_hidden('#skF_1'(A_153, B_154), B_154) | r1_tarski(A_153, B_154))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.36/13.43  tff(c_1724, plain, (![A_179, B_180]: (r1_tarski(A_179, k1_ordinal1(B_180)) | ~r2_hidden('#skF_1'(A_179, k1_ordinal1(B_180)), B_180))), inference(resolution, [status(thm)], [c_30, c_1531])).
% 22.36/13.43  tff(c_1748, plain, (![A_182]: (r1_tarski(A_182, k1_ordinal1(A_182)))), inference(resolution, [status(thm)], [c_6, c_1724])).
% 22.36/13.43  tff(c_1578, plain, (![B_16, B_159]: (r2_hidden(B_16, B_159) | ~r1_tarski(k1_ordinal1(B_16), B_159))), inference(resolution, [status(thm)], [c_28, c_1563])).
% 22.36/13.43  tff(c_1765, plain, (![B_16]: (r2_hidden(B_16, k1_ordinal1(k1_ordinal1(B_16))))), inference(resolution, [status(thm)], [c_1748, c_1578])).
% 22.36/13.43  tff(c_1929, plain, (r2_hidden('#skF_4', k1_ordinal1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1904, c_1765])).
% 22.36/13.43  tff(c_2100, plain, (r1_tarski('#skF_4', k1_ordinal1('#skF_3')) | ~v1_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_1929, c_14])).
% 22.36/13.43  tff(c_2106, plain, (r1_tarski('#skF_4', k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1905, c_2100])).
% 22.36/13.43  tff(c_20, plain, (![A_12, B_13]: (r1_ordinal1(A_12, B_13) | ~r1_tarski(A_12, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.36/13.43  tff(c_2114, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_2106, c_20])).
% 22.36/13.43  tff(c_2123, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2114])).
% 22.36/13.43  tff(c_2602, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_2123])).
% 22.36/13.43  tff(c_2605, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_2602])).
% 22.36/13.43  tff(c_2609, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2605])).
% 22.36/13.43  tff(c_2611, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_2123])).
% 22.36/13.43  tff(c_1543, plain, (![B_156, A_157]: (B_156=A_157 | r2_hidden(A_157, B_156) | ~r2_hidden(A_157, k1_ordinal1(B_156)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 22.36/13.43  tff(c_2470, plain, (![B_216, B_217]: ('#skF_1'(k1_ordinal1(B_216), B_217)=B_216 | r2_hidden('#skF_1'(k1_ordinal1(B_216), B_217), B_216) | r1_tarski(k1_ordinal1(B_216), B_217))), inference(resolution, [status(thm)], [c_6, c_1543])).
% 22.36/13.43  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.36/13.43  tff(c_2501, plain, (![B_216]: ('#skF_1'(k1_ordinal1(B_216), B_216)=B_216 | r1_tarski(k1_ordinal1(B_216), B_216))), inference(resolution, [status(thm)], [c_2470, c_4])).
% 22.36/13.43  tff(c_56, plain, (![A_21]: (v1_ordinal1(A_21) | ~v3_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_38])).
% 22.36/13.43  tff(c_63, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_56])).
% 22.36/13.43  tff(c_1519, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1479, c_1507])).
% 22.36/13.43  tff(c_1528, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_1519])).
% 22.36/13.43  tff(c_2070, plain, (![A_199, B_200, B_201]: (r2_hidden('#skF_1'(A_199, B_200), B_201) | ~r1_tarski(A_199, B_201) | r1_tarski(A_199, B_200))), inference(resolution, [status(thm)], [c_6, c_1563])).
% 22.36/13.43  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 22.36/13.43  tff(c_5921, plain, (![A_324, B_325, B_326, B_327]: (r2_hidden('#skF_1'(A_324, B_325), B_326) | ~r1_tarski(B_327, B_326) | ~r1_tarski(A_324, B_327) | r1_tarski(A_324, B_325))), inference(resolution, [status(thm)], [c_2070, c_2])).
% 22.36/13.43  tff(c_6187, plain, (![A_332, B_333]: (r2_hidden('#skF_1'(A_332, B_333), '#skF_4') | ~r1_tarski(A_332, '#skF_3') | r1_tarski(A_332, B_333))), inference(resolution, [status(thm)], [c_1528, c_5921])).
% 22.36/13.43  tff(c_6408, plain, (![A_337]: (~r1_tarski(A_337, '#skF_3') | r1_tarski(A_337, '#skF_4'))), inference(resolution, [status(thm)], [c_6187, c_4])).
% 22.36/13.43  tff(c_6461, plain, (r1_tarski(k1_ordinal1('#skF_3'), '#skF_4') | '#skF_1'(k1_ordinal1('#skF_3'), '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_2501, c_6408])).
% 22.36/13.43  tff(c_6852, plain, ('#skF_1'(k1_ordinal1('#skF_3'), '#skF_3')='#skF_3'), inference(splitLeft, [status(thm)], [c_6461])).
% 22.36/13.43  tff(c_1541, plain, (![A_153, B_16]: (r1_tarski(A_153, k1_ordinal1(B_16)) | ~r2_hidden('#skF_1'(A_153, k1_ordinal1(B_16)), B_16))), inference(resolution, [status(thm)], [c_30, c_1531])).
% 22.36/13.43  tff(c_1935, plain, (![A_153]: (r1_tarski(A_153, k1_ordinal1('#skF_4')) | ~r2_hidden('#skF_1'(A_153, '#skF_3'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1904, c_1541])).
% 22.36/13.43  tff(c_1969, plain, (![A_153]: (r1_tarski(A_153, '#skF_3') | ~r2_hidden('#skF_1'(A_153, '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1904, c_1935])).
% 22.36/13.43  tff(c_6864, plain, (r1_tarski(k1_ordinal1('#skF_3'), '#skF_3') | ~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6852, c_1969])).
% 22.36/13.43  tff(c_6895, plain, (r1_tarski(k1_ordinal1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_6864])).
% 22.36/13.43  tff(c_6233, plain, (![A_332]: (~r1_tarski(A_332, '#skF_3') | r1_tarski(A_332, '#skF_4'))), inference(resolution, [status(thm)], [c_6187, c_4])).
% 22.36/13.43  tff(c_6938, plain, (r1_tarski(k1_ordinal1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_6895, c_6233])).
% 22.36/13.43  tff(c_7021, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_6938, c_20])).
% 22.36/13.43  tff(c_7050, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2611, c_34, c_7021])).
% 22.36/13.43  tff(c_7052, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1480, c_7050])).
% 22.36/13.43  tff(c_7053, plain, (r1_tarski(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_6461])).
% 22.36/13.43  tff(c_7086, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_7053, c_20])).
% 22.36/13.43  tff(c_7115, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2611, c_34, c_7086])).
% 22.36/13.43  tff(c_7117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1480, c_7115])).
% 22.36/13.43  tff(c_7118, plain, (r2_hidden('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_1902])).
% 22.36/13.43  tff(c_7131, plain, (r1_tarski('#skF_3', k1_ordinal1('#skF_4')) | ~v1_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_7118, c_14])).
% 22.36/13.43  tff(c_7233, plain, (~v1_ordinal1(k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7131])).
% 22.36/13.43  tff(c_7236, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_1490, c_7233])).
% 22.36/13.43  tff(c_7240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_7236])).
% 22.36/13.43  tff(c_7241, plain, (r1_tarski('#skF_3', k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_7131])).
% 22.36/13.43  tff(c_7252, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_4')) | ~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_7241, c_20])).
% 22.36/13.43  tff(c_7257, plain, (r1_ordinal1('#skF_3', k1_ordinal1('#skF_4')) | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7252])).
% 22.36/13.43  tff(c_7258, plain, (~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7257])).
% 22.36/13.43  tff(c_7284, plain, (~v3_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_7258])).
% 22.36/13.43  tff(c_7288, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_7284])).
% 22.36/13.43  tff(c_7290, plain, (v3_ordinal1(k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_7257])).
% 22.36/13.43  tff(c_22, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~r1_ordinal1(A_12, B_13) | ~v3_ordinal1(B_13) | ~v3_ordinal1(A_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 22.36/13.43  tff(c_7939, plain, (![B_390, B_391]: ('#skF_1'(k1_ordinal1(B_390), B_391)=B_390 | r2_hidden('#skF_1'(k1_ordinal1(B_390), B_391), B_390) | r1_tarski(k1_ordinal1(B_390), B_391))), inference(resolution, [status(thm)], [c_6, c_1543])).
% 22.36/13.43  tff(c_7964, plain, (![B_390]: ('#skF_1'(k1_ordinal1(B_390), B_390)=B_390 | r1_tarski(k1_ordinal1(B_390), B_390))), inference(resolution, [status(thm)], [c_7939, c_4])).
% 22.36/13.43  tff(c_7502, plain, (![A_365, B_366, B_367]: (r2_hidden('#skF_1'(A_365, B_366), B_367) | ~r1_tarski(A_365, B_367) | r1_tarski(A_365, B_366))), inference(resolution, [status(thm)], [c_6, c_1563])).
% 22.36/13.43  tff(c_10879, plain, (![A_513, B_514, B_515, B_516]: (r2_hidden('#skF_1'(A_513, B_514), B_515) | ~r1_tarski(B_516, B_515) | ~r1_tarski(A_513, B_516) | r1_tarski(A_513, B_514))), inference(resolution, [status(thm)], [c_7502, c_2])).
% 22.36/13.43  tff(c_10943, plain, (![A_517, B_518]: (r2_hidden('#skF_1'(A_517, B_518), '#skF_4') | ~r1_tarski(A_517, '#skF_3') | r1_tarski(A_517, B_518))), inference(resolution, [status(thm)], [c_1528, c_10879])).
% 22.36/13.43  tff(c_11039, plain, (![A_520]: (~r1_tarski(A_520, '#skF_3') | r1_tarski(A_520, k1_ordinal1('#skF_4')))), inference(resolution, [status(thm)], [c_10943, c_1541])).
% 22.36/13.43  tff(c_11497, plain, (![B_522]: (r2_hidden(B_522, k1_ordinal1('#skF_4')) | ~r1_tarski(k1_ordinal1(B_522), '#skF_3'))), inference(resolution, [status(thm)], [c_11039, c_1578])).
% 22.36/13.43  tff(c_13889, plain, (![B_569, B_570]: (r2_hidden(B_569, B_570) | ~r1_tarski(k1_ordinal1('#skF_4'), B_570) | ~r1_tarski(k1_ordinal1(B_569), '#skF_3'))), inference(resolution, [status(thm)], [c_11497, c_2])).
% 22.36/13.43  tff(c_13952, plain, (![B_569]: (r2_hidden(B_569, '#skF_4') | ~r1_tarski(k1_ordinal1(B_569), '#skF_3') | '#skF_1'(k1_ordinal1('#skF_4'), '#skF_4')='#skF_4')), inference(resolution, [status(thm)], [c_7964, c_13889])).
% 22.36/13.43  tff(c_25124, plain, ('#skF_1'(k1_ordinal1('#skF_4'), '#skF_4')='#skF_4'), inference(splitLeft, [status(thm)], [c_13952])).
% 22.36/13.43  tff(c_25183, plain, (~r2_hidden('#skF_4', '#skF_4') | r1_tarski(k1_ordinal1('#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25124, c_4])).
% 22.36/13.43  tff(c_25223, plain, (~r2_hidden('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_25183])).
% 22.36/13.43  tff(c_7242, plain, (v1_ordinal1(k1_ordinal1('#skF_4'))), inference(splitRight, [status(thm)], [c_7131])).
% 22.36/13.43  tff(c_1716, plain, (![A_177, B_178]: (r1_tarski('#skF_1'(A_177, B_178), A_177) | ~v1_ordinal1(A_177) | r1_tarski(A_177, B_178))), inference(resolution, [status(thm)], [c_6, c_1507])).
% 22.36/13.43  tff(c_1723, plain, (![A_177, B_178]: (r1_ordinal1('#skF_1'(A_177, B_178), A_177) | ~v3_ordinal1(A_177) | ~v3_ordinal1('#skF_1'(A_177, B_178)) | ~v1_ordinal1(A_177) | r1_tarski(A_177, B_178))), inference(resolution, [status(thm)], [c_1716, c_20])).
% 22.36/13.43  tff(c_25150, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_4')) | ~v3_ordinal1(k1_ordinal1('#skF_4')) | ~v3_ordinal1('#skF_1'(k1_ordinal1('#skF_4'), '#skF_4')) | ~v1_ordinal1(k1_ordinal1('#skF_4')) | r1_tarski(k1_ordinal1('#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25124, c_1723])).
% 22.36/13.43  tff(c_25207, plain, (r1_ordinal1('#skF_4', k1_ordinal1('#skF_4')) | r1_tarski(k1_ordinal1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7242, c_34, c_25124, c_7290, c_25150])).
% 22.36/13.43  tff(c_25224, plain, (r1_tarski(k1_ordinal1('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_25207])).
% 22.36/13.43  tff(c_25326, plain, (r2_hidden('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_25224, c_1578])).
% 22.36/13.43  tff(c_25389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25223, c_25326])).
% 22.36/13.43  tff(c_25391, plain, (~r1_tarski(k1_ordinal1('#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_25207])).
% 22.36/13.43  tff(c_13960, plain, (![B_571, A_572, B_573]: (B_571='#skF_1'(A_572, B_573) | r2_hidden('#skF_1'(A_572, B_573), B_571) | ~r1_tarski(A_572, k1_ordinal1(B_571)) | r1_tarski(A_572, B_573))), inference(resolution, [status(thm)], [c_7502, c_26])).
% 22.36/13.43  tff(c_55281, plain, (![A_1068, B_1069, B_1070, B_1071]: (r2_hidden('#skF_1'(A_1068, B_1069), B_1070) | ~r1_tarski(B_1071, B_1070) | B_1071='#skF_1'(A_1068, B_1069) | ~r1_tarski(A_1068, k1_ordinal1(B_1071)) | r1_tarski(A_1068, B_1069))), inference(resolution, [status(thm)], [c_13960, c_2])).
% 22.36/13.43  tff(c_56090, plain, (![A_1075, B_1076]: (r2_hidden('#skF_1'(A_1075, B_1076), '#skF_4') | '#skF_1'(A_1075, B_1076)='#skF_3' | ~r1_tarski(A_1075, k1_ordinal1('#skF_3')) | r1_tarski(A_1075, B_1076))), inference(resolution, [status(thm)], [c_1528, c_55281])).
% 22.36/13.43  tff(c_56155, plain, (r2_hidden('#skF_4', '#skF_4') | '#skF_1'(k1_ordinal1('#skF_4'), '#skF_4')='#skF_3' | ~r1_tarski(k1_ordinal1('#skF_4'), k1_ordinal1('#skF_3')) | r1_tarski(k1_ordinal1('#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25124, c_56090])).
% 22.36/13.43  tff(c_56210, plain, (r2_hidden('#skF_4', '#skF_4') | '#skF_3'='#skF_4' | ~r1_tarski(k1_ordinal1('#skF_4'), k1_ordinal1('#skF_3')) | r1_tarski(k1_ordinal1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_25124, c_56155])).
% 22.36/13.43  tff(c_56211, plain, ('#skF_3'='#skF_4' | ~r1_tarski(k1_ordinal1('#skF_4'), k1_ordinal1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_25391, c_25223, c_56210])).
% 22.36/13.43  tff(c_56214, plain, (~r1_tarski(k1_ordinal1('#skF_4'), k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_56211])).
% 22.36/13.43  tff(c_56235, plain, (~r1_ordinal1(k1_ordinal1('#skF_4'), k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_4'))), inference(resolution, [status(thm)], [c_22, c_56214])).
% 22.36/13.43  tff(c_56248, plain, (~r1_ordinal1(k1_ordinal1('#skF_4'), k1_ordinal1('#skF_3')) | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7290, c_56235])).
% 22.36/13.43  tff(c_56309, plain, (~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitLeft, [status(thm)], [c_56248])).
% 22.36/13.43  tff(c_56312, plain, (~v3_ordinal1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_56309])).
% 22.36/13.43  tff(c_56316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_56312])).
% 22.36/13.43  tff(c_56318, plain, (v3_ordinal1(k1_ordinal1('#skF_3'))), inference(splitRight, [status(thm)], [c_56248])).
% 22.36/13.43  tff(c_1540, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_1531])).
% 22.36/13.43  tff(c_56773, plain, (![A_1088]: ('#skF_1'(A_1088, '#skF_4')='#skF_3' | ~r1_tarski(A_1088, k1_ordinal1('#skF_3')) | r1_tarski(A_1088, '#skF_4'))), inference(resolution, [status(thm)], [c_56090, c_4])).
% 22.36/13.43  tff(c_56961, plain, ('#skF_1'(k1_ordinal1('#skF_3'), '#skF_4')='#skF_3' | r1_tarski(k1_ordinal1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1540, c_56773])).
% 22.36/13.43  tff(c_56962, plain, (r1_tarski(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_56961])).
% 22.36/13.43  tff(c_57041, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4') | ~v3_ordinal1('#skF_4') | ~v3_ordinal1(k1_ordinal1('#skF_3'))), inference(resolution, [status(thm)], [c_56962, c_20])).
% 22.36/13.43  tff(c_57113, plain, (r1_ordinal1(k1_ordinal1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56318, c_34, c_57041])).
% 22.36/13.43  tff(c_57115, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1480, c_57113])).
% 22.36/13.43  tff(c_57117, plain, (~r1_tarski(k1_ordinal1('#skF_3'), '#skF_4')), inference(splitRight, [status(thm)], [c_56961])).
% 22.36/13.43  tff(c_57116, plain, ('#skF_1'(k1_ordinal1('#skF_3'), '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_56961])).
% 22.36/13.43  tff(c_57315, plain, (~r2_hidden('#skF_3', '#skF_4') | r1_tarski(k1_ordinal1('#skF_3'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_57116, c_4])).
% 22.36/13.43  tff(c_57384, plain, (r1_tarski(k1_ordinal1('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_57315])).
% 22.36/13.43  tff(c_57386, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57117, c_57384])).
% 22.36/13.43  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 22.36/13.43  
% 22.36/13.43  Inference rules
% 22.36/13.43  ----------------------
% 22.36/13.43  #Ref     : 0
% 22.36/13.43  #Sup     : 13018
% 22.36/13.43  #Fact    : 0
% 22.36/13.43  #Define  : 0
% 22.36/13.43  #Split   : 26
% 22.36/13.43  #Chain   : 0
% 22.36/13.43  #Close   : 0
% 22.36/13.43  
% 22.36/13.43  Ordering : KBO
% 22.36/13.43  
% 22.36/13.43  Simplification rules
% 22.36/13.43  ----------------------
% 22.36/13.43  #Subsume      : 2449
% 22.36/13.43  #Demod        : 4499
% 22.36/13.43  #Tautology    : 2521
% 22.36/13.43  #SimpNegUnit  : 71
% 22.36/13.43  #BackRed      : 1
% 22.36/13.43  
% 22.36/13.43  #Partial instantiations: 0
% 22.36/13.43  #Strategies tried      : 1
% 22.36/13.43  
% 22.36/13.43  Timing (in seconds)
% 22.36/13.43  ----------------------
% 22.36/13.44  Preprocessing        : 0.35
% 22.36/13.44  Parsing              : 0.19
% 22.36/13.44  CNF conversion       : 0.03
% 22.36/13.44  Main loop            : 12.22
% 22.36/13.44  Inferencing          : 1.65
% 22.36/13.44  Reduction            : 2.63
% 22.36/13.44  Demodulation         : 1.92
% 22.36/13.44  BG Simplification    : 0.20
% 22.36/13.44  Subsumption          : 7.01
% 22.36/13.44  Abstraction          : 0.29
% 22.36/13.44  MUC search           : 0.00
% 22.36/13.44  Cooper               : 0.00
% 22.36/13.44  Total                : 12.62
% 22.36/13.44  Index Insertion      : 0.00
% 22.36/13.44  Index Deletion       : 0.00
% 22.36/13.44  Index Matching       : 0.00
% 22.36/13.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
