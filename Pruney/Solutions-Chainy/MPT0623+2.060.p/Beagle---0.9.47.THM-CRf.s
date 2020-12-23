%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:14 EST 2020

% Result     : Theorem 5.50s
% Output     : CNFRefutation 5.50s
% Verified   : 
% Statistics : Number of formulae       :  150 (3270 expanded)
%              Number of leaves         :   25 (1083 expanded)
%              Depth                    :   20
%              Number of atoms          :  272 (8903 expanded)
%              Number of equality atoms :  112 (4781 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B] :
    ? [C] :
      ( v1_relat_1(C)
      & v1_funct_1(C)
      & k1_relat_1(C) = A
      & ! [D] :
          ( r2_hidden(D,A)
         => k1_funct_1(C,D) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ ( A = k1_xboole_0
              & B != k1_xboole_0 )
          & ! [C] :
              ( ( v1_relat_1(C)
                & v1_funct_1(C) )
             => ~ ( B = k1_relat_1(C)
                  & r1_tarski(k2_relat_1(C),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k1_relat_1(A) = k1_xboole_0
      <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_61,axiom,(
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

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5803,plain,(
    ! [A_5922,B_5923] :
      ( ~ r2_hidden('#skF_1'(A_5922,B_5923),B_5923)
      | r1_tarski(A_5922,B_5923) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5808,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_5803])).

tff(c_36,plain,(
    ! [A_48,B_49] : k1_relat_1('#skF_6'(A_48,B_49)) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [A_48,B_49] : v1_relat_1('#skF_6'(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_45,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_119,plain,(
    ! [A_71] :
      ( k2_relat_1(A_71) = k1_xboole_0
      | k1_relat_1(A_71) != k1_xboole_0
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_125,plain,(
    ! [A_48,B_49] :
      ( k2_relat_1('#skF_6'(A_48,B_49)) = k1_xboole_0
      | k1_relat_1('#skF_6'(A_48,B_49)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_119])).

tff(c_141,plain,(
    ! [B_49] : k2_relat_1('#skF_6'(k1_xboole_0,B_49)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_125])).

tff(c_57,plain,(
    ! [A_63] :
      ( k1_relat_1(A_63) != k1_xboole_0
      | k1_xboole_0 = A_63
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_60,plain,(
    ! [A_48,B_49] :
      ( k1_relat_1('#skF_6'(A_48,B_49)) != k1_xboole_0
      | '#skF_6'(A_48,B_49) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_63,plain,(
    ! [B_49] : '#skF_6'(k1_xboole_0,B_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60])).

tff(c_38,plain,(
    ! [A_48,B_49] : v1_funct_1('#skF_6'(A_48,B_49)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1618,plain,(
    ! [A_2284,B_2285] :
      ( r2_hidden('#skF_3'(A_2284,B_2285),k1_relat_1(A_2284))
      | r2_hidden('#skF_4'(A_2284,B_2285),B_2285)
      | k2_relat_1(A_2284) = B_2285
      | ~ v1_funct_1(A_2284)
      | ~ v1_relat_1(A_2284) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1648,plain,(
    ! [A_48,B_49,B_2285] :
      ( r2_hidden('#skF_3'('#skF_6'(A_48,B_49),B_2285),A_48)
      | r2_hidden('#skF_4'('#skF_6'(A_48,B_49),B_2285),B_2285)
      | k2_relat_1('#skF_6'(A_48,B_49)) = B_2285
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1618])).

tff(c_3854,plain,(
    ! [A_2453,B_2454,B_2455] :
      ( r2_hidden('#skF_3'('#skF_6'(A_2453,B_2454),B_2455),A_2453)
      | r2_hidden('#skF_4'('#skF_6'(A_2453,B_2454),B_2455),B_2455)
      | k2_relat_1('#skF_6'(A_2453,B_2454)) = B_2455 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1648])).

tff(c_64,plain,(
    ! [A_64,B_65] :
      ( k1_xboole_0 != A_64
      | '#skF_6'(A_64,B_65) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60])).

tff(c_72,plain,(
    ! [A_64] :
      ( v1_relat_1(k1_xboole_0)
      | k1_xboole_0 != A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_40])).

tff(c_80,plain,(
    ! [A_64] : k1_xboole_0 != A_64 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_86,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_80])).

tff(c_87,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_74,plain,(
    ! [A_64] :
      ( v1_funct_1(k1_xboole_0)
      | k1_xboole_0 != A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_38])).

tff(c_94,plain,(
    ! [A_64] : k1_xboole_0 != A_64 ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_100,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_94])).

tff(c_101,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_102,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_36])).

tff(c_122,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_119])).

tff(c_128,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_122])).

tff(c_1293,plain,(
    ! [A_2241,D_2242] :
      ( r2_hidden(k1_funct_1(A_2241,D_2242),k2_relat_1(A_2241))
      | ~ r2_hidden(D_2242,k1_relat_1(A_2241))
      | ~ v1_funct_1(A_2241)
      | ~ v1_relat_1(A_2241) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1306,plain,(
    ! [D_2242] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_2242),k1_xboole_0)
      | ~ r2_hidden(D_2242,k1_relat_1(k1_xboole_0))
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_1293])).

tff(c_1314,plain,(
    ! [D_2242] :
      ( r2_hidden(k1_funct_1(k1_xboole_0,D_2242),k1_xboole_0)
      | ~ r2_hidden(D_2242,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_101,c_102,c_1306])).

tff(c_34,plain,(
    ! [A_48,B_49,D_54] :
      ( k1_funct_1('#skF_6'(A_48,B_49),D_54) = B_49
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1300,plain,(
    ! [B_49,A_48,D_54] :
      ( r2_hidden(B_49,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ r2_hidden(D_54,k1_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1293])).

tff(c_1322,plain,(
    ! [B_2244,A_2245,D_2246] :
      ( r2_hidden(B_2244,k2_relat_1('#skF_6'(A_2245,B_2244)))
      | ~ r2_hidden(D_2246,A_2245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_1300])).

tff(c_1324,plain,(
    ! [B_2244,D_2242] :
      ( r2_hidden(B_2244,k2_relat_1('#skF_6'(k1_xboole_0,B_2244)))
      | ~ r2_hidden(D_2242,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1314,c_1322])).

tff(c_1332,plain,(
    ! [B_2244,D_2242] :
      ( r2_hidden(B_2244,k1_xboole_0)
      | ~ r2_hidden(D_2242,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_1324])).

tff(c_1336,plain,(
    ! [D_2242] : ~ r2_hidden(D_2242,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1332])).

tff(c_3904,plain,(
    ! [B_2454,B_2455] :
      ( r2_hidden('#skF_4'('#skF_6'(k1_xboole_0,B_2454),B_2455),B_2455)
      | k2_relat_1('#skF_6'(k1_xboole_0,B_2454)) = B_2455 ) ),
    inference(resolution,[status(thm)],[c_3854,c_1336])).

tff(c_3981,plain,(
    ! [B_2455] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_2455),B_2455)
      | k1_xboole_0 = B_2455 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_63,c_3904])).

tff(c_1454,plain,(
    ! [A_2261,C_2262] :
      ( r2_hidden('#skF_5'(A_2261,k2_relat_1(A_2261),C_2262),k1_relat_1(A_2261))
      | ~ r2_hidden(C_2262,k2_relat_1(A_2261))
      | ~ v1_funct_1(A_2261)
      | ~ v1_relat_1(A_2261) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1469,plain,(
    ! [A_48,B_49,C_2262] :
      ( r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_2262),A_48)
      | ~ r2_hidden(C_2262,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1454])).

tff(c_1479,plain,(
    ! [A_48,B_49,C_2262] :
      ( r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_2262),A_48)
      | ~ r2_hidden(C_2262,k2_relat_1('#skF_6'(A_48,B_49))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1469])).

tff(c_1351,plain,(
    ! [A_2249,C_2250] :
      ( k1_funct_1(A_2249,'#skF_5'(A_2249,k2_relat_1(A_2249),C_2250)) = C_2250
      | ~ r2_hidden(C_2250,k2_relat_1(A_2249))
      | ~ v1_funct_1(A_2249)
      | ~ v1_relat_1(A_2249) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1368,plain,(
    ! [C_2250,B_49,A_48] :
      ( C_2250 = B_49
      | ~ r2_hidden(C_2250,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_48,B_49),k2_relat_1('#skF_6'(A_48,B_49)),C_2250),A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_1351])).

tff(c_3422,plain,(
    ! [C_2427,B_2428,A_2429] :
      ( C_2427 = B_2428
      | ~ r2_hidden(C_2427,k2_relat_1('#skF_6'(A_2429,B_2428)))
      | ~ r2_hidden('#skF_5'('#skF_6'(A_2429,B_2428),k2_relat_1('#skF_6'(A_2429,B_2428)),C_2427),A_2429) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_1368])).

tff(c_3437,plain,(
    ! [C_2430,B_2431,A_2432] :
      ( C_2430 = B_2431
      | ~ r2_hidden(C_2430,k2_relat_1('#skF_6'(A_2432,B_2431))) ) ),
    inference(resolution,[status(thm)],[c_1479,c_3422])).

tff(c_3633,plain,(
    ! [A_2443,B_2444,B_2445] :
      ( '#skF_1'(k2_relat_1('#skF_6'(A_2443,B_2444)),B_2445) = B_2444
      | r1_tarski(k2_relat_1('#skF_6'(A_2443,B_2444)),B_2445) ) ),
    inference(resolution,[status(thm)],[c_6,c_3437])).

tff(c_42,plain,(
    ! [C_56] :
      ( ~ r1_tarski(k2_relat_1(C_56),'#skF_7')
      | k1_relat_1(C_56) != '#skF_8'
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_3689,plain,(
    ! [A_2443,B_2444] :
      ( k1_relat_1('#skF_6'(A_2443,B_2444)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_2443,B_2444))
      | ~ v1_relat_1('#skF_6'(A_2443,B_2444))
      | '#skF_1'(k2_relat_1('#skF_6'(A_2443,B_2444)),'#skF_7') = B_2444 ) ),
    inference(resolution,[status(thm)],[c_3633,c_42])).

tff(c_3722,plain,(
    ! [A_2446,B_2447] :
      ( A_2446 != '#skF_8'
      | '#skF_1'(k2_relat_1('#skF_6'(A_2446,B_2447)),'#skF_7') = B_2447 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_3689])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4179,plain,(
    ! [B_2461,A_2462] :
      ( ~ r2_hidden(B_2461,'#skF_7')
      | r1_tarski(k2_relat_1('#skF_6'(A_2462,B_2461)),'#skF_7')
      | A_2462 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3722,c_4])).

tff(c_4199,plain,(
    ! [A_2462,B_2461] :
      ( k1_relat_1('#skF_6'(A_2462,B_2461)) != '#skF_8'
      | ~ v1_funct_1('#skF_6'(A_2462,B_2461))
      | ~ v1_relat_1('#skF_6'(A_2462,B_2461))
      | ~ r2_hidden(B_2461,'#skF_7')
      | A_2462 != '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_4179,c_42])).

tff(c_4215,plain,(
    ! [B_2461,A_2462] :
      ( ~ r2_hidden(B_2461,'#skF_7')
      | A_2462 != '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_4199])).

tff(c_4218,plain,(
    ! [A_2462] : A_2462 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4215])).

tff(c_4222,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_4218])).

tff(c_4224,plain,(
    ! [B_2463] : ~ r2_hidden(B_2463,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4215])).

tff(c_4228,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_3981,c_4224])).

tff(c_4260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45,c_4228])).

tff(c_4264,plain,(
    ! [B_2464] : r2_hidden(B_2464,k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1332])).

tff(c_62,plain,(
    ! [A_48,B_49] :
      ( k1_xboole_0 != A_48
      | '#skF_6'(A_48,B_49) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_60])).

tff(c_1254,plain,(
    ! [A_2230,B_2231,D_2232] :
      ( k1_funct_1('#skF_6'(A_2230,B_2231),D_2232) = B_2231
      | ~ r2_hidden(D_2232,A_2230) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1263,plain,(
    ! [D_2232,B_49,A_48] :
      ( k1_funct_1(k1_xboole_0,D_2232) = B_49
      | ~ r2_hidden(D_2232,A_48)
      | k1_xboole_0 != A_48 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_1254])).

tff(c_4358,plain,(
    ! [B_2468] : k1_funct_1(k1_xboole_0,B_2468) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_4264,c_1263])).

tff(c_4277,plain,(
    ! [B_2464,B_49] : k1_funct_1(k1_xboole_0,B_2464) = B_49 ),
    inference(resolution,[status(thm)],[c_4264,c_1263])).

tff(c_4753,plain,(
    ! [B_3474] : B_3474 = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_4358,c_4277])).

tff(c_134,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_7')
    | k1_relat_1(k1_xboole_0) != '#skF_8'
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_42])).

tff(c_138,plain,
    ( ~ r1_tarski(k1_xboole_0,'#skF_7')
    | k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_101,c_102,c_134])).

tff(c_140,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_4813,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4753,c_140])).

tff(c_4815,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_4824,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_45])).

tff(c_130,plain,(
    ! [A_48,B_49] :
      ( k2_relat_1('#skF_6'(A_48,B_49)) = k1_xboole_0
      | k1_xboole_0 != A_48 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_125])).

tff(c_4886,plain,(
    ! [B_49] : k2_relat_1('#skF_6'('#skF_8',B_49)) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_4815,c_130])).

tff(c_4821,plain,(
    v1_relat_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_87])).

tff(c_4820,plain,(
    v1_funct_1('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_101])).

tff(c_70,plain,(
    ! [A_64] :
      ( k1_relat_1(k1_xboole_0) = A_64
      | k1_xboole_0 != A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_36])).

tff(c_4846,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_4815,c_70])).

tff(c_4816,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_4815,c_128])).

tff(c_4979,plain,(
    ! [A_3973,D_3974] :
      ( r2_hidden(k1_funct_1(A_3973,D_3974),k2_relat_1(A_3973))
      | ~ r2_hidden(D_3974,k1_relat_1(A_3973))
      | ~ v1_funct_1(A_3973)
      | ~ v1_relat_1(A_3973) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_4990,plain,(
    ! [D_3974] :
      ( r2_hidden(k1_funct_1('#skF_8',D_3974),'#skF_8')
      | ~ r2_hidden(D_3974,k1_relat_1('#skF_8'))
      | ~ v1_funct_1('#skF_8')
      | ~ v1_relat_1('#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4816,c_4979])).

tff(c_4997,plain,(
    ! [D_3974] :
      ( r2_hidden(k1_funct_1('#skF_8',D_3974),'#skF_8')
      | ~ r2_hidden(D_3974,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4821,c_4820,c_4846,c_4990])).

tff(c_4984,plain,(
    ! [B_49,A_48,D_54] :
      ( r2_hidden(B_49,k2_relat_1('#skF_6'(A_48,B_49)))
      | ~ r2_hidden(D_54,k1_relat_1('#skF_6'(A_48,B_49)))
      | ~ v1_funct_1('#skF_6'(A_48,B_49))
      | ~ v1_relat_1('#skF_6'(A_48,B_49))
      | ~ r2_hidden(D_54,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_4979])).

tff(c_5002,plain,(
    ! [B_3976,A_3977,D_3978] :
      ( r2_hidden(B_3976,k2_relat_1('#skF_6'(A_3977,B_3976)))
      | ~ r2_hidden(D_3978,A_3977) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_36,c_4984])).

tff(c_5004,plain,(
    ! [B_3976,D_3974] :
      ( r2_hidden(B_3976,k2_relat_1('#skF_6'('#skF_8',B_3976)))
      | ~ r2_hidden(D_3974,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_4997,c_5002])).

tff(c_5010,plain,(
    ! [B_3976,D_3974] :
      ( r2_hidden(B_3976,'#skF_8')
      | ~ r2_hidden(D_3974,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4886,c_5004])).

tff(c_5015,plain,(
    ! [D_3979] : ~ r2_hidden(D_3979,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5010])).

tff(c_5020,plain,(
    ! [B_2] : r1_tarski('#skF_8',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_5015])).

tff(c_4814,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_4829,plain,(
    ~ r1_tarski('#skF_8','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_4814])).

tff(c_5023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5020,c_4829])).

tff(c_5024,plain,(
    ! [B_3976] : r2_hidden(B_3976,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_5010])).

tff(c_4822,plain,(
    ! [A_48,B_49] :
      ( A_48 != '#skF_8'
      | '#skF_6'(A_48,B_49) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4815,c_4815,c_62])).

tff(c_4952,plain,(
    ! [A_3965,B_3966,D_3967] :
      ( k1_funct_1('#skF_6'(A_3965,B_3966),D_3967) = B_3966
      | ~ r2_hidden(D_3967,A_3965) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5149,plain,(
    ! [D_3993,B_3994,A_3995] :
      ( k1_funct_1('#skF_8',D_3993) = B_3994
      | ~ r2_hidden(D_3993,A_3995)
      | A_3995 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4822,c_4952])).

tff(c_5199,plain,(
    ! [B_3996] : k1_funct_1('#skF_8',B_3996) = '#skF_7' ),
    inference(resolution,[status(thm)],[c_5024,c_5149])).

tff(c_5165,plain,(
    ! [B_3976,B_3994] : k1_funct_1('#skF_8',B_3976) = B_3994 ),
    inference(resolution,[status(thm)],[c_5024,c_5149])).

tff(c_5604,plain,(
    ! [B_5242] : B_5242 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_5199,c_5165])).

tff(c_5655,plain,(
    '#skF_7' = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_5604,c_4816])).

tff(c_5677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4824,c_5655])).

tff(c_5678,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_relat_1(A_6) != k1_xboole_0
      | k1_xboole_0 = A_6
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_5709,plain,(
    ! [A_5914] :
      ( k1_relat_1(A_5914) != '#skF_8'
      | A_5914 = '#skF_8'
      | ~ v1_relat_1(A_5914) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_5678,c_10])).

tff(c_5712,plain,(
    ! [A_48,B_49] :
      ( k1_relat_1('#skF_6'(A_48,B_49)) != '#skF_8'
      | '#skF_6'(A_48,B_49) = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_40,c_5709])).

tff(c_5723,plain,(
    ! [A_5916,B_5917] :
      ( A_5916 != '#skF_8'
      | '#skF_6'(A_5916,B_5917) = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_5712])).

tff(c_5731,plain,(
    ! [A_5916] :
      ( v1_relat_1('#skF_8')
      | A_5916 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5723,c_40])).

tff(c_5739,plain,(
    ! [A_5916] : A_5916 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5731])).

tff(c_5679,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5684,plain,(
    '#skF_7' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_5679])).

tff(c_5746,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5739,c_5684])).

tff(c_5747,plain,(
    v1_relat_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_5731])).

tff(c_5733,plain,(
    ! [A_5916] :
      ( v1_funct_1('#skF_8')
      | A_5916 != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5723,c_38])).

tff(c_5773,plain,(
    ! [A_5916] : A_5916 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5733])).

tff(c_5781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5773,c_5684])).

tff(c_5782,plain,(
    v1_funct_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_5733])).

tff(c_5783,plain,(
    k1_relat_1('#skF_8') = '#skF_8' ),
    inference(superposition,[status(thm),theory(equality)],[c_5723,c_36])).

tff(c_14,plain,(
    ! [A_7] :
      ( k2_relat_1(A_7) = k1_xboole_0
      | k1_relat_1(A_7) != k1_xboole_0
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_5748,plain,(
    ! [A_7] :
      ( k2_relat_1(A_7) = '#skF_8'
      | k1_relat_1(A_7) != '#skF_8'
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5678,c_5678,c_14])).

tff(c_5767,plain,
    ( k2_relat_1('#skF_8') = '#skF_8'
    | k1_relat_1('#skF_8') != '#skF_8' ),
    inference(resolution,[status(thm)],[c_5747,c_5748])).

tff(c_5791,plain,(
    k2_relat_1('#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5783,c_5767])).

tff(c_5689,plain,(
    ! [C_56] :
      ( ~ r1_tarski(k2_relat_1(C_56),'#skF_8')
      | k1_relat_1(C_56) != '#skF_8'
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5684,c_42])).

tff(c_5795,plain,
    ( ~ r1_tarski('#skF_8','#skF_8')
    | k1_relat_1('#skF_8') != '#skF_8'
    | ~ v1_funct_1('#skF_8')
    | ~ v1_relat_1('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5791,c_5689])).

tff(c_5799,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5747,c_5782,c_5783,c_5795])).

tff(c_5811,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5808,c_5799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.50/2.06  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.07  
% 5.50/2.07  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.08  %$ r2_hidden > r1_tarski > v1_relat_1 > v1_funct_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_8 > #skF_2 > #skF_1 > #skF_4
% 5.50/2.08  
% 5.50/2.08  %Foreground sorts:
% 5.50/2.08  
% 5.50/2.08  
% 5.50/2.08  %Background operators:
% 5.50/2.08  
% 5.50/2.08  
% 5.50/2.08  %Foreground operators:
% 5.50/2.08  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 5.50/2.08  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.50/2.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.50/2.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.50/2.08  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.50/2.08  tff('#skF_7', type, '#skF_7': $i).
% 5.50/2.08  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.50/2.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.50/2.08  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.50/2.08  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 5.50/2.08  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 5.50/2.08  tff('#skF_8', type, '#skF_8': $i).
% 5.50/2.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.50/2.08  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.50/2.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.50/2.08  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.50/2.08  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.50/2.08  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.50/2.08  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.50/2.08  
% 5.50/2.10  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 5.50/2.10  tff(f_73, axiom, (![A, B]: (?[C]: (((v1_relat_1(C) & v1_funct_1(C)) & (k1_relat_1(C) = A)) & (![D]: (r2_hidden(D, A) => (k1_funct_1(C, D) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 5.50/2.10  tff(f_91, negated_conjecture, ~(![A, B]: ~(~((A = k1_xboole_0) & ~(B = k1_xboole_0)) & (![C]: ((v1_relat_1(C) & v1_funct_1(C)) => ~((B = k1_relat_1(C)) & r1_tarski(k2_relat_1(C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 5.50/2.10  tff(f_46, axiom, (![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 5.50/2.10  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 5.50/2.10  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(D, k1_relat_1(A)) & (C = k1_funct_1(A, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 5.50/2.10  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.50/2.10  tff(c_5803, plain, (![A_5922, B_5923]: (~r2_hidden('#skF_1'(A_5922, B_5923), B_5923) | r1_tarski(A_5922, B_5923))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.50/2.10  tff(c_5808, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_5803])).
% 5.50/2.10  tff(c_36, plain, (![A_48, B_49]: (k1_relat_1('#skF_6'(A_48, B_49))=A_48)), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_40, plain, (![A_48, B_49]: (v1_relat_1('#skF_6'(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_44, plain, (k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.50/2.10  tff(c_45, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_44])).
% 5.50/2.10  tff(c_119, plain, (![A_71]: (k2_relat_1(A_71)=k1_xboole_0 | k1_relat_1(A_71)!=k1_xboole_0 | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.50/2.10  tff(c_125, plain, (![A_48, B_49]: (k2_relat_1('#skF_6'(A_48, B_49))=k1_xboole_0 | k1_relat_1('#skF_6'(A_48, B_49))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_119])).
% 5.50/2.10  tff(c_141, plain, (![B_49]: (k2_relat_1('#skF_6'(k1_xboole_0, B_49))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_125])).
% 5.50/2.10  tff(c_57, plain, (![A_63]: (k1_relat_1(A_63)!=k1_xboole_0 | k1_xboole_0=A_63 | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.50/2.10  tff(c_60, plain, (![A_48, B_49]: (k1_relat_1('#skF_6'(A_48, B_49))!=k1_xboole_0 | '#skF_6'(A_48, B_49)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_57])).
% 5.50/2.10  tff(c_63, plain, (![B_49]: ('#skF_6'(k1_xboole_0, B_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60])).
% 5.50/2.10  tff(c_38, plain, (![A_48, B_49]: (v1_funct_1('#skF_6'(A_48, B_49)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_1618, plain, (![A_2284, B_2285]: (r2_hidden('#skF_3'(A_2284, B_2285), k1_relat_1(A_2284)) | r2_hidden('#skF_4'(A_2284, B_2285), B_2285) | k2_relat_1(A_2284)=B_2285 | ~v1_funct_1(A_2284) | ~v1_relat_1(A_2284))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.50/2.10  tff(c_1648, plain, (![A_48, B_49, B_2285]: (r2_hidden('#skF_3'('#skF_6'(A_48, B_49), B_2285), A_48) | r2_hidden('#skF_4'('#skF_6'(A_48, B_49), B_2285), B_2285) | k2_relat_1('#skF_6'(A_48, B_49))=B_2285 | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1618])).
% 5.50/2.10  tff(c_3854, plain, (![A_2453, B_2454, B_2455]: (r2_hidden('#skF_3'('#skF_6'(A_2453, B_2454), B_2455), A_2453) | r2_hidden('#skF_4'('#skF_6'(A_2453, B_2454), B_2455), B_2455) | k2_relat_1('#skF_6'(A_2453, B_2454))=B_2455)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1648])).
% 5.50/2.10  tff(c_64, plain, (![A_64, B_65]: (k1_xboole_0!=A_64 | '#skF_6'(A_64, B_65)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60])).
% 5.50/2.10  tff(c_72, plain, (![A_64]: (v1_relat_1(k1_xboole_0) | k1_xboole_0!=A_64)), inference(superposition, [status(thm), theory('equality')], [c_64, c_40])).
% 5.50/2.10  tff(c_80, plain, (![A_64]: (k1_xboole_0!=A_64)), inference(splitLeft, [status(thm)], [c_72])).
% 5.50/2.10  tff(c_86, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_80])).
% 5.50/2.10  tff(c_87, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_72])).
% 5.50/2.10  tff(c_74, plain, (![A_64]: (v1_funct_1(k1_xboole_0) | k1_xboole_0!=A_64)), inference(superposition, [status(thm), theory('equality')], [c_64, c_38])).
% 5.50/2.10  tff(c_94, plain, (![A_64]: (k1_xboole_0!=A_64)), inference(splitLeft, [status(thm)], [c_74])).
% 5.50/2.10  tff(c_100, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_94])).
% 5.50/2.10  tff(c_101, plain, (v1_funct_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_74])).
% 5.50/2.10  tff(c_102, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_64, c_36])).
% 5.50/2.10  tff(c_122, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_119])).
% 5.50/2.10  tff(c_128, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_102, c_122])).
% 5.50/2.10  tff(c_1293, plain, (![A_2241, D_2242]: (r2_hidden(k1_funct_1(A_2241, D_2242), k2_relat_1(A_2241)) | ~r2_hidden(D_2242, k1_relat_1(A_2241)) | ~v1_funct_1(A_2241) | ~v1_relat_1(A_2241))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.50/2.10  tff(c_1306, plain, (![D_2242]: (r2_hidden(k1_funct_1(k1_xboole_0, D_2242), k1_xboole_0) | ~r2_hidden(D_2242, k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_128, c_1293])).
% 5.50/2.10  tff(c_1314, plain, (![D_2242]: (r2_hidden(k1_funct_1(k1_xboole_0, D_2242), k1_xboole_0) | ~r2_hidden(D_2242, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_87, c_101, c_102, c_1306])).
% 5.50/2.10  tff(c_34, plain, (![A_48, B_49, D_54]: (k1_funct_1('#skF_6'(A_48, B_49), D_54)=B_49 | ~r2_hidden(D_54, A_48))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_1300, plain, (![B_49, A_48, D_54]: (r2_hidden(B_49, k2_relat_1('#skF_6'(A_48, B_49))) | ~r2_hidden(D_54, k1_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden(D_54, A_48))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1293])).
% 5.50/2.10  tff(c_1322, plain, (![B_2244, A_2245, D_2246]: (r2_hidden(B_2244, k2_relat_1('#skF_6'(A_2245, B_2244))) | ~r2_hidden(D_2246, A_2245))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_1300])).
% 5.50/2.10  tff(c_1324, plain, (![B_2244, D_2242]: (r2_hidden(B_2244, k2_relat_1('#skF_6'(k1_xboole_0, B_2244))) | ~r2_hidden(D_2242, k1_xboole_0))), inference(resolution, [status(thm)], [c_1314, c_1322])).
% 5.50/2.10  tff(c_1332, plain, (![B_2244, D_2242]: (r2_hidden(B_2244, k1_xboole_0) | ~r2_hidden(D_2242, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_1324])).
% 5.50/2.10  tff(c_1336, plain, (![D_2242]: (~r2_hidden(D_2242, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_1332])).
% 5.50/2.10  tff(c_3904, plain, (![B_2454, B_2455]: (r2_hidden('#skF_4'('#skF_6'(k1_xboole_0, B_2454), B_2455), B_2455) | k2_relat_1('#skF_6'(k1_xboole_0, B_2454))=B_2455)), inference(resolution, [status(thm)], [c_3854, c_1336])).
% 5.50/2.10  tff(c_3981, plain, (![B_2455]: (r2_hidden('#skF_4'(k1_xboole_0, B_2455), B_2455) | k1_xboole_0=B_2455)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_63, c_3904])).
% 5.50/2.10  tff(c_1454, plain, (![A_2261, C_2262]: (r2_hidden('#skF_5'(A_2261, k2_relat_1(A_2261), C_2262), k1_relat_1(A_2261)) | ~r2_hidden(C_2262, k2_relat_1(A_2261)) | ~v1_funct_1(A_2261) | ~v1_relat_1(A_2261))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.50/2.10  tff(c_1469, plain, (![A_48, B_49, C_2262]: (r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_2262), A_48) | ~r2_hidden(C_2262, k2_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1454])).
% 5.50/2.10  tff(c_1479, plain, (![A_48, B_49, C_2262]: (r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_2262), A_48) | ~r2_hidden(C_2262, k2_relat_1('#skF_6'(A_48, B_49))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1469])).
% 5.50/2.10  tff(c_1351, plain, (![A_2249, C_2250]: (k1_funct_1(A_2249, '#skF_5'(A_2249, k2_relat_1(A_2249), C_2250))=C_2250 | ~r2_hidden(C_2250, k2_relat_1(A_2249)) | ~v1_funct_1(A_2249) | ~v1_relat_1(A_2249))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.50/2.10  tff(c_1368, plain, (![C_2250, B_49, A_48]: (C_2250=B_49 | ~r2_hidden(C_2250, k2_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden('#skF_5'('#skF_6'(A_48, B_49), k2_relat_1('#skF_6'(A_48, B_49)), C_2250), A_48))), inference(superposition, [status(thm), theory('equality')], [c_34, c_1351])).
% 5.50/2.10  tff(c_3422, plain, (![C_2427, B_2428, A_2429]: (C_2427=B_2428 | ~r2_hidden(C_2427, k2_relat_1('#skF_6'(A_2429, B_2428))) | ~r2_hidden('#skF_5'('#skF_6'(A_2429, B_2428), k2_relat_1('#skF_6'(A_2429, B_2428)), C_2427), A_2429))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_1368])).
% 5.50/2.10  tff(c_3437, plain, (![C_2430, B_2431, A_2432]: (C_2430=B_2431 | ~r2_hidden(C_2430, k2_relat_1('#skF_6'(A_2432, B_2431))))), inference(resolution, [status(thm)], [c_1479, c_3422])).
% 5.50/2.10  tff(c_3633, plain, (![A_2443, B_2444, B_2445]: ('#skF_1'(k2_relat_1('#skF_6'(A_2443, B_2444)), B_2445)=B_2444 | r1_tarski(k2_relat_1('#skF_6'(A_2443, B_2444)), B_2445))), inference(resolution, [status(thm)], [c_6, c_3437])).
% 5.50/2.10  tff(c_42, plain, (![C_56]: (~r1_tarski(k2_relat_1(C_56), '#skF_7') | k1_relat_1(C_56)!='#skF_8' | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.50/2.10  tff(c_3689, plain, (![A_2443, B_2444]: (k1_relat_1('#skF_6'(A_2443, B_2444))!='#skF_8' | ~v1_funct_1('#skF_6'(A_2443, B_2444)) | ~v1_relat_1('#skF_6'(A_2443, B_2444)) | '#skF_1'(k2_relat_1('#skF_6'(A_2443, B_2444)), '#skF_7')=B_2444)), inference(resolution, [status(thm)], [c_3633, c_42])).
% 5.50/2.10  tff(c_3722, plain, (![A_2446, B_2447]: (A_2446!='#skF_8' | '#skF_1'(k2_relat_1('#skF_6'(A_2446, B_2447)), '#skF_7')=B_2447)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_3689])).
% 5.50/2.10  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.50/2.10  tff(c_4179, plain, (![B_2461, A_2462]: (~r2_hidden(B_2461, '#skF_7') | r1_tarski(k2_relat_1('#skF_6'(A_2462, B_2461)), '#skF_7') | A_2462!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3722, c_4])).
% 5.50/2.10  tff(c_4199, plain, (![A_2462, B_2461]: (k1_relat_1('#skF_6'(A_2462, B_2461))!='#skF_8' | ~v1_funct_1('#skF_6'(A_2462, B_2461)) | ~v1_relat_1('#skF_6'(A_2462, B_2461)) | ~r2_hidden(B_2461, '#skF_7') | A_2462!='#skF_8')), inference(resolution, [status(thm)], [c_4179, c_42])).
% 5.50/2.10  tff(c_4215, plain, (![B_2461, A_2462]: (~r2_hidden(B_2461, '#skF_7') | A_2462!='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_4199])).
% 5.50/2.10  tff(c_4218, plain, (![A_2462]: (A_2462!='#skF_8')), inference(splitLeft, [status(thm)], [c_4215])).
% 5.50/2.10  tff(c_4222, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_4218])).
% 5.50/2.10  tff(c_4224, plain, (![B_2463]: (~r2_hidden(B_2463, '#skF_7'))), inference(splitRight, [status(thm)], [c_4215])).
% 5.50/2.10  tff(c_4228, plain, (k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_3981, c_4224])).
% 5.50/2.10  tff(c_4260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45, c_4228])).
% 5.50/2.10  tff(c_4264, plain, (![B_2464]: (r2_hidden(B_2464, k1_xboole_0))), inference(splitRight, [status(thm)], [c_1332])).
% 5.50/2.10  tff(c_62, plain, (![A_48, B_49]: (k1_xboole_0!=A_48 | '#skF_6'(A_48, B_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_60])).
% 5.50/2.10  tff(c_1254, plain, (![A_2230, B_2231, D_2232]: (k1_funct_1('#skF_6'(A_2230, B_2231), D_2232)=B_2231 | ~r2_hidden(D_2232, A_2230))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_1263, plain, (![D_2232, B_49, A_48]: (k1_funct_1(k1_xboole_0, D_2232)=B_49 | ~r2_hidden(D_2232, A_48) | k1_xboole_0!=A_48)), inference(superposition, [status(thm), theory('equality')], [c_62, c_1254])).
% 5.50/2.10  tff(c_4358, plain, (![B_2468]: (k1_funct_1(k1_xboole_0, B_2468)='#skF_8')), inference(resolution, [status(thm)], [c_4264, c_1263])).
% 5.50/2.10  tff(c_4277, plain, (![B_2464, B_49]: (k1_funct_1(k1_xboole_0, B_2464)=B_49)), inference(resolution, [status(thm)], [c_4264, c_1263])).
% 5.50/2.10  tff(c_4753, plain, (![B_3474]: (B_3474='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4358, c_4277])).
% 5.50/2.10  tff(c_134, plain, (~r1_tarski(k1_xboole_0, '#skF_7') | k1_relat_1(k1_xboole_0)!='#skF_8' | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_128, c_42])).
% 5.50/2.10  tff(c_138, plain, (~r1_tarski(k1_xboole_0, '#skF_7') | k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_87, c_101, c_102, c_134])).
% 5.50/2.10  tff(c_140, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_138])).
% 5.50/2.10  tff(c_4813, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4753, c_140])).
% 5.50/2.10  tff(c_4815, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_138])).
% 5.50/2.10  tff(c_4824, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4815, c_45])).
% 5.50/2.10  tff(c_130, plain, (![A_48, B_49]: (k2_relat_1('#skF_6'(A_48, B_49))=k1_xboole_0 | k1_xboole_0!=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_125])).
% 5.50/2.10  tff(c_4886, plain, (![B_49]: (k2_relat_1('#skF_6'('#skF_8', B_49))='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4815, c_4815, c_130])).
% 5.50/2.10  tff(c_4821, plain, (v1_relat_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4815, c_87])).
% 5.50/2.10  tff(c_4820, plain, (v1_funct_1('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4815, c_101])).
% 5.50/2.10  tff(c_70, plain, (![A_64]: (k1_relat_1(k1_xboole_0)=A_64 | k1_xboole_0!=A_64)), inference(superposition, [status(thm), theory('equality')], [c_64, c_36])).
% 5.50/2.10  tff(c_4846, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4815, c_4815, c_70])).
% 5.50/2.10  tff(c_4816, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_4815, c_4815, c_128])).
% 5.50/2.10  tff(c_4979, plain, (![A_3973, D_3974]: (r2_hidden(k1_funct_1(A_3973, D_3974), k2_relat_1(A_3973)) | ~r2_hidden(D_3974, k1_relat_1(A_3973)) | ~v1_funct_1(A_3973) | ~v1_relat_1(A_3973))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.50/2.10  tff(c_4990, plain, (![D_3974]: (r2_hidden(k1_funct_1('#skF_8', D_3974), '#skF_8') | ~r2_hidden(D_3974, k1_relat_1('#skF_8')) | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_4816, c_4979])).
% 5.50/2.10  tff(c_4997, plain, (![D_3974]: (r2_hidden(k1_funct_1('#skF_8', D_3974), '#skF_8') | ~r2_hidden(D_3974, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4821, c_4820, c_4846, c_4990])).
% 5.50/2.10  tff(c_4984, plain, (![B_49, A_48, D_54]: (r2_hidden(B_49, k2_relat_1('#skF_6'(A_48, B_49))) | ~r2_hidden(D_54, k1_relat_1('#skF_6'(A_48, B_49))) | ~v1_funct_1('#skF_6'(A_48, B_49)) | ~v1_relat_1('#skF_6'(A_48, B_49)) | ~r2_hidden(D_54, A_48))), inference(superposition, [status(thm), theory('equality')], [c_34, c_4979])).
% 5.50/2.10  tff(c_5002, plain, (![B_3976, A_3977, D_3978]: (r2_hidden(B_3976, k2_relat_1('#skF_6'(A_3977, B_3976))) | ~r2_hidden(D_3978, A_3977))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_36, c_4984])).
% 5.50/2.10  tff(c_5004, plain, (![B_3976, D_3974]: (r2_hidden(B_3976, k2_relat_1('#skF_6'('#skF_8', B_3976))) | ~r2_hidden(D_3974, '#skF_8'))), inference(resolution, [status(thm)], [c_4997, c_5002])).
% 5.50/2.10  tff(c_5010, plain, (![B_3976, D_3974]: (r2_hidden(B_3976, '#skF_8') | ~r2_hidden(D_3974, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_4886, c_5004])).
% 5.50/2.10  tff(c_5015, plain, (![D_3979]: (~r2_hidden(D_3979, '#skF_8'))), inference(splitLeft, [status(thm)], [c_5010])).
% 5.50/2.10  tff(c_5020, plain, (![B_2]: (r1_tarski('#skF_8', B_2))), inference(resolution, [status(thm)], [c_6, c_5015])).
% 5.50/2.10  tff(c_4814, plain, (~r1_tarski(k1_xboole_0, '#skF_7')), inference(splitRight, [status(thm)], [c_138])).
% 5.50/2.10  tff(c_4829, plain, (~r1_tarski('#skF_8', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_4815, c_4814])).
% 5.50/2.10  tff(c_5023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5020, c_4829])).
% 5.50/2.10  tff(c_5024, plain, (![B_3976]: (r2_hidden(B_3976, '#skF_8'))), inference(splitRight, [status(thm)], [c_5010])).
% 5.50/2.10  tff(c_4822, plain, (![A_48, B_49]: (A_48!='#skF_8' | '#skF_6'(A_48, B_49)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_4815, c_4815, c_62])).
% 5.50/2.10  tff(c_4952, plain, (![A_3965, B_3966, D_3967]: (k1_funct_1('#skF_6'(A_3965, B_3966), D_3967)=B_3966 | ~r2_hidden(D_3967, A_3965))), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.50/2.10  tff(c_5149, plain, (![D_3993, B_3994, A_3995]: (k1_funct_1('#skF_8', D_3993)=B_3994 | ~r2_hidden(D_3993, A_3995) | A_3995!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_4822, c_4952])).
% 5.50/2.10  tff(c_5199, plain, (![B_3996]: (k1_funct_1('#skF_8', B_3996)='#skF_7')), inference(resolution, [status(thm)], [c_5024, c_5149])).
% 5.50/2.10  tff(c_5165, plain, (![B_3976, B_3994]: (k1_funct_1('#skF_8', B_3976)=B_3994)), inference(resolution, [status(thm)], [c_5024, c_5149])).
% 5.50/2.10  tff(c_5604, plain, (![B_5242]: (B_5242='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_5199, c_5165])).
% 5.50/2.10  tff(c_5655, plain, ('#skF_7'='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_5604, c_4816])).
% 5.50/2.10  tff(c_5677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4824, c_5655])).
% 5.50/2.10  tff(c_5678, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_44])).
% 5.50/2.10  tff(c_10, plain, (![A_6]: (k1_relat_1(A_6)!=k1_xboole_0 | k1_xboole_0=A_6 | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 5.50/2.10  tff(c_5709, plain, (![A_5914]: (k1_relat_1(A_5914)!='#skF_8' | A_5914='#skF_8' | ~v1_relat_1(A_5914))), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_5678, c_10])).
% 5.50/2.10  tff(c_5712, plain, (![A_48, B_49]: (k1_relat_1('#skF_6'(A_48, B_49))!='#skF_8' | '#skF_6'(A_48, B_49)='#skF_8')), inference(resolution, [status(thm)], [c_40, c_5709])).
% 5.50/2.10  tff(c_5723, plain, (![A_5916, B_5917]: (A_5916!='#skF_8' | '#skF_6'(A_5916, B_5917)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_5712])).
% 5.50/2.10  tff(c_5731, plain, (![A_5916]: (v1_relat_1('#skF_8') | A_5916!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5723, c_40])).
% 5.50/2.10  tff(c_5739, plain, (![A_5916]: (A_5916!='#skF_8')), inference(splitLeft, [status(thm)], [c_5731])).
% 5.50/2.10  tff(c_5679, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_44])).
% 5.50/2.10  tff(c_5684, plain, ('#skF_7'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_5679])).
% 5.50/2.10  tff(c_5746, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5739, c_5684])).
% 5.50/2.10  tff(c_5747, plain, (v1_relat_1('#skF_8')), inference(splitRight, [status(thm)], [c_5731])).
% 5.50/2.10  tff(c_5733, plain, (![A_5916]: (v1_funct_1('#skF_8') | A_5916!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5723, c_38])).
% 5.50/2.10  tff(c_5773, plain, (![A_5916]: (A_5916!='#skF_8')), inference(splitLeft, [status(thm)], [c_5733])).
% 5.50/2.10  tff(c_5781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5773, c_5684])).
% 5.50/2.10  tff(c_5782, plain, (v1_funct_1('#skF_8')), inference(splitRight, [status(thm)], [c_5733])).
% 5.50/2.10  tff(c_5783, plain, (k1_relat_1('#skF_8')='#skF_8'), inference(superposition, [status(thm), theory('equality')], [c_5723, c_36])).
% 5.50/2.10  tff(c_14, plain, (![A_7]: (k2_relat_1(A_7)=k1_xboole_0 | k1_relat_1(A_7)!=k1_xboole_0 | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.50/2.10  tff(c_5748, plain, (![A_7]: (k2_relat_1(A_7)='#skF_8' | k1_relat_1(A_7)!='#skF_8' | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_5678, c_5678, c_14])).
% 5.50/2.10  tff(c_5767, plain, (k2_relat_1('#skF_8')='#skF_8' | k1_relat_1('#skF_8')!='#skF_8'), inference(resolution, [status(thm)], [c_5747, c_5748])).
% 5.50/2.10  tff(c_5791, plain, (k2_relat_1('#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5783, c_5767])).
% 5.50/2.10  tff(c_5689, plain, (![C_56]: (~r1_tarski(k2_relat_1(C_56), '#skF_8') | k1_relat_1(C_56)!='#skF_8' | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(demodulation, [status(thm), theory('equality')], [c_5684, c_42])).
% 5.50/2.10  tff(c_5795, plain, (~r1_tarski('#skF_8', '#skF_8') | k1_relat_1('#skF_8')!='#skF_8' | ~v1_funct_1('#skF_8') | ~v1_relat_1('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_5791, c_5689])).
% 5.50/2.10  tff(c_5799, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5747, c_5782, c_5783, c_5795])).
% 5.50/2.10  tff(c_5811, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5808, c_5799])).
% 5.50/2.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.50/2.10  
% 5.50/2.10  Inference rules
% 5.50/2.10  ----------------------
% 5.50/2.10  #Ref     : 7
% 5.50/2.10  #Sup     : 1350
% 5.50/2.10  #Fact    : 0
% 5.50/2.10  #Define  : 0
% 5.50/2.10  #Split   : 12
% 5.50/2.10  #Chain   : 0
% 5.50/2.10  #Close   : 0
% 5.50/2.10  
% 5.50/2.10  Ordering : KBO
% 5.50/2.10  
% 5.50/2.10  Simplification rules
% 5.50/2.10  ----------------------
% 5.50/2.10  #Subsume      : 468
% 5.50/2.10  #Demod        : 971
% 5.50/2.10  #Tautology    : 183
% 5.50/2.10  #SimpNegUnit  : 52
% 5.50/2.10  #BackRed      : 16
% 5.50/2.10  
% 5.50/2.10  #Partial instantiations: 1931
% 5.50/2.10  #Strategies tried      : 1
% 5.50/2.10  
% 5.50/2.10  Timing (in seconds)
% 5.50/2.10  ----------------------
% 5.50/2.11  Preprocessing        : 0.30
% 5.50/2.11  Parsing              : 0.15
% 5.50/2.11  CNF conversion       : 0.03
% 5.50/2.11  Main loop            : 1.01
% 5.50/2.11  Inferencing          : 0.40
% 5.50/2.11  Reduction            : 0.31
% 5.50/2.11  Demodulation         : 0.21
% 5.50/2.11  BG Simplification    : 0.04
% 5.50/2.11  Subsumption          : 0.19
% 5.50/2.11  Abstraction          : 0.05
% 5.50/2.11  MUC search           : 0.00
% 5.50/2.11  Cooper               : 0.00
% 5.50/2.11  Total                : 1.36
% 5.50/2.11  Index Insertion      : 0.00
% 5.50/2.11  Index Deletion       : 0.00
% 5.50/2.11  Index Matching       : 0.00
% 5.50/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
