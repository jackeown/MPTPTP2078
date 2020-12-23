%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:50 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.79s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 287 expanded)
%              Number of leaves         :   17 ( 100 expanded)
%              Depth                    :   12
%              Number of atoms          :  170 ( 717 expanded)
%              Number of equality atoms :   25 (  89 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( ! [C] :
              ( m1_subset_1(C,A)
             => r2_hidden(C,B) )
         => A = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_2135,plain,(
    ! [B_168,A_169] :
      ( m1_subset_1(B_168,A_169)
      | ~ v1_xboole_0(B_168)
      | ~ v1_xboole_0(A_169) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_28,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [C_15] :
      ( r2_hidden(C_15,'#skF_5')
      | ~ m1_subset_1(C_15,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_83,plain,(
    ! [C_30,A_31,B_32] :
      ( r2_hidden(C_30,A_31)
      | ~ r2_hidden(C_30,B_32)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_131,plain,(
    ! [C_39,A_40] :
      ( r2_hidden(C_39,A_40)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(A_40))
      | ~ m1_subset_1(C_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_138,plain,(
    ! [C_39] :
      ( r2_hidden(C_39,'#skF_4')
      | ~ m1_subset_1(C_39,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_131])).

tff(c_93,plain,(
    ! [A_33,B_34] :
      ( ~ r2_hidden('#skF_2'(A_33,B_34),A_33)
      | ~ r2_hidden('#skF_3'(A_33,B_34),B_34)
      | B_34 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_308,plain,(
    ! [B_64] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_64),B_64)
      | B_64 = '#skF_5'
      | ~ m1_subset_1('#skF_2'('#skF_5',B_64),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_324,plain,
    ( '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_138,c_308])).

tff(c_339,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_324])).

tff(c_343,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_339])).

tff(c_30,plain,(
    ! [C_18] :
      ( r2_hidden(C_18,'#skF_5')
      | ~ m1_subset_1(C_18,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    ! [C_18] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ m1_subset_1(C_18,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_2])).

tff(c_35,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_102,plain,(
    ! [A_35,A_36] :
      ( r2_hidden('#skF_1'(A_35),A_36)
      | ~ m1_subset_1(A_35,k1_zfmisc_1(A_36))
      | v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_114,plain,(
    ! [A_37,A_38] :
      ( ~ v1_xboole_0(A_37)
      | ~ m1_subset_1(A_38,k1_zfmisc_1(A_37))
      | v1_xboole_0(A_38) ) ),
    inference(resolution,[status(thm)],[c_102,c_2])).

tff(c_125,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_114])).

tff(c_130,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_125])).

tff(c_197,plain,(
    ! [A_49,B_50] :
      ( r2_hidden('#skF_2'(A_49,B_50),B_50)
      | r2_hidden('#skF_3'(A_49,B_50),A_49)
      | B_50 = A_49 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_22,plain,(
    ! [C_13,A_10,B_11] :
      ( r2_hidden(C_13,A_10)
      | ~ r2_hidden(C_13,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1206,plain,(
    ! [A_117,B_118,A_119] :
      ( r2_hidden('#skF_3'(A_117,B_118),A_119)
      | ~ m1_subset_1(A_117,k1_zfmisc_1(A_119))
      | r2_hidden('#skF_2'(A_117,B_118),B_118)
      | B_118 = A_117 ) ),
    inference(resolution,[status(thm)],[c_197,c_22])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden('#skF_2'(A_5,B_6),B_6)
      | ~ r2_hidden('#skF_3'(A_5,B_6),B_6)
      | B_6 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1278,plain,(
    ! [A_120,A_121] :
      ( ~ m1_subset_1(A_120,k1_zfmisc_1(A_121))
      | r2_hidden('#skF_2'(A_120,A_121),A_121)
      | A_121 = A_120 ) ),
    inference(resolution,[status(thm)],[c_1206,c_8])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( m1_subset_1(B_9,A_8)
      | ~ r2_hidden(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1626,plain,(
    ! [A_141,A_142] :
      ( m1_subset_1('#skF_2'(A_141,A_142),A_142)
      | v1_xboole_0(A_142)
      | ~ m1_subset_1(A_141,k1_zfmisc_1(A_142))
      | A_142 = A_141 ) ),
    inference(resolution,[status(thm)],[c_1278,c_14])).

tff(c_179,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden('#skF_2'(A_47,B_48),A_47)
      | r2_hidden('#skF_3'(A_47,B_48),A_47)
      | B_48 = A_47 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1102,plain,(
    ! [A_114,B_115] :
      ( m1_subset_1('#skF_3'(A_114,B_115),A_114)
      | v1_xboole_0(A_114)
      | ~ r2_hidden('#skF_2'(A_114,B_115),A_114)
      | B_115 = A_114 ) ),
    inference(resolution,[status(thm)],[c_179,c_14])).

tff(c_1152,plain,(
    ! [B_115] :
      ( m1_subset_1('#skF_3'('#skF_5',B_115),'#skF_5')
      | v1_xboole_0('#skF_5')
      | B_115 = '#skF_5'
      | ~ m1_subset_1('#skF_2'('#skF_5',B_115),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_1102])).

tff(c_1178,plain,(
    ! [B_116] :
      ( m1_subset_1('#skF_3'('#skF_5',B_116),'#skF_5')
      | B_116 = '#skF_5'
      | ~ m1_subset_1('#skF_2'('#skF_5',B_116),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_1152])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r2_hidden(B_9,A_8)
      | ~ m1_subset_1(B_9,A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_344,plain,(
    ! [B_65,A_66,A_67] :
      ( r2_hidden(B_65,A_66)
      | ~ m1_subset_1(A_67,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_65,A_67)
      | v1_xboole_0(A_67) ) ),
    inference(resolution,[status(thm)],[c_16,c_83])).

tff(c_358,plain,(
    ! [B_65] :
      ( r2_hidden(B_65,'#skF_4')
      | ~ m1_subset_1(B_65,'#skF_5')
      | v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_344])).

tff(c_370,plain,(
    ! [B_68] :
      ( r2_hidden(B_68,'#skF_4')
      | ~ m1_subset_1(B_68,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_358])).

tff(c_101,plain,(
    ! [B_34] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_34),B_34)
      | B_34 = '#skF_5'
      | ~ m1_subset_1('#skF_2'('#skF_5',B_34),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_93])).

tff(c_374,plain,
    ( '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_370,c_101])).

tff(c_392,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_4')
    | ~ m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_374])).

tff(c_431,plain,(
    ~ m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_1189,plain,
    ( '#skF_5' = '#skF_4'
    | ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1178,c_431])).

tff(c_1203,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1189])).

tff(c_1645,plain,
    ( v1_xboole_0('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1('#skF_4'))
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1626,c_1203])).

tff(c_1678,plain,
    ( v1_xboole_0('#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_1645])).

tff(c_1680,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_130,c_1678])).

tff(c_1682,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_386,plain,(
    ! [B_68] :
      ( m1_subset_1(B_68,'#skF_4')
      | v1_xboole_0('#skF_4')
      | ~ m1_subset_1(B_68,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_370,c_14])).

tff(c_398,plain,(
    ! [B_68] :
      ( m1_subset_1(B_68,'#skF_4')
      | ~ m1_subset_1(B_68,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_386])).

tff(c_1698,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1682,c_398])).

tff(c_1705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_343,c_1698])).

tff(c_1706,plain,(
    ~ m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_1707,plain,(
    m1_subset_1('#skF_3'('#skF_5','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_339])).

tff(c_163,plain,(
    ! [A_45,B_46] :
      ( r2_hidden('#skF_2'(A_45,B_46),B_46)
      | ~ r2_hidden('#skF_3'(A_45,B_46),B_46)
      | B_46 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1772,plain,(
    ! [A_147] :
      ( r2_hidden('#skF_2'(A_147,'#skF_4'),'#skF_4')
      | A_147 = '#skF_4'
      | ~ m1_subset_1('#skF_3'(A_147,'#skF_4'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_138,c_163])).

tff(c_1780,plain,(
    ! [A_147] :
      ( m1_subset_1('#skF_2'(A_147,'#skF_4'),'#skF_4')
      | v1_xboole_0('#skF_4')
      | A_147 = '#skF_4'
      | ~ m1_subset_1('#skF_3'(A_147,'#skF_4'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_1772,c_14])).

tff(c_2106,plain,(
    ! [A_165] :
      ( m1_subset_1('#skF_2'(A_165,'#skF_4'),'#skF_4')
      | A_165 = '#skF_4'
      | ~ m1_subset_1('#skF_3'(A_165,'#skF_4'),'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1780])).

tff(c_2113,plain,
    ( m1_subset_1('#skF_2'('#skF_5','#skF_4'),'#skF_4')
    | '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1707,c_2106])).

tff(c_2126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1706,c_2113])).

tff(c_2127,plain,(
    ! [C_18] : ~ m1_subset_1(C_18,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2140,plain,(
    ! [B_168] :
      ( ~ v1_xboole_0(B_168)
      | ~ v1_xboole_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2135,c_2127])).

tff(c_2141,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2140])).

tff(c_2157,plain,(
    ! [B_174,A_175] :
      ( m1_subset_1(B_174,A_175)
      | ~ r2_hidden(B_174,A_175)
      | v1_xboole_0(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2166,plain,(
    ! [A_176] :
      ( m1_subset_1('#skF_1'(A_176),A_176)
      | v1_xboole_0(A_176) ) ),
    inference(resolution,[status(thm)],[c_4,c_2157])).

tff(c_2173,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2166,c_2127])).

tff(c_2178,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2141,c_2173])).

tff(c_2179,plain,(
    ! [B_168] : ~ v1_xboole_0(B_168) ),
    inference(splitRight,[status(thm)],[c_2140])).

tff(c_2128,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_2183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2179,c_2128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.69  
% 3.60/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.69  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2
% 3.60/1.69  
% 3.60/1.69  %Foreground sorts:
% 3.60/1.69  
% 3.60/1.69  
% 3.60/1.69  %Background operators:
% 3.60/1.69  
% 3.60/1.69  
% 3.60/1.69  %Foreground operators:
% 3.60/1.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.69  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.60/1.69  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.60/1.69  tff('#skF_5', type, '#skF_5': $i).
% 3.60/1.69  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.69  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.69  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.60/1.69  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.69  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.69  
% 3.79/1.71  tff(f_51, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 3.79/1.71  tff(f_68, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => ((![C]: (m1_subset_1(C, A) => r2_hidden(C, B))) => (A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_subset_1)).
% 3.79/1.71  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 3.79/1.71  tff(f_38, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tarski)).
% 3.79/1.71  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.79/1.71  tff(c_2135, plain, (![B_168, A_169]: (m1_subset_1(B_168, A_169) | ~v1_xboole_0(B_168) | ~v1_xboole_0(A_169))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.71  tff(c_24, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.79/1.71  tff(c_28, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.79/1.71  tff(c_26, plain, (![C_15]: (r2_hidden(C_15, '#skF_5') | ~m1_subset_1(C_15, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.79/1.71  tff(c_83, plain, (![C_30, A_31, B_32]: (r2_hidden(C_30, A_31) | ~r2_hidden(C_30, B_32) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.79/1.71  tff(c_131, plain, (![C_39, A_40]: (r2_hidden(C_39, A_40) | ~m1_subset_1('#skF_5', k1_zfmisc_1(A_40)) | ~m1_subset_1(C_39, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_83])).
% 3.79/1.71  tff(c_138, plain, (![C_39]: (r2_hidden(C_39, '#skF_4') | ~m1_subset_1(C_39, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_131])).
% 3.79/1.71  tff(c_93, plain, (![A_33, B_34]: (~r2_hidden('#skF_2'(A_33, B_34), A_33) | ~r2_hidden('#skF_3'(A_33, B_34), B_34) | B_34=A_33)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.79/1.71  tff(c_308, plain, (![B_64]: (~r2_hidden('#skF_3'('#skF_5', B_64), B_64) | B_64='#skF_5' | ~m1_subset_1('#skF_2'('#skF_5', B_64), '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_93])).
% 3.79/1.71  tff(c_324, plain, ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_138, c_308])).
% 3.79/1.71  tff(c_339, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_24, c_324])).
% 3.79/1.71  tff(c_343, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_339])).
% 3.79/1.71  tff(c_30, plain, (![C_18]: (r2_hidden(C_18, '#skF_5') | ~m1_subset_1(C_18, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.79/1.71  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.71  tff(c_34, plain, (![C_18]: (~v1_xboole_0('#skF_5') | ~m1_subset_1(C_18, '#skF_4'))), inference(resolution, [status(thm)], [c_30, c_2])).
% 3.79/1.71  tff(c_35, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 3.79/1.71  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.79/1.71  tff(c_102, plain, (![A_35, A_36]: (r2_hidden('#skF_1'(A_35), A_36) | ~m1_subset_1(A_35, k1_zfmisc_1(A_36)) | v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_4, c_83])).
% 3.79/1.71  tff(c_114, plain, (![A_37, A_38]: (~v1_xboole_0(A_37) | ~m1_subset_1(A_38, k1_zfmisc_1(A_37)) | v1_xboole_0(A_38))), inference(resolution, [status(thm)], [c_102, c_2])).
% 3.79/1.71  tff(c_125, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_114])).
% 3.79/1.71  tff(c_130, plain, (~v1_xboole_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_35, c_125])).
% 3.79/1.71  tff(c_197, plain, (![A_49, B_50]: (r2_hidden('#skF_2'(A_49, B_50), B_50) | r2_hidden('#skF_3'(A_49, B_50), A_49) | B_50=A_49)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.79/1.71  tff(c_22, plain, (![C_13, A_10, B_11]: (r2_hidden(C_13, A_10) | ~r2_hidden(C_13, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.79/1.71  tff(c_1206, plain, (![A_117, B_118, A_119]: (r2_hidden('#skF_3'(A_117, B_118), A_119) | ~m1_subset_1(A_117, k1_zfmisc_1(A_119)) | r2_hidden('#skF_2'(A_117, B_118), B_118) | B_118=A_117)), inference(resolution, [status(thm)], [c_197, c_22])).
% 3.79/1.71  tff(c_8, plain, (![A_5, B_6]: (r2_hidden('#skF_2'(A_5, B_6), B_6) | ~r2_hidden('#skF_3'(A_5, B_6), B_6) | B_6=A_5)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.79/1.71  tff(c_1278, plain, (![A_120, A_121]: (~m1_subset_1(A_120, k1_zfmisc_1(A_121)) | r2_hidden('#skF_2'(A_120, A_121), A_121) | A_121=A_120)), inference(resolution, [status(thm)], [c_1206, c_8])).
% 3.79/1.71  tff(c_14, plain, (![B_9, A_8]: (m1_subset_1(B_9, A_8) | ~r2_hidden(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.71  tff(c_1626, plain, (![A_141, A_142]: (m1_subset_1('#skF_2'(A_141, A_142), A_142) | v1_xboole_0(A_142) | ~m1_subset_1(A_141, k1_zfmisc_1(A_142)) | A_142=A_141)), inference(resolution, [status(thm)], [c_1278, c_14])).
% 3.79/1.71  tff(c_179, plain, (![A_47, B_48]: (~r2_hidden('#skF_2'(A_47, B_48), A_47) | r2_hidden('#skF_3'(A_47, B_48), A_47) | B_48=A_47)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.79/1.71  tff(c_1102, plain, (![A_114, B_115]: (m1_subset_1('#skF_3'(A_114, B_115), A_114) | v1_xboole_0(A_114) | ~r2_hidden('#skF_2'(A_114, B_115), A_114) | B_115=A_114)), inference(resolution, [status(thm)], [c_179, c_14])).
% 3.79/1.71  tff(c_1152, plain, (![B_115]: (m1_subset_1('#skF_3'('#skF_5', B_115), '#skF_5') | v1_xboole_0('#skF_5') | B_115='#skF_5' | ~m1_subset_1('#skF_2'('#skF_5', B_115), '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_1102])).
% 3.79/1.71  tff(c_1178, plain, (![B_116]: (m1_subset_1('#skF_3'('#skF_5', B_116), '#skF_5') | B_116='#skF_5' | ~m1_subset_1('#skF_2'('#skF_5', B_116), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_35, c_1152])).
% 3.79/1.71  tff(c_16, plain, (![B_9, A_8]: (r2_hidden(B_9, A_8) | ~m1_subset_1(B_9, A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.71  tff(c_344, plain, (![B_65, A_66, A_67]: (r2_hidden(B_65, A_66) | ~m1_subset_1(A_67, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_65, A_67) | v1_xboole_0(A_67))), inference(resolution, [status(thm)], [c_16, c_83])).
% 3.79/1.71  tff(c_358, plain, (![B_65]: (r2_hidden(B_65, '#skF_4') | ~m1_subset_1(B_65, '#skF_5') | v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_344])).
% 3.79/1.71  tff(c_370, plain, (![B_68]: (r2_hidden(B_68, '#skF_4') | ~m1_subset_1(B_68, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_35, c_358])).
% 3.79/1.71  tff(c_101, plain, (![B_34]: (~r2_hidden('#skF_3'('#skF_5', B_34), B_34) | B_34='#skF_5' | ~m1_subset_1('#skF_2'('#skF_5', B_34), '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_93])).
% 3.79/1.71  tff(c_374, plain, ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_370, c_101])).
% 3.79/1.71  tff(c_392, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_4') | ~m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_24, c_374])).
% 3.79/1.71  tff(c_431, plain, (~m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_5')), inference(splitLeft, [status(thm)], [c_392])).
% 3.79/1.71  tff(c_1189, plain, ('#skF_5'='#skF_4' | ~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1178, c_431])).
% 3.79/1.71  tff(c_1203, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_24, c_1189])).
% 3.79/1.71  tff(c_1645, plain, (v1_xboole_0('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1('#skF_4')) | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1626, c_1203])).
% 3.79/1.71  tff(c_1678, plain, (v1_xboole_0('#skF_4') | '#skF_5'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_1645])).
% 3.79/1.71  tff(c_1680, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_130, c_1678])).
% 3.79/1.71  tff(c_1682, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_5')), inference(splitRight, [status(thm)], [c_392])).
% 3.79/1.71  tff(c_386, plain, (![B_68]: (m1_subset_1(B_68, '#skF_4') | v1_xboole_0('#skF_4') | ~m1_subset_1(B_68, '#skF_5'))), inference(resolution, [status(thm)], [c_370, c_14])).
% 3.79/1.71  tff(c_398, plain, (![B_68]: (m1_subset_1(B_68, '#skF_4') | ~m1_subset_1(B_68, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_130, c_386])).
% 3.79/1.71  tff(c_1698, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1682, c_398])).
% 3.79/1.71  tff(c_1705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_343, c_1698])).
% 3.79/1.71  tff(c_1706, plain, (~m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_339])).
% 3.79/1.71  tff(c_1707, plain, (m1_subset_1('#skF_3'('#skF_5', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_339])).
% 3.79/1.71  tff(c_163, plain, (![A_45, B_46]: (r2_hidden('#skF_2'(A_45, B_46), B_46) | ~r2_hidden('#skF_3'(A_45, B_46), B_46) | B_46=A_45)), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.79/1.71  tff(c_1772, plain, (![A_147]: (r2_hidden('#skF_2'(A_147, '#skF_4'), '#skF_4') | A_147='#skF_4' | ~m1_subset_1('#skF_3'(A_147, '#skF_4'), '#skF_4'))), inference(resolution, [status(thm)], [c_138, c_163])).
% 3.79/1.71  tff(c_1780, plain, (![A_147]: (m1_subset_1('#skF_2'(A_147, '#skF_4'), '#skF_4') | v1_xboole_0('#skF_4') | A_147='#skF_4' | ~m1_subset_1('#skF_3'(A_147, '#skF_4'), '#skF_4'))), inference(resolution, [status(thm)], [c_1772, c_14])).
% 3.79/1.71  tff(c_2106, plain, (![A_165]: (m1_subset_1('#skF_2'(A_165, '#skF_4'), '#skF_4') | A_165='#skF_4' | ~m1_subset_1('#skF_3'(A_165, '#skF_4'), '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_130, c_1780])).
% 3.79/1.71  tff(c_2113, plain, (m1_subset_1('#skF_2'('#skF_5', '#skF_4'), '#skF_4') | '#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_1707, c_2106])).
% 3.79/1.71  tff(c_2126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1706, c_2113])).
% 3.79/1.71  tff(c_2127, plain, (![C_18]: (~m1_subset_1(C_18, '#skF_4'))), inference(splitRight, [status(thm)], [c_34])).
% 3.79/1.71  tff(c_2140, plain, (![B_168]: (~v1_xboole_0(B_168) | ~v1_xboole_0('#skF_4'))), inference(resolution, [status(thm)], [c_2135, c_2127])).
% 3.79/1.71  tff(c_2141, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2140])).
% 3.79/1.71  tff(c_2157, plain, (![B_174, A_175]: (m1_subset_1(B_174, A_175) | ~r2_hidden(B_174, A_175) | v1_xboole_0(A_175))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.79/1.71  tff(c_2166, plain, (![A_176]: (m1_subset_1('#skF_1'(A_176), A_176) | v1_xboole_0(A_176))), inference(resolution, [status(thm)], [c_4, c_2157])).
% 3.79/1.71  tff(c_2173, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_2166, c_2127])).
% 3.79/1.71  tff(c_2178, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2141, c_2173])).
% 3.79/1.71  tff(c_2179, plain, (![B_168]: (~v1_xboole_0(B_168))), inference(splitRight, [status(thm)], [c_2140])).
% 3.79/1.71  tff(c_2128, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 3.79/1.71  tff(c_2183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2179, c_2128])).
% 3.79/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.79/1.71  
% 3.79/1.71  Inference rules
% 3.79/1.71  ----------------------
% 3.79/1.71  #Ref     : 0
% 3.79/1.71  #Sup     : 426
% 3.79/1.71  #Fact    : 0
% 3.79/1.71  #Define  : 0
% 3.79/1.71  #Split   : 6
% 3.79/1.71  #Chain   : 0
% 3.79/1.71  #Close   : 0
% 3.79/1.71  
% 3.79/1.71  Ordering : KBO
% 3.79/1.71  
% 3.79/1.71  Simplification rules
% 3.79/1.71  ----------------------
% 3.79/1.71  #Subsume      : 174
% 3.79/1.71  #Demod        : 4
% 3.79/1.71  #Tautology    : 72
% 3.79/1.71  #SimpNegUnit  : 94
% 3.79/1.71  #BackRed      : 2
% 3.79/1.71  
% 3.79/1.71  #Partial instantiations: 0
% 3.79/1.71  #Strategies tried      : 1
% 3.79/1.71  
% 3.79/1.71  Timing (in seconds)
% 3.79/1.71  ----------------------
% 3.79/1.71  Preprocessing        : 0.24
% 3.79/1.71  Parsing              : 0.13
% 3.79/1.71  CNF conversion       : 0.02
% 3.79/1.71  Main loop            : 0.60
% 3.79/1.71  Inferencing          : 0.24
% 3.79/1.71  Reduction            : 0.13
% 3.79/1.71  Demodulation         : 0.07
% 3.79/1.71  BG Simplification    : 0.02
% 3.79/1.71  Subsumption          : 0.17
% 3.79/1.71  Abstraction          : 0.03
% 3.79/1.71  MUC search           : 0.00
% 3.79/1.71  Cooper               : 0.00
% 3.79/1.71  Total                : 0.88
% 3.79/1.71  Index Insertion      : 0.00
% 3.79/1.71  Index Deletion       : 0.00
% 3.79/1.71  Index Matching       : 0.00
% 3.79/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
