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
% DateTime   : Thu Dec  3 10:28:16 EST 2020

% Result     : Theorem 4.07s
% Output     : CNFRefutation 4.48s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 274 expanded)
%              Number of leaves         :   24 ( 104 expanded)
%              Depth                    :   21
%              Number of atoms          :  150 ( 673 expanded)
%              Number of equality atoms :   33 ( 156 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ( ~ v1_xboole_0(B)
              & v1_zfmisc_1(B) )
           => ( r1_tarski(A,B)
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_38,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_40,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_100,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_106,plain,
    ( '#skF_7' = '#skF_6'
    | ~ r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_100])).

tff(c_114,plain,(
    ~ r1_tarski('#skF_7','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_106])).

tff(c_46,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_42,plain,(
    v1_zfmisc_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_5'(A_19),A_19)
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_201,plain,(
    ! [A_56,B_57] :
      ( k6_domain_1(A_56,B_57) = k1_tarski(B_57)
      | ~ m1_subset_1(B_57,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_714,plain,(
    ! [A_566] :
      ( k6_domain_1(A_566,'#skF_5'(A_566)) = k1_tarski('#skF_5'(A_566))
      | ~ v1_zfmisc_1(A_566)
      | v1_xboole_0(A_566) ) ),
    inference(resolution,[status(thm)],[c_36,c_201])).

tff(c_34,plain,(
    ! [A_19] :
      ( k6_domain_1(A_19,'#skF_5'(A_19)) = A_19
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1830,plain,(
    ! [A_2569] :
      ( k1_tarski('#skF_5'(A_2569)) = A_2569
      | ~ v1_zfmisc_1(A_2569)
      | v1_xboole_0(A_2569)
      | ~ v1_zfmisc_1(A_2569)
      | v1_xboole_0(A_2569) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_34])).

tff(c_20,plain,(
    ! [C_16] : r2_hidden(C_16,k1_tarski(C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ! [B_26,A_27] :
      ( ~ r2_hidden(B_26,A_27)
      | ~ v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [C_16] : ~ v1_xboole_0(k1_tarski(C_16)) ),
    inference(resolution,[status(thm)],[c_20,c_50])).

tff(c_62,plain,(
    ! [A_31] :
      ( v1_xboole_0(A_31)
      | r2_hidden('#skF_1'(A_31),A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [C_16,A_12] :
      ( C_16 = A_12
      | ~ r2_hidden(C_16,k1_tarski(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [A_12] :
      ( '#skF_1'(k1_tarski(A_12)) = A_12
      | v1_xboole_0(k1_tarski(A_12)) ) ),
    inference(resolution,[status(thm)],[c_62,c_18])).

tff(c_72,plain,(
    ! [A_12] : '#skF_1'(k1_tarski(A_12)) = A_12 ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_66])).

tff(c_2240,plain,(
    ! [A_2979] :
      ( '#skF_5'(A_2979) = '#skF_1'(A_2979)
      | ~ v1_zfmisc_1(A_2979)
      | v1_xboole_0(A_2979)
      | ~ v1_zfmisc_1(A_2979)
      | v1_xboole_0(A_2979) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1830,c_72])).

tff(c_2254,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_42,c_2240])).

tff(c_2257,plain,
    ( '#skF_5'('#skF_7') = '#skF_1'('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2254])).

tff(c_2258,plain,(
    '#skF_5'('#skF_7') = '#skF_1'('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2257])).

tff(c_720,plain,(
    ! [A_566] :
      ( k1_tarski('#skF_5'(A_566)) = A_566
      | ~ v1_zfmisc_1(A_566)
      | v1_xboole_0(A_566)
      | ~ v1_zfmisc_1(A_566)
      | v1_xboole_0(A_566) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_714,c_34])).

tff(c_2381,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7')
    | ~ v1_zfmisc_1('#skF_7')
    | v1_xboole_0('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2258,c_720])).

tff(c_2414,plain,
    ( k1_tarski('#skF_1'('#skF_7')) = '#skF_7'
    | v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_2381])).

tff(c_2415,plain,(
    k1_tarski('#skF_1'('#skF_7')) = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2414])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_88,plain,(
    ! [A_33,B_34] :
      ( r2_hidden('#skF_2'(A_33,B_34),A_33)
      | r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_96,plain,(
    ! [A_12,B_34] :
      ( '#skF_2'(k1_tarski(A_12),B_34) = A_12
      | r1_tarski(k1_tarski(A_12),B_34) ) ),
    inference(resolution,[status(thm)],[c_88,c_18])).

tff(c_151,plain,(
    ! [C_47,B_48,A_49] :
      ( r2_hidden(C_47,B_48)
      | ~ r2_hidden(C_47,A_49)
      | ~ r1_tarski(A_49,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_206,plain,(
    ! [A_58,B_59] :
      ( r2_hidden('#skF_1'(A_58),B_59)
      | ~ r1_tarski(A_58,B_59)
      | v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_4,c_151])).

tff(c_6,plain,(
    ! [C_9,B_6,A_5] :
      ( r2_hidden(C_9,B_6)
      | ~ r2_hidden(C_9,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1106,plain,(
    ! [A_1710,B_1711,B_1712] :
      ( r2_hidden('#skF_1'(A_1710),B_1711)
      | ~ r1_tarski(B_1712,B_1711)
      | ~ r1_tarski(A_1710,B_1712)
      | v1_xboole_0(A_1710) ) ),
    inference(resolution,[status(thm)],[c_206,c_6])).

tff(c_1131,plain,(
    ! [A_1746] :
      ( r2_hidden('#skF_1'(A_1746),'#skF_7')
      | ~ r1_tarski(A_1746,'#skF_6')
      | v1_xboole_0(A_1746) ) ),
    inference(resolution,[status(thm)],[c_40,c_1106])).

tff(c_1178,plain,(
    ! [A_12] :
      ( r2_hidden(A_12,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_12),'#skF_6')
      | v1_xboole_0(k1_tarski(A_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_1131])).

tff(c_1190,plain,(
    ! [A_1780] :
      ( r2_hidden(A_1780,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_1780),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1178])).

tff(c_1206,plain,(
    ! [A_1814] :
      ( r2_hidden(A_1814,'#skF_7')
      | '#skF_2'(k1_tarski(A_1814),'#skF_6') = A_1814 ) ),
    inference(resolution,[status(thm)],[c_96,c_1190])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1271,plain,(
    ! [A_1848] :
      ( ~ r2_hidden(A_1848,'#skF_6')
      | r1_tarski(k1_tarski(A_1848),'#skF_6')
      | r2_hidden(A_1848,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1206,c_8])).

tff(c_1189,plain,(
    ! [A_12] :
      ( r2_hidden(A_12,'#skF_7')
      | ~ r1_tarski(k1_tarski(A_12),'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_1178])).

tff(c_1327,plain,(
    ! [A_1882] :
      ( ~ r2_hidden(A_1882,'#skF_6')
      | r2_hidden(A_1882,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_1271,c_1189])).

tff(c_1444,plain,(
    ! [A_2054,B_2055] :
      ( r2_hidden(A_2054,B_2055)
      | ~ r1_tarski('#skF_7',B_2055)
      | ~ r2_hidden(A_2054,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1327,c_6])).

tff(c_1461,plain,(
    ! [B_2055] :
      ( r2_hidden('#skF_1'('#skF_6'),B_2055)
      | ~ r1_tarski('#skF_7',B_2055)
      | v1_xboole_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_4,c_1444])).

tff(c_1470,plain,(
    ! [B_2089] :
      ( r2_hidden('#skF_1'('#skF_6'),B_2089)
      | ~ r1_tarski('#skF_7',B_2089) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_1461])).

tff(c_1504,plain,(
    ! [A_12] :
      ( A_12 = '#skF_1'('#skF_6')
      | ~ r1_tarski('#skF_7',k1_tarski(A_12)) ) ),
    inference(resolution,[status(thm)],[c_1470,c_18])).

tff(c_2474,plain,
    ( '#skF_1'('#skF_7') = '#skF_1'('#skF_6')
    | ~ r1_tarski('#skF_7','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_2415,c_1504])).

tff(c_2574,plain,(
    '#skF_1'('#skF_7') = '#skF_1'('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2474])).

tff(c_2506,plain,(
    ! [B_34] :
      ( '#skF_2'(k1_tarski('#skF_1'('#skF_7')),B_34) = '#skF_1'('#skF_7')
      | r1_tarski('#skF_7',B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2415,c_96])).

tff(c_2578,plain,(
    ! [B_34] :
      ( '#skF_2'('#skF_7',B_34) = '#skF_1'('#skF_7')
      | r1_tarski('#skF_7',B_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2415,c_2506])).

tff(c_3259,plain,(
    ! [B_3428] :
      ( '#skF_2'('#skF_7',B_3428) = '#skF_1'('#skF_6')
      | r1_tarski('#skF_7',B_3428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2574,c_2578])).

tff(c_3337,plain,(
    '#skF_1'('#skF_6') = '#skF_2'('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_3259,c_114])).

tff(c_3366,plain,
    ( v1_xboole_0('#skF_6')
    | r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3337,c_4])).

tff(c_3375,plain,(
    r2_hidden('#skF_2'('#skF_7','#skF_6'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_3366])).

tff(c_3635,plain,(
    r1_tarski('#skF_7','#skF_6') ),
    inference(resolution,[status(thm)],[c_3375,c_8])).

tff(c_3650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_114,c_3635])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.07/1.77  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.43/1.78  
% 4.43/1.78  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.78  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > #nlpp > k1_tarski > #skF_5 > #skF_1 > #skF_7 > #skF_3 > #skF_6 > #skF_2 > #skF_4
% 4.48/1.78  
% 4.48/1.78  %Foreground sorts:
% 4.48/1.78  
% 4.48/1.78  
% 4.48/1.78  %Background operators:
% 4.48/1.78  
% 4.48/1.78  
% 4.48/1.78  %Foreground operators:
% 4.48/1.78  tff('#skF_5', type, '#skF_5': $i > $i).
% 4.48/1.78  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.78  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.48/1.78  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.48/1.78  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.48/1.78  tff('#skF_7', type, '#skF_7': $i).
% 4.48/1.78  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.48/1.78  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 4.48/1.78  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.78  tff('#skF_6', type, '#skF_6': $i).
% 4.48/1.78  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.78  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.78  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.48/1.78  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 4.48/1.78  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.48/1.78  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.48/1.78  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.78  
% 4.48/1.79  tff(f_82, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 4.48/1.79  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.48/1.79  tff(f_68, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 4.48/1.79  tff(f_58, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 4.48/1.79  tff(f_51, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.48/1.79  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.48/1.79  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.48/1.79  tff(c_38, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.48/1.79  tff(c_40, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.48/1.79  tff(c_100, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.48/1.79  tff(c_106, plain, ('#skF_7'='#skF_6' | ~r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_40, c_100])).
% 4.48/1.79  tff(c_114, plain, (~r1_tarski('#skF_7', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_106])).
% 4.48/1.79  tff(c_46, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.48/1.79  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.48/1.79  tff(c_44, plain, (~v1_xboole_0('#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.48/1.79  tff(c_42, plain, (v1_zfmisc_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.48/1.79  tff(c_36, plain, (![A_19]: (m1_subset_1('#skF_5'(A_19), A_19) | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.48/1.79  tff(c_201, plain, (![A_56, B_57]: (k6_domain_1(A_56, B_57)=k1_tarski(B_57) | ~m1_subset_1(B_57, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.48/1.79  tff(c_714, plain, (![A_566]: (k6_domain_1(A_566, '#skF_5'(A_566))=k1_tarski('#skF_5'(A_566)) | ~v1_zfmisc_1(A_566) | v1_xboole_0(A_566))), inference(resolution, [status(thm)], [c_36, c_201])).
% 4.48/1.79  tff(c_34, plain, (![A_19]: (k6_domain_1(A_19, '#skF_5'(A_19))=A_19 | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.48/1.79  tff(c_1830, plain, (![A_2569]: (k1_tarski('#skF_5'(A_2569))=A_2569 | ~v1_zfmisc_1(A_2569) | v1_xboole_0(A_2569) | ~v1_zfmisc_1(A_2569) | v1_xboole_0(A_2569))), inference(superposition, [status(thm), theory('equality')], [c_714, c_34])).
% 4.48/1.80  tff(c_20, plain, (![C_16]: (r2_hidden(C_16, k1_tarski(C_16)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.48/1.80  tff(c_50, plain, (![B_26, A_27]: (~r2_hidden(B_26, A_27) | ~v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.48/1.80  tff(c_54, plain, (![C_16]: (~v1_xboole_0(k1_tarski(C_16)))), inference(resolution, [status(thm)], [c_20, c_50])).
% 4.48/1.80  tff(c_62, plain, (![A_31]: (v1_xboole_0(A_31) | r2_hidden('#skF_1'(A_31), A_31))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.48/1.80  tff(c_18, plain, (![C_16, A_12]: (C_16=A_12 | ~r2_hidden(C_16, k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.48/1.80  tff(c_66, plain, (![A_12]: ('#skF_1'(k1_tarski(A_12))=A_12 | v1_xboole_0(k1_tarski(A_12)))), inference(resolution, [status(thm)], [c_62, c_18])).
% 4.48/1.80  tff(c_72, plain, (![A_12]: ('#skF_1'(k1_tarski(A_12))=A_12)), inference(negUnitSimplification, [status(thm)], [c_54, c_66])).
% 4.48/1.80  tff(c_2240, plain, (![A_2979]: ('#skF_5'(A_2979)='#skF_1'(A_2979) | ~v1_zfmisc_1(A_2979) | v1_xboole_0(A_2979) | ~v1_zfmisc_1(A_2979) | v1_xboole_0(A_2979))), inference(superposition, [status(thm), theory('equality')], [c_1830, c_72])).
% 4.48/1.80  tff(c_2254, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_42, c_2240])).
% 4.48/1.80  tff(c_2257, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7') | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2254])).
% 4.48/1.80  tff(c_2258, plain, ('#skF_5'('#skF_7')='#skF_1'('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_44, c_2257])).
% 4.48/1.80  tff(c_720, plain, (![A_566]: (k1_tarski('#skF_5'(A_566))=A_566 | ~v1_zfmisc_1(A_566) | v1_xboole_0(A_566) | ~v1_zfmisc_1(A_566) | v1_xboole_0(A_566))), inference(superposition, [status(thm), theory('equality')], [c_714, c_34])).
% 4.48/1.80  tff(c_2381, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7') | ~v1_zfmisc_1('#skF_7') | v1_xboole_0('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2258, c_720])).
% 4.48/1.80  tff(c_2414, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7' | v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_2381])).
% 4.48/1.80  tff(c_2415, plain, (k1_tarski('#skF_1'('#skF_7'))='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_44, c_2414])).
% 4.48/1.80  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.48/1.80  tff(c_88, plain, (![A_33, B_34]: (r2_hidden('#skF_2'(A_33, B_34), A_33) | r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.48/1.80  tff(c_96, plain, (![A_12, B_34]: ('#skF_2'(k1_tarski(A_12), B_34)=A_12 | r1_tarski(k1_tarski(A_12), B_34))), inference(resolution, [status(thm)], [c_88, c_18])).
% 4.48/1.80  tff(c_151, plain, (![C_47, B_48, A_49]: (r2_hidden(C_47, B_48) | ~r2_hidden(C_47, A_49) | ~r1_tarski(A_49, B_48))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.48/1.80  tff(c_206, plain, (![A_58, B_59]: (r2_hidden('#skF_1'(A_58), B_59) | ~r1_tarski(A_58, B_59) | v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_4, c_151])).
% 4.48/1.80  tff(c_6, plain, (![C_9, B_6, A_5]: (r2_hidden(C_9, B_6) | ~r2_hidden(C_9, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.48/1.80  tff(c_1106, plain, (![A_1710, B_1711, B_1712]: (r2_hidden('#skF_1'(A_1710), B_1711) | ~r1_tarski(B_1712, B_1711) | ~r1_tarski(A_1710, B_1712) | v1_xboole_0(A_1710))), inference(resolution, [status(thm)], [c_206, c_6])).
% 4.48/1.80  tff(c_1131, plain, (![A_1746]: (r2_hidden('#skF_1'(A_1746), '#skF_7') | ~r1_tarski(A_1746, '#skF_6') | v1_xboole_0(A_1746))), inference(resolution, [status(thm)], [c_40, c_1106])).
% 4.48/1.80  tff(c_1178, plain, (![A_12]: (r2_hidden(A_12, '#skF_7') | ~r1_tarski(k1_tarski(A_12), '#skF_6') | v1_xboole_0(k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_1131])).
% 4.48/1.80  tff(c_1190, plain, (![A_1780]: (r2_hidden(A_1780, '#skF_7') | ~r1_tarski(k1_tarski(A_1780), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1178])).
% 4.48/1.80  tff(c_1206, plain, (![A_1814]: (r2_hidden(A_1814, '#skF_7') | '#skF_2'(k1_tarski(A_1814), '#skF_6')=A_1814)), inference(resolution, [status(thm)], [c_96, c_1190])).
% 4.48/1.80  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.48/1.80  tff(c_1271, plain, (![A_1848]: (~r2_hidden(A_1848, '#skF_6') | r1_tarski(k1_tarski(A_1848), '#skF_6') | r2_hidden(A_1848, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1206, c_8])).
% 4.48/1.80  tff(c_1189, plain, (![A_12]: (r2_hidden(A_12, '#skF_7') | ~r1_tarski(k1_tarski(A_12), '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_54, c_1178])).
% 4.48/1.80  tff(c_1327, plain, (![A_1882]: (~r2_hidden(A_1882, '#skF_6') | r2_hidden(A_1882, '#skF_7'))), inference(resolution, [status(thm)], [c_1271, c_1189])).
% 4.48/1.80  tff(c_1444, plain, (![A_2054, B_2055]: (r2_hidden(A_2054, B_2055) | ~r1_tarski('#skF_7', B_2055) | ~r2_hidden(A_2054, '#skF_6'))), inference(resolution, [status(thm)], [c_1327, c_6])).
% 4.48/1.80  tff(c_1461, plain, (![B_2055]: (r2_hidden('#skF_1'('#skF_6'), B_2055) | ~r1_tarski('#skF_7', B_2055) | v1_xboole_0('#skF_6'))), inference(resolution, [status(thm)], [c_4, c_1444])).
% 4.48/1.80  tff(c_1470, plain, (![B_2089]: (r2_hidden('#skF_1'('#skF_6'), B_2089) | ~r1_tarski('#skF_7', B_2089))), inference(negUnitSimplification, [status(thm)], [c_46, c_1461])).
% 4.48/1.80  tff(c_1504, plain, (![A_12]: (A_12='#skF_1'('#skF_6') | ~r1_tarski('#skF_7', k1_tarski(A_12)))), inference(resolution, [status(thm)], [c_1470, c_18])).
% 4.48/1.80  tff(c_2474, plain, ('#skF_1'('#skF_7')='#skF_1'('#skF_6') | ~r1_tarski('#skF_7', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2415, c_1504])).
% 4.48/1.80  tff(c_2574, plain, ('#skF_1'('#skF_7')='#skF_1'('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2474])).
% 4.48/1.80  tff(c_2506, plain, (![B_34]: ('#skF_2'(k1_tarski('#skF_1'('#skF_7')), B_34)='#skF_1'('#skF_7') | r1_tarski('#skF_7', B_34))), inference(superposition, [status(thm), theory('equality')], [c_2415, c_96])).
% 4.48/1.80  tff(c_2578, plain, (![B_34]: ('#skF_2'('#skF_7', B_34)='#skF_1'('#skF_7') | r1_tarski('#skF_7', B_34))), inference(demodulation, [status(thm), theory('equality')], [c_2415, c_2506])).
% 4.48/1.80  tff(c_3259, plain, (![B_3428]: ('#skF_2'('#skF_7', B_3428)='#skF_1'('#skF_6') | r1_tarski('#skF_7', B_3428))), inference(demodulation, [status(thm), theory('equality')], [c_2574, c_2578])).
% 4.48/1.80  tff(c_3337, plain, ('#skF_1'('#skF_6')='#skF_2'('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_3259, c_114])).
% 4.48/1.80  tff(c_3366, plain, (v1_xboole_0('#skF_6') | r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3337, c_4])).
% 4.48/1.80  tff(c_3375, plain, (r2_hidden('#skF_2'('#skF_7', '#skF_6'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_3366])).
% 4.48/1.80  tff(c_3635, plain, (r1_tarski('#skF_7', '#skF_6')), inference(resolution, [status(thm)], [c_3375, c_8])).
% 4.48/1.80  tff(c_3650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_114, c_3635])).
% 4.48/1.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.80  
% 4.48/1.80  Inference rules
% 4.48/1.80  ----------------------
% 4.48/1.80  #Ref     : 0
% 4.48/1.80  #Sup     : 610
% 4.48/1.80  #Fact    : 4
% 4.48/1.80  #Define  : 0
% 4.48/1.80  #Split   : 7
% 4.48/1.80  #Chain   : 0
% 4.48/1.80  #Close   : 0
% 4.48/1.80  
% 4.48/1.80  Ordering : KBO
% 4.48/1.80  
% 4.48/1.80  Simplification rules
% 4.48/1.80  ----------------------
% 4.48/1.80  #Subsume      : 145
% 4.48/1.80  #Demod        : 164
% 4.48/1.80  #Tautology    : 166
% 4.48/1.80  #SimpNegUnit  : 85
% 4.48/1.80  #BackRed      : 21
% 4.48/1.80  
% 4.48/1.80  #Partial instantiations: 2163
% 4.48/1.80  #Strategies tried      : 1
% 4.48/1.80  
% 4.48/1.80  Timing (in seconds)
% 4.48/1.80  ----------------------
% 4.48/1.80  Preprocessing        : 0.30
% 4.48/1.80  Parsing              : 0.15
% 4.48/1.80  CNF conversion       : 0.02
% 4.48/1.80  Main loop            : 0.73
% 4.48/1.80  Inferencing          : 0.33
% 4.48/1.80  Reduction            : 0.17
% 4.48/1.80  Demodulation         : 0.11
% 4.48/1.80  BG Simplification    : 0.03
% 4.48/1.80  Subsumption          : 0.15
% 4.48/1.80  Abstraction          : 0.03
% 4.48/1.80  MUC search           : 0.00
% 4.48/1.80  Cooper               : 0.00
% 4.48/1.80  Total                : 1.06
% 4.48/1.80  Index Insertion      : 0.00
% 4.48/1.80  Index Deletion       : 0.00
% 4.48/1.80  Index Matching       : 0.00
% 4.48/1.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
