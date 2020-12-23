%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0506+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:24 EST 2020

% Result     : Theorem 12.45s
% Output     : CNFRefutation 12.45s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 702 expanded)
%              Number of leaves         :   28 ( 246 expanded)
%              Depth                    :   21
%              Number of atoms          :  277 (2269 expanded)
%              Number of equality atoms :   13 ( 195 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > k4_tarski > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k7_relat_1(C,A),k7_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( v1_relat_1(C)
         => ( C = k7_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(D,B)
                  & r2_hidden(k4_tarski(D,E),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_relat_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_42,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_26,plain,(
    ! [A_37,B_38] :
      ( v1_relat_1(k7_relat_1(A_37,B_38))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_19083,plain,(
    ! [A_996,B_997] :
      ( r2_hidden(k4_tarski('#skF_5'(A_996,B_997),'#skF_6'(A_996,B_997)),A_996)
      | r1_tarski(A_996,B_997)
      | ~ v1_relat_1(A_996) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_20,B_30] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),B_30)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_19092,plain,(
    ! [A_996] :
      ( r1_tarski(A_996,A_996)
      | ~ v1_relat_1(A_996) ) ),
    inference(resolution,[status(thm)],[c_19083,c_22])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( m1_subset_1(A_41,k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_51,plain,(
    ! [C_57,B_58,A_59] :
      ( ~ v1_xboole_0(C_57)
      | ~ m1_subset_1(B_58,k1_zfmisc_1(C_57))
      | ~ r2_hidden(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [B_42,A_59,A_41] :
      ( ~ v1_xboole_0(B_42)
      | ~ r2_hidden(A_59,A_41)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_19110,plain,(
    ! [B_1003,A_1004,B_1005] :
      ( ~ v1_xboole_0(B_1003)
      | ~ r1_tarski(A_1004,B_1003)
      | r1_tarski(A_1004,B_1005)
      | ~ v1_relat_1(A_1004) ) ),
    inference(resolution,[status(thm)],[c_19083,c_54])).

tff(c_19130,plain,(
    ! [A_1010,B_1011] :
      ( ~ v1_xboole_0(A_1010)
      | r1_tarski(A_1010,B_1011)
      | ~ v1_relat_1(A_1010) ) ),
    inference(resolution,[status(thm)],[c_19092,c_19110])).

tff(c_38,plain,(
    ~ r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_19143,plain,
    ( ~ v1_xboole_0(k7_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_19130,c_38])).

tff(c_19144,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_19143])).

tff(c_19147,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_19144])).

tff(c_19151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_19147])).

tff(c_19153,plain,(
    v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_19143])).

tff(c_40,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,B_40)
      | v1_xboole_0(B_40)
      | ~ m1_subset_1(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,(
    ! [B_60,A_61,A_62] :
      ( ~ v1_xboole_0(B_60)
      | ~ r2_hidden(A_61,A_62)
      | ~ r1_tarski(A_62,B_60) ) ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_67,plain,(
    ! [B_69,B_70,A_71] :
      ( ~ v1_xboole_0(B_69)
      | ~ r1_tarski(B_70,B_69)
      | v1_xboole_0(B_70)
      | ~ m1_subset_1(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_70,plain,(
    ! [A_71] :
      ( ~ v1_xboole_0('#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_71,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_71,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_83,plain,(
    ! [A_77,B_78] :
      ( r2_hidden(k4_tarski('#skF_5'(A_77,B_78),'#skF_6'(A_77,B_78)),A_77)
      | r1_tarski(A_77,B_78)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(resolution,[status(thm)],[c_83,c_22])).

tff(c_110,plain,(
    ! [B_84,A_85,B_86] :
      ( ~ v1_xboole_0(B_84)
      | ~ r1_tarski(A_85,B_84)
      | r1_tarski(A_85,B_86)
      | ~ v1_relat_1(A_85) ) ),
    inference(resolution,[status(thm)],[c_83,c_54])).

tff(c_117,plain,(
    ! [A_87,B_88] :
      ( ~ v1_xboole_0(A_87)
      | r1_tarski(A_87,B_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_92,c_110])).

tff(c_130,plain,
    ( ~ v1_xboole_0(k7_relat_1('#skF_9','#skF_7'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_117,c_38])).

tff(c_131,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_134,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_134])).

tff(c_140,plain,(
    v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_399,plain,(
    ! [A_150,B_151,C_152] :
      ( r2_hidden(k4_tarski('#skF_1'(A_150,B_151,C_152),'#skF_2'(A_150,B_151,C_152)),A_150)
      | r2_hidden(k4_tarski('#skF_3'(A_150,B_151,C_152),'#skF_4'(A_150,B_151,C_152)),C_152)
      | k7_relat_1(A_150,B_151) = C_152
      | ~ v1_relat_1(C_152)
      | ~ v1_relat_1(A_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_1,B_12,C_13] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_12,C_13),'#skF_2'(A_1,B_12,C_13)),C_13)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_12,C_13),'#skF_4'(A_1,B_12,C_13)),C_13)
      | k7_relat_1(A_1,B_12) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_447,plain,(
    ! [A_156,B_157] :
      ( r2_hidden(k4_tarski('#skF_3'(A_156,B_157,A_156),'#skF_4'(A_156,B_157,A_156)),A_156)
      | k7_relat_1(A_156,B_157) = A_156
      | ~ v1_relat_1(A_156) ) ),
    inference(resolution,[status(thm)],[c_399,c_8])).

tff(c_18,plain,(
    ! [D_18,B_12,E_19,A_1] :
      ( r2_hidden(D_18,B_12)
      | ~ r2_hidden(k4_tarski(D_18,E_19),k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4661,plain,(
    ! [A_549,B_550,B_551] :
      ( r2_hidden('#skF_3'(k7_relat_1(A_549,B_550),B_551,k7_relat_1(A_549,B_550)),B_550)
      | ~ v1_relat_1(A_549)
      | k7_relat_1(k7_relat_1(A_549,B_550),B_551) = k7_relat_1(A_549,B_550)
      | ~ v1_relat_1(k7_relat_1(A_549,B_550)) ) ),
    inference(resolution,[status(thm)],[c_447,c_18])).

tff(c_432,plain,(
    ! [A_150,B_151] :
      ( r2_hidden(k4_tarski('#skF_3'(A_150,B_151,A_150),'#skF_4'(A_150,B_151,A_150)),A_150)
      | k7_relat_1(A_150,B_151) = A_150
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_399,c_8])).

tff(c_595,plain,(
    ! [A_186,B_187,C_188] :
      ( r2_hidden(k4_tarski('#skF_1'(A_186,B_187,C_188),'#skF_2'(A_186,B_187,C_188)),A_186)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_186,B_187,C_188),'#skF_4'(A_186,B_187,C_188)),A_186)
      | ~ r2_hidden('#skF_3'(A_186,B_187,C_188),B_187)
      | k7_relat_1(A_186,B_187) = C_188
      | ~ v1_relat_1(C_188)
      | ~ v1_relat_1(A_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [A_1,B_12,C_13] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_12,C_13),'#skF_2'(A_1,B_12,C_13)),C_13)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_12,C_13),'#skF_4'(A_1,B_12,C_13)),A_1)
      | ~ r2_hidden('#skF_3'(A_1,B_12,C_13),B_12)
      | k7_relat_1(A_1,B_12) = C_13
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1004,plain,(
    ! [A_244,B_245] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_244,B_245,A_244),'#skF_4'(A_244,B_245,A_244)),A_244)
      | ~ r2_hidden('#skF_3'(A_244,B_245,A_244),B_245)
      | k7_relat_1(A_244,B_245) = A_244
      | ~ v1_relat_1(A_244) ) ),
    inference(resolution,[status(thm)],[c_595,c_2])).

tff(c_1027,plain,(
    ! [A_150,B_151] :
      ( ~ r2_hidden('#skF_3'(A_150,B_151,A_150),B_151)
      | k7_relat_1(A_150,B_151) = A_150
      | ~ v1_relat_1(A_150) ) ),
    inference(resolution,[status(thm)],[c_432,c_1004])).

tff(c_4731,plain,(
    ! [A_556,B_557] :
      ( ~ v1_relat_1(A_556)
      | k7_relat_1(k7_relat_1(A_556,B_557),B_557) = k7_relat_1(A_556,B_557)
      | ~ v1_relat_1(k7_relat_1(A_556,B_557)) ) ),
    inference(resolution,[status(thm)],[c_4661,c_1027])).

tff(c_4733,plain,
    ( ~ v1_relat_1('#skF_9')
    | k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7') = k7_relat_1('#skF_9','#skF_7') ),
    inference(resolution,[status(thm)],[c_140,c_4731])).

tff(c_4738,plain,(
    k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7') = k7_relat_1('#skF_9','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4733])).

tff(c_24,plain,(
    ! [A_20,B_30] :
      ( r2_hidden(k4_tarski('#skF_5'(A_20,B_30),'#skF_6'(A_20,B_30)),A_20)
      | r1_tarski(A_20,B_30)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141,plain,(
    ! [D_89,B_90,E_91,A_92] :
      ( r2_hidden(D_89,B_90)
      | ~ r2_hidden(k4_tarski(D_89,E_91),k7_relat_1(A_92,B_90))
      | ~ v1_relat_1(k7_relat_1(A_92,B_90))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_232,plain,(
    ! [A_113,B_114,B_115] :
      ( r2_hidden('#skF_5'(k7_relat_1(A_113,B_114),B_115),B_114)
      | ~ v1_relat_1(A_113)
      | r1_tarski(k7_relat_1(A_113,B_114),B_115)
      | ~ v1_relat_1(k7_relat_1(A_113,B_114)) ) ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_59,plain,(
    ! [A_63,C_64,B_65] :
      ( m1_subset_1(A_63,C_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(C_64))
      | ~ r2_hidden(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    ! [A_63,B_42,A_41] :
      ( m1_subset_1(A_63,B_42)
      | ~ r2_hidden(A_63,A_41)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_237,plain,(
    ! [A_113,B_114,B_115,B_42] :
      ( m1_subset_1('#skF_5'(k7_relat_1(A_113,B_114),B_115),B_42)
      | ~ r1_tarski(B_114,B_42)
      | ~ v1_relat_1(A_113)
      | r1_tarski(k7_relat_1(A_113,B_114),B_115)
      | ~ v1_relat_1(k7_relat_1(A_113,B_114)) ) ),
    inference(resolution,[status(thm)],[c_232,c_62])).

tff(c_4818,plain,(
    ! [B_115,B_42] :
      ( m1_subset_1('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_115),B_42)
      | ~ r1_tarski('#skF_7',B_42)
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | r1_tarski(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7'),B_115)
      | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4738,c_237])).

tff(c_4913,plain,(
    ! [B_115,B_42] :
      ( m1_subset_1('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_115),B_42)
      | ~ r1_tarski('#skF_7',B_42)
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_115) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_4738,c_4738,c_140,c_4818])).

tff(c_149,plain,(
    ! [A_92,B_90,B_30] :
      ( r2_hidden('#skF_5'(k7_relat_1(A_92,B_90),B_30),B_90)
      | ~ v1_relat_1(A_92)
      | r1_tarski(k7_relat_1(A_92,B_90),B_30)
      | ~ v1_relat_1(k7_relat_1(A_92,B_90)) ) ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_239,plain,(
    ! [D_116,E_117,A_118,B_119] :
      ( r2_hidden(k4_tarski(D_116,E_117),k7_relat_1(A_118,B_119))
      | ~ r2_hidden(k4_tarski(D_116,E_117),A_118)
      | ~ r2_hidden(D_116,B_119)
      | ~ v1_relat_1(k7_relat_1(A_118,B_119))
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2527,plain,(
    ! [A_399,A_400,B_401] :
      ( r1_tarski(A_399,k7_relat_1(A_400,B_401))
      | ~ v1_relat_1(A_399)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_399,k7_relat_1(A_400,B_401)),'#skF_6'(A_399,k7_relat_1(A_400,B_401))),A_400)
      | ~ r2_hidden('#skF_5'(A_399,k7_relat_1(A_400,B_401)),B_401)
      | ~ v1_relat_1(k7_relat_1(A_400,B_401))
      | ~ v1_relat_1(A_400) ) ),
    inference(resolution,[status(thm)],[c_239,c_22])).

tff(c_2565,plain,(
    ! [A_402,B_403] :
      ( ~ r2_hidden('#skF_5'(A_402,k7_relat_1(A_402,B_403)),B_403)
      | ~ v1_relat_1(k7_relat_1(A_402,B_403))
      | r1_tarski(A_402,k7_relat_1(A_402,B_403))
      | ~ v1_relat_1(A_402) ) ),
    inference(resolution,[status(thm)],[c_24,c_2527])).

tff(c_2580,plain,(
    ! [A_92,B_90] :
      ( ~ v1_relat_1(k7_relat_1(k7_relat_1(A_92,B_90),B_90))
      | ~ v1_relat_1(A_92)
      | r1_tarski(k7_relat_1(A_92,B_90),k7_relat_1(k7_relat_1(A_92,B_90),B_90))
      | ~ v1_relat_1(k7_relat_1(A_92,B_90)) ) ),
    inference(resolution,[status(thm)],[c_149,c_2565])).

tff(c_4787,plain,
    ( ~ v1_relat_1(k7_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7'),'#skF_7'))
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
    | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7'),'#skF_7'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_9','#skF_7'),'#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4738,c_2580])).

tff(c_4893,plain,(
    r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_4738,c_4738,c_4738,c_140,c_140,c_4738,c_4738,c_4787])).

tff(c_95,plain,(
    ! [C_79,D_80,B_81,A_82] :
      ( r2_hidden(k4_tarski(C_79,D_80),B_81)
      | ~ r2_hidden(k4_tarski(C_79,D_80),A_82)
      | ~ r1_tarski(A_82,B_81)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_167,plain,(
    ! [A_99,B_100,B_101] :
      ( r2_hidden(k4_tarski('#skF_5'(A_99,B_100),'#skF_6'(A_99,B_100)),B_101)
      | ~ r1_tarski(A_99,B_101)
      | r1_tarski(A_99,B_100)
      | ~ v1_relat_1(A_99) ) ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_16,plain,(
    ! [D_18,E_19,A_1,B_12] :
      ( r2_hidden(k4_tarski(D_18,E_19),A_1)
      | ~ r2_hidden(k4_tarski(D_18,E_19),k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(k7_relat_1(A_1,B_12))
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9999,plain,(
    ! [A_728,B_729,A_730,B_731] :
      ( r2_hidden(k4_tarski('#skF_5'(A_728,B_729),'#skF_6'(A_728,B_729)),A_730)
      | ~ v1_relat_1(k7_relat_1(A_730,B_731))
      | ~ v1_relat_1(A_730)
      | ~ r1_tarski(A_728,k7_relat_1(A_730,B_731))
      | r1_tarski(A_728,B_729)
      | ~ v1_relat_1(A_728) ) ),
    inference(resolution,[status(thm)],[c_167,c_16])).

tff(c_10012,plain,(
    ! [B_729] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_729),'#skF_6'(k7_relat_1('#skF_9','#skF_7'),B_729)),'#skF_9')
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_729)
      | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_4893,c_9999])).

tff(c_10282,plain,(
    ! [B_737] :
      ( r2_hidden(k4_tarski('#skF_5'(k7_relat_1('#skF_9','#skF_7'),B_737),'#skF_6'(k7_relat_1('#skF_9','#skF_7'),B_737)),'#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),B_737) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_42,c_10012])).

tff(c_259,plain,(
    ! [A_20,A_118,B_119] :
      ( r1_tarski(A_20,k7_relat_1(A_118,B_119))
      | ~ v1_relat_1(A_20)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_20,k7_relat_1(A_118,B_119)),'#skF_6'(A_20,k7_relat_1(A_118,B_119))),A_118)
      | ~ r2_hidden('#skF_5'(A_20,k7_relat_1(A_118,B_119)),B_119)
      | ~ v1_relat_1(k7_relat_1(A_118,B_119))
      | ~ v1_relat_1(A_118) ) ),
    inference(resolution,[status(thm)],[c_239,c_22])).

tff(c_10297,plain,(
    ! [B_119] :
      ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7'))
      | ~ r2_hidden('#skF_5'(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_119)),B_119)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_119))
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_119)) ) ),
    inference(resolution,[status(thm)],[c_10282,c_259])).

tff(c_11046,plain,(
    ! [B_765] :
      ( ~ r2_hidden('#skF_5'(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_765)),B_765)
      | ~ v1_relat_1(k7_relat_1('#skF_9',B_765))
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_765)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_140,c_10297])).

tff(c_18699,plain,(
    ! [B_983] :
      ( ~ v1_relat_1(k7_relat_1('#skF_9',B_983))
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_983))
      | v1_xboole_0(B_983)
      | ~ m1_subset_1('#skF_5'(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_983)),B_983) ) ),
    inference(resolution,[status(thm)],[c_28,c_11046])).

tff(c_18811,plain,(
    ! [B_989] :
      ( ~ v1_relat_1(k7_relat_1('#skF_9',B_989))
      | v1_xboole_0(B_989)
      | ~ r1_tarski('#skF_7',B_989)
      | r1_tarski(k7_relat_1('#skF_9','#skF_7'),k7_relat_1('#skF_9',B_989)) ) ),
    inference(resolution,[status(thm)],[c_4913,c_18699])).

tff(c_18930,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
    | v1_xboole_0('#skF_8')
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_18811,c_38])).

tff(c_19060,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8'))
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_18930])).

tff(c_19061,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_9','#skF_8')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_19060])).

tff(c_19064,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_19061])).

tff(c_19068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_19064])).

tff(c_19070,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_19120,plain,(
    ! [D_1006,B_1007,E_1008,A_1009] :
      ( r2_hidden(D_1006,B_1007)
      | ~ r2_hidden(k4_tarski(D_1006,E_1008),k7_relat_1(A_1009,B_1007))
      | ~ v1_relat_1(k7_relat_1(A_1009,B_1007))
      | ~ v1_relat_1(A_1009) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_19250,plain,(
    ! [A_1034,B_1035,B_1036] :
      ( r2_hidden('#skF_5'(k7_relat_1(A_1034,B_1035),B_1036),B_1035)
      | ~ v1_relat_1(A_1034)
      | r1_tarski(k7_relat_1(A_1034,B_1035),B_1036)
      | ~ v1_relat_1(k7_relat_1(A_1034,B_1035)) ) ),
    inference(resolution,[status(thm)],[c_24,c_19120])).

tff(c_19257,plain,(
    ! [B_1037,B_1038,A_1039,B_1040] :
      ( ~ v1_xboole_0(B_1037)
      | ~ r1_tarski(B_1038,B_1037)
      | ~ v1_relat_1(A_1039)
      | r1_tarski(k7_relat_1(A_1039,B_1038),B_1040)
      | ~ v1_relat_1(k7_relat_1(A_1039,B_1038)) ) ),
    inference(resolution,[status(thm)],[c_19250,c_54])).

tff(c_19263,plain,(
    ! [A_1039,B_1040] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ v1_relat_1(A_1039)
      | r1_tarski(k7_relat_1(A_1039,'#skF_7'),B_1040)
      | ~ v1_relat_1(k7_relat_1(A_1039,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_40,c_19257])).

tff(c_19269,plain,(
    ! [A_1041,B_1042] :
      ( ~ v1_relat_1(A_1041)
      | r1_tarski(k7_relat_1(A_1041,'#skF_7'),B_1042)
      | ~ v1_relat_1(k7_relat_1(A_1041,'#skF_7')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19070,c_19263])).

tff(c_19287,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k7_relat_1('#skF_9','#skF_7')) ),
    inference(resolution,[status(thm)],[c_19269,c_38])).

tff(c_19298,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_19153,c_42,c_19287])).

%------------------------------------------------------------------------------
