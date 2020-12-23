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
% DateTime   : Thu Dec  3 10:24:21 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 443 expanded)
%              Number of leaves         :   46 ( 166 expanded)
%              Depth                    :   15
%              Number of atoms          :  193 (1383 expanded)
%              Number of equality atoms :    8 ( 144 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff(v4_pre_topc,type,(
    v4_pre_topc: ( $i * $i ) > $o )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_160,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,u1_struct_0(A))
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A))))
               => ~ ( ! [D] :
                        ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                       => ( r2_hidden(D,C)
                        <=> ( v3_pre_topc(D,A)
                            & v4_pre_topc(D,A)
                            & r2_hidden(B,D) ) ) )
                    & C = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

tff(f_112,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_108,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_120,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v4_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_132,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_104,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_76,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_62,plain,(
    ! [A_60] :
      ( l1_struct_0(A_60)
      | ~ l1_pre_topc(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_80,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_121,plain,(
    ! [A_84] :
      ( u1_struct_0(A_84) = k2_struct_0(A_84)
      | ~ l1_struct_0(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_126,plain,(
    ! [A_85] :
      ( u1_struct_0(A_85) = k2_struct_0(A_85)
      | ~ l1_pre_topc(A_85) ) ),
    inference(resolution,[status(thm)],[c_62,c_121])).

tff(c_130,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_126])).

tff(c_160,plain,(
    ! [A_93] :
      ( ~ v1_xboole_0(u1_struct_0(A_93))
      | ~ l1_struct_0(A_93)
      | v2_struct_0(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_163,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_160])).

tff(c_164,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_3'))
    | ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_163])).

tff(c_165,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_164])).

tff(c_168,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_165])).

tff(c_172,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_168])).

tff(c_173,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_164])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_12,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_93,plain,(
    ! [A_6] : r1_tarski('#skF_5',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_12])).

tff(c_78,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_66,plain,(
    ! [A_62] :
      ( v4_pre_topc(k2_struct_0(A_62),A_62)
      | ~ l1_pre_topc(A_62)
      | ~ v2_pre_topc(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_131,plain,(
    m1_subset_1('#skF_4',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_74])).

tff(c_42,plain,(
    ! [B_41,A_40] :
      ( r2_hidden(B_41,A_40)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_68,plain,(
    ! [A_63] :
      ( v3_pre_topc(k2_struct_0(A_63),A_63)
      | ~ l1_pre_topc(A_63)
      | ~ v2_pre_topc(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_44,plain,(
    ! [B_41,A_40] :
      ( m1_subset_1(B_41,A_40)
      | ~ v1_xboole_0(B_41)
      | ~ v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_86,plain,(
    ! [D_75] :
      ( v4_pre_topc(D_75,'#skF_3')
      | ~ r2_hidden(D_75,'#skF_5')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_148,plain,(
    ! [D_92] :
      ( v4_pre_topc(D_92,'#skF_3')
      | ~ r2_hidden(D_92,'#skF_5')
      | ~ m1_subset_1(D_92,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_86])).

tff(c_157,plain,(
    ! [B_41] :
      ( v4_pre_topc(B_41,'#skF_3')
      | ~ r2_hidden(B_41,'#skF_5')
      | ~ v1_xboole_0(B_41)
      | ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_44,c_148])).

tff(c_1510,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_30,plain,(
    ! [C_39,A_35] :
      ( r2_hidden(C_39,k1_zfmisc_1(A_35))
      | ~ r1_tarski(C_39,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1354,plain,(
    ! [B_259,A_260] :
      ( m1_subset_1(B_259,A_260)
      | ~ r2_hidden(B_259,A_260)
      | v1_xboole_0(A_260) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1457,plain,(
    ! [C_282,A_283] :
      ( m1_subset_1(C_282,k1_zfmisc_1(A_283))
      | v1_xboole_0(k1_zfmisc_1(A_283))
      | ~ r1_tarski(C_282,A_283) ) ),
    inference(resolution,[status(thm)],[c_30,c_1354])).

tff(c_88,plain,(
    ! [D_75] :
      ( v3_pre_topc(D_75,'#skF_3')
      | ~ r2_hidden(D_75,'#skF_5')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1307,plain,(
    ! [D_75] :
      ( v3_pre_topc(D_75,'#skF_3')
      | ~ r2_hidden(D_75,'#skF_5')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_88])).

tff(c_1494,plain,(
    ! [C_282] :
      ( v3_pre_topc(C_282,'#skF_3')
      | ~ r2_hidden(C_282,'#skF_5')
      | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ r1_tarski(C_282,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1457,c_1307])).

tff(c_1580,plain,(
    ! [C_300] :
      ( v3_pre_topc(C_300,'#skF_3')
      | ~ r2_hidden(C_300,'#skF_5')
      | ~ r1_tarski(C_300,k2_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1510,c_1494])).

tff(c_1589,plain,
    ( v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_1580])).

tff(c_1592,plain,(
    ~ r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1589])).

tff(c_82,plain,(
    ! [D_75] :
      ( r2_hidden(D_75,'#skF_5')
      | ~ r2_hidden('#skF_4',D_75)
      | ~ v4_pre_topc(D_75,'#skF_3')
      | ~ v3_pre_topc(D_75,'#skF_3')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(u1_struct_0('#skF_3'))) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1402,plain,(
    ! [D_75] :
      ( r2_hidden(D_75,'#skF_5')
      | ~ r2_hidden('#skF_4',D_75)
      | ~ v4_pre_topc(D_75,'#skF_3')
      | ~ v3_pre_topc(D_75,'#skF_3')
      | ~ m1_subset_1(D_75,k1_zfmisc_1(k2_struct_0('#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_130,c_82])).

tff(c_1491,plain,(
    ! [C_282] :
      ( r2_hidden(C_282,'#skF_5')
      | ~ r2_hidden('#skF_4',C_282)
      | ~ v4_pre_topc(C_282,'#skF_3')
      | ~ v3_pre_topc(C_282,'#skF_3')
      | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ r1_tarski(C_282,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_1457,c_1402])).

tff(c_2616,plain,(
    ! [C_380] :
      ( r2_hidden(C_380,'#skF_5')
      | ~ r2_hidden('#skF_4',C_380)
      | ~ v4_pre_topc(C_380,'#skF_3')
      | ~ v3_pre_topc(C_380,'#skF_3')
      | ~ r1_tarski(C_380,k2_struct_0('#skF_3')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1510,c_1491])).

tff(c_2628,plain,
    ( r2_hidden(k2_struct_0('#skF_3'),'#skF_5')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_2616])).

tff(c_2637,plain,
    ( ~ r2_hidden('#skF_4',k2_struct_0('#skF_3'))
    | ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1592,c_2628])).

tff(c_2838,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2637])).

tff(c_2841,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_2838])).

tff(c_2845,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2841])).

tff(c_2846,plain,
    ( ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3')
    | ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_2637])).

tff(c_2956,plain,(
    ~ r2_hidden('#skF_4',k2_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2846])).

tff(c_2962,plain,
    ( ~ m1_subset_1('#skF_4',k2_struct_0('#skF_3'))
    | v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_42,c_2956])).

tff(c_2968,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_2962])).

tff(c_2970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_2968])).

tff(c_2971,plain,(
    ~ v4_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2846])).

tff(c_2994,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_2971])).

tff(c_2998,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_2994])).

tff(c_3000,plain,(
    r2_hidden(k2_struct_0('#skF_3'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_1589])).

tff(c_58,plain,(
    ! [B_58,A_57] :
      ( ~ r1_tarski(B_58,A_57)
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3012,plain,(
    ~ r1_tarski('#skF_5',k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3000,c_58])).

tff(c_3025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_3012])).

tff(c_3027,plain,(
    v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_1388,plain,(
    ! [A_267,C_268,B_269] :
      ( m1_subset_1(A_267,C_268)
      | ~ m1_subset_1(B_269,k1_zfmisc_1(C_268))
      | ~ r2_hidden(A_267,B_269) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1498,plain,(
    ! [A_284,C_285,B_286] :
      ( m1_subset_1(A_284,C_285)
      | ~ r2_hidden(A_284,B_286)
      | ~ v1_xboole_0(B_286)
      | ~ v1_xboole_0(k1_zfmisc_1(C_285)) ) ),
    inference(resolution,[status(thm)],[c_44,c_1388])).

tff(c_3080,plain,(
    ! [C_400,C_401,A_402] :
      ( m1_subset_1(C_400,C_401)
      | ~ v1_xboole_0(k1_zfmisc_1(A_402))
      | ~ v1_xboole_0(k1_zfmisc_1(C_401))
      | ~ r1_tarski(C_400,A_402) ) ),
    inference(resolution,[status(thm)],[c_30,c_1498])).

tff(c_3087,plain,(
    ! [C_403,C_404] :
      ( m1_subset_1(C_403,C_404)
      | ~ v1_xboole_0(k1_zfmisc_1(C_404))
      | ~ r1_tarski(C_403,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3027,c_3080])).

tff(c_3094,plain,(
    ! [C_405] :
      ( m1_subset_1(C_405,k2_struct_0('#skF_3'))
      | ~ r1_tarski(C_405,k2_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_3027,c_3087])).

tff(c_3103,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_6,c_3094])).

tff(c_1281,plain,(
    ! [B_249,A_250] :
      ( r2_hidden(B_249,A_250)
      | ~ m1_subset_1(B_249,A_250)
      | v1_xboole_0(A_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1363,plain,(
    ! [A_261,B_262] :
      ( ~ r1_tarski(A_261,B_262)
      | ~ m1_subset_1(B_262,A_261)
      | v1_xboole_0(A_261) ) ),
    inference(resolution,[status(thm)],[c_1281,c_58])).

tff(c_1370,plain,(
    ! [B_2] :
      ( ~ m1_subset_1(B_2,B_2)
      | v1_xboole_0(B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_1363])).

tff(c_3112,plain,(
    v1_xboole_0(k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_3103,c_1370])).

tff(c_3119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_173,c_3112])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/1.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.94  
% 5.00/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.94  %$ v4_pre_topc > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > u1_struct_0 > k2_struct_0 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 5.00/1.94  
% 5.00/1.94  %Foreground sorts:
% 5.00/1.94  
% 5.00/1.94  
% 5.00/1.94  %Background operators:
% 5.00/1.94  
% 5.00/1.94  
% 5.00/1.94  %Foreground operators:
% 5.00/1.94  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.00/1.94  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.00/1.94  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/1.94  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.00/1.94  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.00/1.94  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.00/1.94  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.00/1.94  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.00/1.94  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.00/1.94  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/1.94  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.00/1.94  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.00/1.94  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.00/1.94  tff('#skF_5', type, '#skF_5': $i).
% 5.00/1.94  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.00/1.94  tff('#skF_3', type, '#skF_3': $i).
% 5.00/1.94  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.94  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.00/1.94  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.00/1.94  tff(v4_pre_topc, type, v4_pre_topc: ($i * $i) > $o).
% 5.00/1.94  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.94  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/1.94  tff('#skF_4', type, '#skF_4': $i).
% 5.00/1.94  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/1.94  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 5.00/1.94  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.00/1.94  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/1.94  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.00/1.94  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.00/1.94  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.00/1.94  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.00/1.94  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.00/1.94  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.00/1.94  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.00/1.94  
% 5.00/1.96  tff(f_160, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) => ~((![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) => (r2_hidden(D, C) <=> ((v3_pre_topc(D, A) & v4_pre_topc(D, A)) & r2_hidden(B, D))))) & (C = k1_xboole_0)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_connsp_2)).
% 5.00/1.96  tff(f_112, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.00/1.96  tff(f_108, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.00/1.96  tff(f_120, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.00/1.96  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.00/1.96  tff(f_37, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.00/1.96  tff(f_126, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v4_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_pre_topc)).
% 5.00/1.96  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 5.00/1.96  tff(f_132, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.00/1.96  tff(f_58, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 5.00/1.96  tff(f_104, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 5.00/1.96  tff(f_99, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.00/1.96  tff(c_76, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.00/1.96  tff(c_62, plain, (![A_60]: (l1_struct_0(A_60) | ~l1_pre_topc(A_60))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.00/1.96  tff(c_80, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.00/1.96  tff(c_121, plain, (![A_84]: (u1_struct_0(A_84)=k2_struct_0(A_84) | ~l1_struct_0(A_84))), inference(cnfTransformation, [status(thm)], [f_108])).
% 5.00/1.96  tff(c_126, plain, (![A_85]: (u1_struct_0(A_85)=k2_struct_0(A_85) | ~l1_pre_topc(A_85))), inference(resolution, [status(thm)], [c_62, c_121])).
% 5.00/1.96  tff(c_130, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_76, c_126])).
% 5.00/1.96  tff(c_160, plain, (![A_93]: (~v1_xboole_0(u1_struct_0(A_93)) | ~l1_struct_0(A_93) | v2_struct_0(A_93))), inference(cnfTransformation, [status(thm)], [f_120])).
% 5.00/1.96  tff(c_163, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_130, c_160])).
% 5.00/1.96  tff(c_164, plain, (~v1_xboole_0(k2_struct_0('#skF_3')) | ~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_80, c_163])).
% 5.00/1.96  tff(c_165, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_164])).
% 5.00/1.96  tff(c_168, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_165])).
% 5.00/1.96  tff(c_172, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_168])).
% 5.00/1.96  tff(c_173, plain, (~v1_xboole_0(k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_164])).
% 5.00/1.96  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.00/1.96  tff(c_70, plain, (k1_xboole_0='#skF_5'), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.00/1.96  tff(c_12, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.00/1.96  tff(c_93, plain, (![A_6]: (r1_tarski('#skF_5', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_12])).
% 5.00/1.96  tff(c_78, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.00/1.96  tff(c_66, plain, (![A_62]: (v4_pre_topc(k2_struct_0(A_62), A_62) | ~l1_pre_topc(A_62) | ~v2_pre_topc(A_62))), inference(cnfTransformation, [status(thm)], [f_126])).
% 5.00/1.96  tff(c_74, plain, (m1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.00/1.96  tff(c_131, plain, (m1_subset_1('#skF_4', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_74])).
% 5.00/1.96  tff(c_42, plain, (![B_41, A_40]: (r2_hidden(B_41, A_40) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.00/1.96  tff(c_68, plain, (![A_63]: (v3_pre_topc(k2_struct_0(A_63), A_63) | ~l1_pre_topc(A_63) | ~v2_pre_topc(A_63))), inference(cnfTransformation, [status(thm)], [f_132])).
% 5.00/1.96  tff(c_44, plain, (![B_41, A_40]: (m1_subset_1(B_41, A_40) | ~v1_xboole_0(B_41) | ~v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.00/1.96  tff(c_86, plain, (![D_75]: (v4_pre_topc(D_75, '#skF_3') | ~r2_hidden(D_75, '#skF_5') | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.00/1.96  tff(c_148, plain, (![D_92]: (v4_pre_topc(D_92, '#skF_3') | ~r2_hidden(D_92, '#skF_5') | ~m1_subset_1(D_92, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_86])).
% 5.00/1.96  tff(c_157, plain, (![B_41]: (v4_pre_topc(B_41, '#skF_3') | ~r2_hidden(B_41, '#skF_5') | ~v1_xboole_0(B_41) | ~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(resolution, [status(thm)], [c_44, c_148])).
% 5.00/1.96  tff(c_1510, plain, (~v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitLeft, [status(thm)], [c_157])).
% 5.00/1.96  tff(c_30, plain, (![C_39, A_35]: (r2_hidden(C_39, k1_zfmisc_1(A_35)) | ~r1_tarski(C_39, A_35))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.00/1.96  tff(c_1354, plain, (![B_259, A_260]: (m1_subset_1(B_259, A_260) | ~r2_hidden(B_259, A_260) | v1_xboole_0(A_260))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.00/1.96  tff(c_1457, plain, (![C_282, A_283]: (m1_subset_1(C_282, k1_zfmisc_1(A_283)) | v1_xboole_0(k1_zfmisc_1(A_283)) | ~r1_tarski(C_282, A_283))), inference(resolution, [status(thm)], [c_30, c_1354])).
% 5.00/1.96  tff(c_88, plain, (![D_75]: (v3_pre_topc(D_75, '#skF_3') | ~r2_hidden(D_75, '#skF_5') | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.00/1.96  tff(c_1307, plain, (![D_75]: (v3_pre_topc(D_75, '#skF_3') | ~r2_hidden(D_75, '#skF_5') | ~m1_subset_1(D_75, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_88])).
% 5.00/1.96  tff(c_1494, plain, (![C_282]: (v3_pre_topc(C_282, '#skF_3') | ~r2_hidden(C_282, '#skF_5') | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~r1_tarski(C_282, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1457, c_1307])).
% 5.00/1.96  tff(c_1580, plain, (![C_300]: (v3_pre_topc(C_300, '#skF_3') | ~r2_hidden(C_300, '#skF_5') | ~r1_tarski(C_300, k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1510, c_1494])).
% 5.00/1.96  tff(c_1589, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(resolution, [status(thm)], [c_6, c_1580])).
% 5.00/1.96  tff(c_1592, plain, (~r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitLeft, [status(thm)], [c_1589])).
% 5.00/1.96  tff(c_82, plain, (![D_75]: (r2_hidden(D_75, '#skF_5') | ~r2_hidden('#skF_4', D_75) | ~v4_pre_topc(D_75, '#skF_3') | ~v3_pre_topc(D_75, '#skF_3') | ~m1_subset_1(D_75, k1_zfmisc_1(u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 5.00/1.96  tff(c_1402, plain, (![D_75]: (r2_hidden(D_75, '#skF_5') | ~r2_hidden('#skF_4', D_75) | ~v4_pre_topc(D_75, '#skF_3') | ~v3_pre_topc(D_75, '#skF_3') | ~m1_subset_1(D_75, k1_zfmisc_1(k2_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_130, c_82])).
% 5.00/1.96  tff(c_1491, plain, (![C_282]: (r2_hidden(C_282, '#skF_5') | ~r2_hidden('#skF_4', C_282) | ~v4_pre_topc(C_282, '#skF_3') | ~v3_pre_topc(C_282, '#skF_3') | v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~r1_tarski(C_282, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_1457, c_1402])).
% 5.00/1.96  tff(c_2616, plain, (![C_380]: (r2_hidden(C_380, '#skF_5') | ~r2_hidden('#skF_4', C_380) | ~v4_pre_topc(C_380, '#skF_3') | ~v3_pre_topc(C_380, '#skF_3') | ~r1_tarski(C_380, k2_struct_0('#skF_3')))), inference(negUnitSimplification, [status(thm)], [c_1510, c_1491])).
% 5.00/1.96  tff(c_2628, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_2616])).
% 5.00/1.96  tff(c_2637, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3')) | ~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1592, c_2628])).
% 5.00/1.96  tff(c_2838, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_2637])).
% 5.00/1.96  tff(c_2841, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_68, c_2838])).
% 5.00/1.96  tff(c_2845, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2841])).
% 5.00/1.96  tff(c_2846, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3') | ~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_2637])).
% 5.00/1.96  tff(c_2956, plain, (~r2_hidden('#skF_4', k2_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_2846])).
% 5.00/1.96  tff(c_2962, plain, (~m1_subset_1('#skF_4', k2_struct_0('#skF_3')) | v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_42, c_2956])).
% 5.00/1.96  tff(c_2968, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_2962])).
% 5.00/1.96  tff(c_2970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_2968])).
% 5.00/1.96  tff(c_2971, plain, (~v4_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_2846])).
% 5.00/1.96  tff(c_2994, plain, (~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_2971])).
% 5.00/1.96  tff(c_2998, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_2994])).
% 5.00/1.96  tff(c_3000, plain, (r2_hidden(k2_struct_0('#skF_3'), '#skF_5')), inference(splitRight, [status(thm)], [c_1589])).
% 5.00/1.96  tff(c_58, plain, (![B_58, A_57]: (~r1_tarski(B_58, A_57) | ~r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_104])).
% 5.00/1.96  tff(c_3012, plain, (~r1_tarski('#skF_5', k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3000, c_58])).
% 5.00/1.96  tff(c_3025, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_3012])).
% 5.00/1.96  tff(c_3027, plain, (v1_xboole_0(k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_157])).
% 5.00/1.96  tff(c_1388, plain, (![A_267, C_268, B_269]: (m1_subset_1(A_267, C_268) | ~m1_subset_1(B_269, k1_zfmisc_1(C_268)) | ~r2_hidden(A_267, B_269))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.00/1.96  tff(c_1498, plain, (![A_284, C_285, B_286]: (m1_subset_1(A_284, C_285) | ~r2_hidden(A_284, B_286) | ~v1_xboole_0(B_286) | ~v1_xboole_0(k1_zfmisc_1(C_285)))), inference(resolution, [status(thm)], [c_44, c_1388])).
% 5.00/1.96  tff(c_3080, plain, (![C_400, C_401, A_402]: (m1_subset_1(C_400, C_401) | ~v1_xboole_0(k1_zfmisc_1(A_402)) | ~v1_xboole_0(k1_zfmisc_1(C_401)) | ~r1_tarski(C_400, A_402))), inference(resolution, [status(thm)], [c_30, c_1498])).
% 5.00/1.96  tff(c_3087, plain, (![C_403, C_404]: (m1_subset_1(C_403, C_404) | ~v1_xboole_0(k1_zfmisc_1(C_404)) | ~r1_tarski(C_403, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3027, c_3080])).
% 5.00/1.96  tff(c_3094, plain, (![C_405]: (m1_subset_1(C_405, k2_struct_0('#skF_3')) | ~r1_tarski(C_405, k2_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_3027, c_3087])).
% 5.00/1.96  tff(c_3103, plain, (m1_subset_1(k2_struct_0('#skF_3'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_6, c_3094])).
% 5.00/1.96  tff(c_1281, plain, (![B_249, A_250]: (r2_hidden(B_249, A_250) | ~m1_subset_1(B_249, A_250) | v1_xboole_0(A_250))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.00/1.96  tff(c_1363, plain, (![A_261, B_262]: (~r1_tarski(A_261, B_262) | ~m1_subset_1(B_262, A_261) | v1_xboole_0(A_261))), inference(resolution, [status(thm)], [c_1281, c_58])).
% 5.00/1.96  tff(c_1370, plain, (![B_2]: (~m1_subset_1(B_2, B_2) | v1_xboole_0(B_2))), inference(resolution, [status(thm)], [c_6, c_1363])).
% 5.00/1.96  tff(c_3112, plain, (v1_xboole_0(k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_3103, c_1370])).
% 5.00/1.96  tff(c_3119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_173, c_3112])).
% 5.00/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/1.96  
% 5.00/1.96  Inference rules
% 5.00/1.96  ----------------------
% 5.00/1.96  #Ref     : 0
% 5.00/1.96  #Sup     : 643
% 5.00/1.96  #Fact    : 2
% 5.00/1.96  #Define  : 0
% 5.00/1.96  #Split   : 18
% 5.00/1.96  #Chain   : 0
% 5.00/1.96  #Close   : 0
% 5.00/1.96  
% 5.00/1.96  Ordering : KBO
% 5.00/1.96  
% 5.00/1.96  Simplification rules
% 5.00/1.96  ----------------------
% 5.00/1.96  #Subsume      : 107
% 5.00/1.96  #Demod        : 151
% 5.00/1.96  #Tautology    : 210
% 5.00/1.96  #SimpNegUnit  : 53
% 5.00/1.96  #BackRed      : 1
% 5.00/1.96  
% 5.00/1.96  #Partial instantiations: 0
% 5.00/1.96  #Strategies tried      : 1
% 5.00/1.96  
% 5.00/1.96  Timing (in seconds)
% 5.00/1.96  ----------------------
% 5.00/1.96  Preprocessing        : 0.39
% 5.00/1.96  Parsing              : 0.20
% 5.00/1.96  CNF conversion       : 0.03
% 5.00/1.96  Main loop            : 0.76
% 5.00/1.96  Inferencing          : 0.27
% 5.00/1.96  Reduction            : 0.22
% 5.00/1.96  Demodulation         : 0.14
% 5.00/1.96  BG Simplification    : 0.04
% 5.00/1.96  Subsumption          : 0.17
% 5.00/1.96  Abstraction          : 0.04
% 5.00/1.96  MUC search           : 0.00
% 5.00/1.96  Cooper               : 0.00
% 5.00/1.96  Total                : 1.18
% 5.00/1.96  Index Insertion      : 0.00
% 5.00/1.96  Index Deletion       : 0.00
% 5.00/1.96  Index Matching       : 0.00
% 5.00/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
