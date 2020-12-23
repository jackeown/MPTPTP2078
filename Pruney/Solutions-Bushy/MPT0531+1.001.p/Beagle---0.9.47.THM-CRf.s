%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0531+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:36:26 EST 2020

% Result     : Theorem 10.44s
% Output     : CNFRefutation 10.70s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 585 expanded)
%              Number of leaves         :   28 ( 207 expanded)
%              Depth                    :   21
%              Number of atoms          :  254 (1846 expanded)
%              Number of equality atoms :   13 ( 152 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k8_relat_1 > k4_tarski > #nlpp > k1_zfmisc_1 > #skF_6 > #skF_1 > #skF_4 > #skF_7 > #skF_2 > #skF_9 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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
         => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t131_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => v1_relat_1(k8_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

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
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( C = k8_relat_1(A,B)
          <=> ! [D,E] :
                ( r2_hidden(k4_tarski(D,E),C)
              <=> ( r2_hidden(E,A)
                  & r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_relat_1)).

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
    ! [A_36,B_37] :
      ( v1_relat_1(k8_relat_1(A_36,B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12990,plain,(
    ! [A_800,B_801] :
      ( r2_hidden(k4_tarski('#skF_5'(A_800,B_801),'#skF_6'(A_800,B_801)),A_800)
      | r1_tarski(A_800,B_801)
      | ~ v1_relat_1(A_800) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_19,B_29] :
      ( ~ r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),B_29)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_12999,plain,(
    ! [A_800] :
      ( r1_tarski(A_800,A_800)
      | ~ v1_relat_1(A_800) ) ),
    inference(resolution,[status(thm)],[c_12990,c_22])).

tff(c_32,plain,(
    ! [A_40,B_41] :
      ( m1_subset_1(A_40,k1_zfmisc_1(B_41))
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_51,plain,(
    ! [C_56,B_57,A_58] :
      ( ~ v1_xboole_0(C_56)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(C_56))
      | ~ r2_hidden(A_58,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [B_41,A_58,A_40] :
      ( ~ v1_xboole_0(B_41)
      | ~ r2_hidden(A_58,A_40)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_13017,plain,(
    ! [B_807,A_808,B_809] :
      ( ~ v1_xboole_0(B_807)
      | ~ r1_tarski(A_808,B_807)
      | r1_tarski(A_808,B_809)
      | ~ v1_relat_1(A_808) ) ),
    inference(resolution,[status(thm)],[c_12990,c_54])).

tff(c_13037,plain,(
    ! [A_814,B_815] :
      ( ~ v1_xboole_0(A_814)
      | r1_tarski(A_814,B_815)
      | ~ v1_relat_1(A_814) ) ),
    inference(resolution,[status(thm)],[c_12999,c_13017])).

tff(c_38,plain,(
    ~ r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1('#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_13050,plain,
    ( ~ v1_xboole_0(k8_relat_1('#skF_7','#skF_9'))
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_13037,c_38])).

tff(c_13051,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_13050])).

tff(c_13054,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_13051])).

tff(c_13058,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_13054])).

tff(c_13060,plain,(
    v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_13050])).

tff(c_40,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_28,plain,(
    ! [A_38,B_39] :
      ( r2_hidden(A_38,B_39)
      | v1_xboole_0(B_39)
      | ~ m1_subset_1(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_55,plain,(
    ! [B_59,A_60,A_61] :
      ( ~ v1_xboole_0(B_59)
      | ~ r2_hidden(A_60,A_61)
      | ~ r1_tarski(A_61,B_59) ) ),
    inference(resolution,[status(thm)],[c_32,c_51])).

tff(c_67,plain,(
    ! [B_68,B_69,A_70] :
      ( ~ v1_xboole_0(B_68)
      | ~ r1_tarski(B_69,B_68)
      | v1_xboole_0(B_69)
      | ~ m1_subset_1(A_70,B_69) ) ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_70,plain,(
    ! [A_70] :
      ( ~ v1_xboole_0('#skF_8')
      | v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_70,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_40,c_67])).

tff(c_71,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_83,plain,(
    ! [A_76,B_77] :
      ( r2_hidden(k4_tarski('#skF_5'(A_76,B_77),'#skF_6'(A_76,B_77)),A_76)
      | r1_tarski(A_76,B_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,(
    ! [A_76] :
      ( r1_tarski(A_76,A_76)
      | ~ v1_relat_1(A_76) ) ),
    inference(resolution,[status(thm)],[c_83,c_22])).

tff(c_110,plain,(
    ! [B_83,A_84,B_85] :
      ( ~ v1_xboole_0(B_83)
      | ~ r1_tarski(A_84,B_83)
      | r1_tarski(A_84,B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(resolution,[status(thm)],[c_83,c_54])).

tff(c_117,plain,(
    ! [A_86,B_87] :
      ( ~ v1_xboole_0(A_86)
      | r1_tarski(A_86,B_87)
      | ~ v1_relat_1(A_86) ) ),
    inference(resolution,[status(thm)],[c_92,c_110])).

tff(c_130,plain,
    ( ~ v1_xboole_0(k8_relat_1('#skF_7','#skF_9'))
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_117,c_38])).

tff(c_131,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_134,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_131])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_134])).

tff(c_140,plain,(
    v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_399,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden(k4_tarski('#skF_1'(A_149,B_150,C_151),'#skF_2'(A_149,B_150,C_151)),B_150)
      | r2_hidden(k4_tarski('#skF_3'(A_149,B_150,C_151),'#skF_4'(A_149,B_150,C_151)),C_151)
      | k8_relat_1(A_149,B_150) = C_151
      | ~ v1_relat_1(C_151)
      | ~ v1_relat_1(B_150) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_1,B_2,C_12] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),C_12)
      | r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),C_12)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_447,plain,(
    ! [A_155,B_156] :
      ( r2_hidden(k4_tarski('#skF_3'(A_155,B_156,B_156),'#skF_4'(A_155,B_156,B_156)),B_156)
      | k8_relat_1(A_155,B_156) = B_156
      | ~ v1_relat_1(B_156) ) ),
    inference(resolution,[status(thm)],[c_399,c_8])).

tff(c_18,plain,(
    ! [E_18,A_1,D_17,B_2] :
      ( r2_hidden(E_18,A_1)
      | ~ r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3710,plain,(
    ! [A_487,A_488,B_489] :
      ( r2_hidden('#skF_4'(A_487,k8_relat_1(A_488,B_489),k8_relat_1(A_488,B_489)),A_488)
      | ~ v1_relat_1(B_489)
      | k8_relat_1(A_487,k8_relat_1(A_488,B_489)) = k8_relat_1(A_488,B_489)
      | ~ v1_relat_1(k8_relat_1(A_488,B_489)) ) ),
    inference(resolution,[status(thm)],[c_447,c_18])).

tff(c_432,plain,(
    ! [A_149,B_150] :
      ( r2_hidden(k4_tarski('#skF_3'(A_149,B_150,B_150),'#skF_4'(A_149,B_150,B_150)),B_150)
      | k8_relat_1(A_149,B_150) = B_150
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_399,c_8])).

tff(c_583,plain,(
    ! [A_186,B_187,C_188] :
      ( r2_hidden(k4_tarski('#skF_1'(A_186,B_187,C_188),'#skF_2'(A_186,B_187,C_188)),B_187)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_186,B_187,C_188),'#skF_4'(A_186,B_187,C_188)),B_187)
      | ~ r2_hidden('#skF_4'(A_186,B_187,C_188),A_186)
      | k8_relat_1(A_186,B_187) = C_188
      | ~ v1_relat_1(C_188)
      | ~ v1_relat_1(B_187) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [A_1,B_2,C_12] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_1,B_2,C_12),'#skF_2'(A_1,B_2,C_12)),C_12)
      | ~ r2_hidden(k4_tarski('#skF_3'(A_1,B_2,C_12),'#skF_4'(A_1,B_2,C_12)),B_2)
      | ~ r2_hidden('#skF_4'(A_1,B_2,C_12),A_1)
      | k8_relat_1(A_1,B_2) = C_12
      | ~ v1_relat_1(C_12)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_993,plain,(
    ! [A_241,B_242] :
      ( ~ r2_hidden(k4_tarski('#skF_3'(A_241,B_242,B_242),'#skF_4'(A_241,B_242,B_242)),B_242)
      | ~ r2_hidden('#skF_4'(A_241,B_242,B_242),A_241)
      | k8_relat_1(A_241,B_242) = B_242
      | ~ v1_relat_1(B_242) ) ),
    inference(resolution,[status(thm)],[c_583,c_2])).

tff(c_1016,plain,(
    ! [A_149,B_150] :
      ( ~ r2_hidden('#skF_4'(A_149,B_150,B_150),A_149)
      | k8_relat_1(A_149,B_150) = B_150
      | ~ v1_relat_1(B_150) ) ),
    inference(resolution,[status(thm)],[c_432,c_993])).

tff(c_3785,plain,(
    ! [B_493,A_494] :
      ( ~ v1_relat_1(B_493)
      | k8_relat_1(A_494,k8_relat_1(A_494,B_493)) = k8_relat_1(A_494,B_493)
      | ~ v1_relat_1(k8_relat_1(A_494,B_493)) ) ),
    inference(resolution,[status(thm)],[c_3710,c_1016])).

tff(c_3787,plain,
    ( ~ v1_relat_1('#skF_9')
    | k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9')) = k8_relat_1('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_140,c_3785])).

tff(c_3792,plain,(
    k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9')) = k8_relat_1('#skF_7','#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_3787])).

tff(c_24,plain,(
    ! [A_19,B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(A_19,B_29),'#skF_6'(A_19,B_29)),A_19)
      | r1_tarski(A_19,B_29)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_141,plain,(
    ! [E_88,A_89,D_90,B_91] :
      ( r2_hidden(E_88,A_89)
      | ~ r2_hidden(k4_tarski(D_90,E_88),k8_relat_1(A_89,B_91))
      | ~ v1_relat_1(k8_relat_1(A_89,B_91))
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_232,plain,(
    ! [A_112,B_113,B_114] :
      ( r2_hidden('#skF_6'(k8_relat_1(A_112,B_113),B_114),A_112)
      | ~ v1_relat_1(B_113)
      | r1_tarski(k8_relat_1(A_112,B_113),B_114)
      | ~ v1_relat_1(k8_relat_1(A_112,B_113)) ) ),
    inference(resolution,[status(thm)],[c_24,c_141])).

tff(c_59,plain,(
    ! [A_62,C_63,B_64] :
      ( m1_subset_1(A_62,C_63)
      | ~ m1_subset_1(B_64,k1_zfmisc_1(C_63))
      | ~ r2_hidden(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_62,plain,(
    ! [A_62,B_41,A_40] :
      ( m1_subset_1(A_62,B_41)
      | ~ r2_hidden(A_62,A_40)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_32,c_59])).

tff(c_237,plain,(
    ! [A_112,B_113,B_114,B_41] :
      ( m1_subset_1('#skF_6'(k8_relat_1(A_112,B_113),B_114),B_41)
      | ~ r1_tarski(A_112,B_41)
      | ~ v1_relat_1(B_113)
      | r1_tarski(k8_relat_1(A_112,B_113),B_114)
      | ~ v1_relat_1(k8_relat_1(A_112,B_113)) ) ),
    inference(resolution,[status(thm)],[c_232,c_62])).

tff(c_3866,plain,(
    ! [B_114,B_41] :
      ( m1_subset_1('#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_114),B_41)
      | ~ r1_tarski('#skF_7',B_41)
      | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9')),B_114)
      | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3792,c_237])).

tff(c_3955,plain,(
    ! [B_114,B_41] :
      ( m1_subset_1('#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_114),B_41)
      | ~ r1_tarski('#skF_7',B_41)
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),B_114) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_3792,c_3792,c_140,c_3866])).

tff(c_157,plain,(
    ! [D_94,E_95,B_96,A_97] :
      ( r2_hidden(k4_tarski(D_94,E_95),B_96)
      | ~ r2_hidden(k4_tarski(D_94,E_95),k8_relat_1(A_97,B_96))
      | ~ v1_relat_1(k8_relat_1(A_97,B_96))
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_165,plain,(
    ! [A_97,B_96,B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1(A_97,B_96),B_29),'#skF_6'(k8_relat_1(A_97,B_96),B_29)),B_96)
      | ~ v1_relat_1(B_96)
      | r1_tarski(k8_relat_1(A_97,B_96),B_29)
      | ~ v1_relat_1(k8_relat_1(A_97,B_96)) ) ),
    inference(resolution,[status(thm)],[c_24,c_157])).

tff(c_3877,plain,(
    ! [B_29] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1('#skF_7','#skF_9'),B_29),'#skF_6'(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9')),B_29)),k8_relat_1('#skF_7','#skF_9'))
      | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9')),B_29)
      | ~ v1_relat_1(k8_relat_1('#skF_7',k8_relat_1('#skF_7','#skF_9'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3792,c_165])).

tff(c_7890,plain,(
    ! [B_631] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1('#skF_7','#skF_9'),B_631),'#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_631)),k8_relat_1('#skF_7','#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),B_631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_3792,c_3792,c_140,c_3792,c_3877])).

tff(c_16,plain,(
    ! [D_17,E_18,B_2,A_1] :
      ( r2_hidden(k4_tarski(D_17,E_18),B_2)
      | ~ r2_hidden(k4_tarski(D_17,E_18),k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(k8_relat_1(A_1,B_2))
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7900,plain,(
    ! [B_631] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1('#skF_7','#skF_9'),B_631),'#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_631)),'#skF_9')
      | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),B_631) ) ),
    inference(resolution,[status(thm)],[c_7890,c_16])).

tff(c_7932,plain,(
    ! [B_632] :
      ( r2_hidden(k4_tarski('#skF_5'(k8_relat_1('#skF_7','#skF_9'),B_632),'#skF_6'(k8_relat_1('#skF_7','#skF_9'),B_632)),'#skF_9')
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),B_632) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_140,c_7900])).

tff(c_239,plain,(
    ! [D_115,E_116,A_117,B_118] :
      ( r2_hidden(k4_tarski(D_115,E_116),k8_relat_1(A_117,B_118))
      | ~ r2_hidden(k4_tarski(D_115,E_116),B_118)
      | ~ r2_hidden(E_116,A_117)
      | ~ v1_relat_1(k8_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_259,plain,(
    ! [A_19,A_117,B_118] :
      ( r1_tarski(A_19,k8_relat_1(A_117,B_118))
      | ~ v1_relat_1(A_19)
      | ~ r2_hidden(k4_tarski('#skF_5'(A_19,k8_relat_1(A_117,B_118)),'#skF_6'(A_19,k8_relat_1(A_117,B_118))),B_118)
      | ~ r2_hidden('#skF_6'(A_19,k8_relat_1(A_117,B_118)),A_117)
      | ~ v1_relat_1(k8_relat_1(A_117,B_118))
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_239,c_22])).

tff(c_7945,plain,(
    ! [A_117] :
      ( ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9'))
      | ~ r2_hidden('#skF_6'(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(A_117,'#skF_9')),A_117)
      | ~ v1_relat_1(k8_relat_1(A_117,'#skF_9'))
      | ~ v1_relat_1('#skF_9')
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(A_117,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_7932,c_259])).

tff(c_8417,plain,(
    ! [A_646] :
      ( ~ r2_hidden('#skF_6'(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(A_646,'#skF_9')),A_646)
      | ~ v1_relat_1(k8_relat_1(A_646,'#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(A_646,'#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_140,c_7945])).

tff(c_12673,plain,(
    ! [B_787] :
      ( ~ v1_relat_1(k8_relat_1(B_787,'#skF_9'))
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(B_787,'#skF_9'))
      | v1_xboole_0(B_787)
      | ~ m1_subset_1('#skF_6'(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(B_787,'#skF_9')),B_787) ) ),
    inference(resolution,[status(thm)],[c_28,c_8417])).

tff(c_12770,plain,(
    ! [B_793] :
      ( ~ v1_relat_1(k8_relat_1(B_793,'#skF_9'))
      | v1_xboole_0(B_793)
      | ~ r1_tarski('#skF_7',B_793)
      | r1_tarski(k8_relat_1('#skF_7','#skF_9'),k8_relat_1(B_793,'#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_3955,c_12673])).

tff(c_12866,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9'))
    | v1_xboole_0('#skF_8')
    | ~ r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_12770,c_38])).

tff(c_12967,plain,
    ( ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9'))
    | v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_12866])).

tff(c_12968,plain,(
    ~ v1_relat_1(k8_relat_1('#skF_8','#skF_9')) ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_12967])).

tff(c_12971,plain,(
    ~ v1_relat_1('#skF_9') ),
    inference(resolution,[status(thm)],[c_26,c_12968])).

tff(c_12975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_12971])).

tff(c_12977,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_13027,plain,(
    ! [E_810,A_811,D_812,B_813] :
      ( r2_hidden(E_810,A_811)
      | ~ r2_hidden(k4_tarski(D_812,E_810),k8_relat_1(A_811,B_813))
      | ~ v1_relat_1(k8_relat_1(A_811,B_813))
      | ~ v1_relat_1(B_813) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_13157,plain,(
    ! [A_838,B_839,B_840] :
      ( r2_hidden('#skF_6'(k8_relat_1(A_838,B_839),B_840),A_838)
      | ~ v1_relat_1(B_839)
      | r1_tarski(k8_relat_1(A_838,B_839),B_840)
      | ~ v1_relat_1(k8_relat_1(A_838,B_839)) ) ),
    inference(resolution,[status(thm)],[c_24,c_13027])).

tff(c_13164,plain,(
    ! [B_841,A_842,B_843,B_844] :
      ( ~ v1_xboole_0(B_841)
      | ~ r1_tarski(A_842,B_841)
      | ~ v1_relat_1(B_843)
      | r1_tarski(k8_relat_1(A_842,B_843),B_844)
      | ~ v1_relat_1(k8_relat_1(A_842,B_843)) ) ),
    inference(resolution,[status(thm)],[c_13157,c_54])).

tff(c_13170,plain,(
    ! [B_843,B_844] :
      ( ~ v1_xboole_0('#skF_8')
      | ~ v1_relat_1(B_843)
      | r1_tarski(k8_relat_1('#skF_7',B_843),B_844)
      | ~ v1_relat_1(k8_relat_1('#skF_7',B_843)) ) ),
    inference(resolution,[status(thm)],[c_40,c_13164])).

tff(c_13176,plain,(
    ! [B_845,B_846] :
      ( ~ v1_relat_1(B_845)
      | r1_tarski(k8_relat_1('#skF_7',B_845),B_846)
      | ~ v1_relat_1(k8_relat_1('#skF_7',B_845)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12977,c_13170])).

tff(c_13194,plain,
    ( ~ v1_relat_1('#skF_9')
    | ~ v1_relat_1(k8_relat_1('#skF_7','#skF_9')) ),
    inference(resolution,[status(thm)],[c_13176,c_38])).

tff(c_13205,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13060,c_42,c_13194])).

%------------------------------------------------------------------------------
