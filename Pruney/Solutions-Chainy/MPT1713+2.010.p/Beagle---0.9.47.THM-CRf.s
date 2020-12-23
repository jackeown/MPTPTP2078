%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:26:30 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 301 expanded)
%              Number of leaves         :   24 ( 115 expanded)
%              Depth                    :   12
%              Number of atoms          :  267 (1265 expanded)
%              Number of equality atoms :    1 (   5 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(r1_tsep_1,type,(
    r1_tsep_1: ( $i * $i ) > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( ( ~ v2_struct_0(B)
              & m1_pre_topc(B,A) )
           => ! [C] :
                ( ( ~ v2_struct_0(C)
                  & m1_pre_topc(C,A) )
               => ( m1_pre_topc(B,C)
                 => ( ~ r1_tsep_1(B,C)
                    & ~ r1_tsep_1(C,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_45,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_69,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => ! [B] :
          ( l1_struct_0(B)
         => ( r1_tsep_1(A,B)
          <=> r1_xboole_0(u1_struct_0(A),u1_struct_0(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_34,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_32,plain,(
    m1_pre_topc('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_26,plain,(
    m1_pre_topc('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_36,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_341,plain,(
    ! [B_68,A_69] :
      ( l1_pre_topc(B_68)
      | ~ m1_pre_topc(B_68,A_69)
      | ~ l1_pre_topc(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_344,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_341])).

tff(c_353,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_344])).

tff(c_10,plain,(
    ! [A_6] :
      ( l1_struct_0(A_6)
      | ~ l1_pre_topc(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_389,plain,(
    ! [B_85,C_86,A_87] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0(C_86))
      | ~ m1_pre_topc(B_85,C_86)
      | ~ m1_pre_topc(C_86,A_87)
      | ~ m1_pre_topc(B_85,A_87)
      | ~ l1_pre_topc(A_87)
      | ~ v2_pre_topc(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_391,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_85,'#skF_2')
      | ~ m1_pre_topc(B_85,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_389])).

tff(c_417,plain,(
    ! [B_90] :
      ( r1_tarski(u1_struct_0(B_90),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_90,'#skF_2')
      | ~ m1_pre_topc(B_90,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_391])).

tff(c_369,plain,(
    ! [A_76,B_77] :
      ( r1_xboole_0(u1_struct_0(A_76),u1_struct_0(B_77))
      | ~ r1_tsep_1(A_76,B_77)
      | ~ l1_struct_0(B_77)
      | ~ l1_struct_0(A_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(C_5,A_3)
      | v1_xboole_0(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_372,plain,(
    ! [C_5,B_77,A_76] :
      ( ~ r1_tarski(C_5,u1_struct_0(B_77))
      | ~ r1_tarski(C_5,u1_struct_0(A_76))
      | v1_xboole_0(C_5)
      | ~ r1_tsep_1(A_76,B_77)
      | ~ l1_struct_0(B_77)
      | ~ l1_struct_0(A_76) ) ),
    inference(resolution,[status(thm)],[c_369,c_8])).

tff(c_426,plain,(
    ! [B_90,A_76] :
      ( ~ r1_tarski(u1_struct_0(B_90),u1_struct_0(A_76))
      | v1_xboole_0(u1_struct_0(B_90))
      | ~ r1_tsep_1(A_76,'#skF_2')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_76)
      | ~ m1_pre_topc(B_90,'#skF_2')
      | ~ m1_pre_topc(B_90,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_417,c_372])).

tff(c_553,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_426])).

tff(c_556,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_553])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_556])).

tff(c_562,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_426])).

tff(c_45,plain,(
    ! [B_27,A_28] :
      ( l1_pre_topc(B_27)
      | ~ m1_pre_topc(B_27,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_48,plain,
    ( l1_pre_topc('#skF_2')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_45])).

tff(c_57,plain,(
    l1_pre_topc('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_48])).

tff(c_94,plain,(
    ! [B_45,C_46,A_47] :
      ( r1_tarski(u1_struct_0(B_45),u1_struct_0(C_46))
      | ~ m1_pre_topc(B_45,C_46)
      | ~ m1_pre_topc(C_46,A_47)
      | ~ m1_pre_topc(B_45,A_47)
      | ~ l1_pre_topc(A_47)
      | ~ v2_pre_topc(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_96,plain,(
    ! [B_45] :
      ( r1_tarski(u1_struct_0(B_45),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_45,'#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_32,c_94])).

tff(c_166,plain,(
    ! [B_53] :
      ( r1_tarski(u1_struct_0(B_53),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_53,'#skF_2')
      | ~ m1_pre_topc(B_53,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_96])).

tff(c_73,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(u1_struct_0(A_35),u1_struct_0(B_36))
      | ~ r1_tsep_1(A_35,B_36)
      | ~ l1_struct_0(B_36)
      | ~ l1_struct_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76,plain,(
    ! [C_5,B_36,A_35] :
      ( ~ r1_tarski(C_5,u1_struct_0(B_36))
      | ~ r1_tarski(C_5,u1_struct_0(A_35))
      | v1_xboole_0(C_5)
      | ~ r1_tsep_1(A_35,B_36)
      | ~ l1_struct_0(B_36)
      | ~ l1_struct_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_73,c_8])).

tff(c_178,plain,(
    ! [B_53,A_35] :
      ( ~ r1_tarski(u1_struct_0(B_53),u1_struct_0(A_35))
      | v1_xboole_0(u1_struct_0(B_53))
      | ~ r1_tsep_1(A_35,'#skF_2')
      | ~ l1_struct_0('#skF_2')
      | ~ l1_struct_0(A_35)
      | ~ m1_pre_topc(B_53,'#skF_2')
      | ~ m1_pre_topc(B_53,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_166,c_76])).

tff(c_253,plain,(
    ~ l1_struct_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_256,plain,(
    ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_253])).

tff(c_260,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_256])).

tff(c_262,plain,(
    l1_struct_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [B_48,C_49,A_50] :
      ( m1_pre_topc(B_48,C_49)
      | ~ r1_tarski(u1_struct_0(B_48),u1_struct_0(C_49))
      | ~ m1_pre_topc(C_49,A_50)
      | ~ m1_pre_topc(B_48,A_50)
      | ~ l1_pre_topc(A_50)
      | ~ v2_pre_topc(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_115,plain,(
    ! [B_51,A_52] :
      ( m1_pre_topc(B_51,B_51)
      | ~ m1_pre_topc(B_51,A_52)
      | ~ l1_pre_topc(A_52)
      | ~ v2_pre_topc(A_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_110])).

tff(c_117,plain,
    ( m1_pre_topc('#skF_2','#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_32,c_115])).

tff(c_124,plain,(
    m1_pre_topc('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_117])).

tff(c_24,plain,
    ( r1_tsep_1('#skF_3','#skF_2')
    | r1_tsep_1('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_43,plain,(
    r1_tsep_1('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_103,plain,(
    ! [B_45] :
      ( r1_tarski(u1_struct_0(B_45),u1_struct_0('#skF_2'))
      | ~ m1_pre_topc(B_45,'#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_96])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_51,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_45])).

tff(c_60,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_51])).

tff(c_98,plain,(
    ! [B_45] :
      ( r1_tarski(u1_struct_0(B_45),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_45,'#skF_3')
      | ~ m1_pre_topc(B_45,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_94])).

tff(c_180,plain,(
    ! [B_54] :
      ( r1_tarski(u1_struct_0(B_54),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_54,'#skF_3')
      | ~ m1_pre_topc(B_54,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_98])).

tff(c_82,plain,(
    ! [C_39,B_40,A_41] :
      ( ~ r1_tarski(C_39,u1_struct_0(B_40))
      | ~ r1_tarski(C_39,u1_struct_0(A_41))
      | v1_xboole_0(C_39)
      | ~ r1_tsep_1(A_41,B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_73,c_8])).

tff(c_86,plain,(
    ! [B_40,A_41] :
      ( ~ r1_tarski(u1_struct_0(B_40),u1_struct_0(A_41))
      | v1_xboole_0(u1_struct_0(B_40))
      | ~ r1_tsep_1(A_41,B_40)
      | ~ l1_struct_0(B_40)
      | ~ l1_struct_0(A_41) ) ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_191,plain,(
    ! [B_54] :
      ( v1_xboole_0(u1_struct_0(B_54))
      | ~ r1_tsep_1('#skF_3',B_54)
      | ~ l1_struct_0(B_54)
      | ~ l1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_54,'#skF_3')
      | ~ m1_pre_topc(B_54,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_180,c_86])).

tff(c_243,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_191])).

tff(c_246,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_243])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_246])).

tff(c_252,plain,(
    l1_struct_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_191])).

tff(c_192,plain,(
    ! [B_54,A_35] :
      ( ~ r1_tarski(u1_struct_0(B_54),u1_struct_0(A_35))
      | v1_xboole_0(u1_struct_0(B_54))
      | ~ r1_tsep_1(A_35,'#skF_3')
      | ~ l1_struct_0('#skF_3')
      | ~ l1_struct_0(A_35)
      | ~ m1_pre_topc(B_54,'#skF_3')
      | ~ m1_pre_topc(B_54,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_180,c_76])).

tff(c_305,plain,(
    ! [B_63,A_64] :
      ( ~ r1_tarski(u1_struct_0(B_63),u1_struct_0(A_64))
      | v1_xboole_0(u1_struct_0(B_63))
      | ~ r1_tsep_1(A_64,'#skF_3')
      | ~ l1_struct_0(A_64)
      | ~ m1_pre_topc(B_63,'#skF_3')
      | ~ m1_pre_topc(B_63,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_192])).

tff(c_311,plain,(
    ! [B_45] :
      ( v1_xboole_0(u1_struct_0(B_45))
      | ~ r1_tsep_1('#skF_2','#skF_3')
      | ~ l1_struct_0('#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_3')
      | ~ m1_pre_topc(B_45,'#skF_2')
      | ~ m1_pre_topc(B_45,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_103,c_305])).

tff(c_324,plain,(
    ! [B_65] :
      ( v1_xboole_0(u1_struct_0(B_65))
      | ~ m1_pre_topc(B_65,'#skF_3')
      | ~ m1_pre_topc(B_65,'#skF_2')
      | ~ m1_pre_topc(B_65,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_43,c_311])).

tff(c_14,plain,(
    ! [A_10] :
      ( ~ v1_xboole_0(u1_struct_0(A_10))
      | ~ l1_struct_0(A_10)
      | v2_struct_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_329,plain,(
    ! [B_66] :
      ( ~ l1_struct_0(B_66)
      | v2_struct_0(B_66)
      | ~ m1_pre_topc(B_66,'#skF_3')
      | ~ m1_pre_topc(B_66,'#skF_2')
      | ~ m1_pre_topc(B_66,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_324,c_14])).

tff(c_332,plain,
    ( ~ l1_struct_0('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_124,c_329])).

tff(c_335,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_262,c_332])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_335])).

tff(c_338,plain,(
    r1_tsep_1('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_347,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_341])).

tff(c_356,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_347])).

tff(c_393,plain,(
    ! [B_85] :
      ( r1_tarski(u1_struct_0(B_85),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_85,'#skF_3')
      | ~ m1_pre_topc(B_85,'#skF_1')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_28,c_389])).

tff(c_406,plain,(
    ! [B_89] :
      ( r1_tarski(u1_struct_0(B_89),u1_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_89,'#skF_3')
      | ~ m1_pre_topc(B_89,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_393])).

tff(c_378,plain,(
    ! [C_80,B_81,A_82] :
      ( ~ r1_tarski(C_80,u1_struct_0(B_81))
      | ~ r1_tarski(C_80,u1_struct_0(A_82))
      | v1_xboole_0(C_80)
      | ~ r1_tsep_1(A_82,B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_369,c_8])).

tff(c_382,plain,(
    ! [B_81,A_82] :
      ( ~ r1_tarski(u1_struct_0(B_81),u1_struct_0(A_82))
      | v1_xboole_0(u1_struct_0(B_81))
      | ~ r1_tsep_1(A_82,B_81)
      | ~ l1_struct_0(B_81)
      | ~ l1_struct_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_6,c_378])).

tff(c_414,plain,(
    ! [B_89] :
      ( v1_xboole_0(u1_struct_0(B_89))
      | ~ r1_tsep_1('#skF_3',B_89)
      | ~ l1_struct_0(B_89)
      | ~ l1_struct_0('#skF_3')
      | ~ m1_pre_topc(B_89,'#skF_3')
      | ~ m1_pre_topc(B_89,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_406,c_382])).

tff(c_537,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_414])).

tff(c_540,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_537])).

tff(c_544,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_540])).

tff(c_548,plain,(
    ! [B_98] :
      ( v1_xboole_0(u1_struct_0(B_98))
      | ~ r1_tsep_1('#skF_3',B_98)
      | ~ l1_struct_0(B_98)
      | ~ m1_pre_topc(B_98,'#skF_3')
      | ~ m1_pre_topc(B_98,'#skF_1') ) ),
    inference(splitRight,[status(thm)],[c_414])).

tff(c_563,plain,(
    ! [B_99] :
      ( v2_struct_0(B_99)
      | ~ r1_tsep_1('#skF_3',B_99)
      | ~ l1_struct_0(B_99)
      | ~ m1_pre_topc(B_99,'#skF_3')
      | ~ m1_pre_topc(B_99,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_548,c_14])).

tff(c_566,plain,
    ( v2_struct_0('#skF_2')
    | ~ l1_struct_0('#skF_2')
    | ~ m1_pre_topc('#skF_2','#skF_3')
    | ~ m1_pre_topc('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_338,c_563])).

tff(c_569,plain,(
    v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_26,c_562,c_566])).

tff(c_571,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:29:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.36  
% 2.70/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.36  %$ r1_xboole_0 > r1_tsep_1 > r1_tarski > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > l1_struct_0 > l1_pre_topc > #nlpp > u1_struct_0 > #skF_2 > #skF_3 > #skF_1
% 2.70/1.36  
% 2.70/1.36  %Foreground sorts:
% 2.70/1.36  
% 2.70/1.36  
% 2.70/1.36  %Background operators:
% 2.70/1.36  
% 2.70/1.36  
% 2.70/1.36  %Foreground operators:
% 2.70/1.36  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 2.70/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.36  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 2.70/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.70/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.70/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.36  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 2.70/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.36  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 2.70/1.36  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 2.70/1.36  tff(r1_tsep_1, type, r1_tsep_1: ($i * $i) > $o).
% 2.70/1.36  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 2.70/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.70/1.36  
% 2.70/1.38  tff(f_111, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (m1_pre_topc(B, C) => (~r1_tsep_1(B, C) & ~r1_tsep_1(C, B))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tmap_1)).
% 2.70/1.38  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.70/1.38  tff(f_45, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.70/1.38  tff(f_83, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 2.70/1.38  tff(f_69, axiom, (![A]: (l1_struct_0(A) => (![B]: (l1_struct_0(B) => (r1_tsep_1(A, B) <=> r1_xboole_0(u1_struct_0(A), u1_struct_0(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 2.70/1.38  tff(f_41, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.70/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.38  tff(f_60, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 2.70/1.38  tff(c_34, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.38  tff(c_32, plain, (m1_pre_topc('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.38  tff(c_26, plain, (m1_pre_topc('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.38  tff(c_36, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.38  tff(c_341, plain, (![B_68, A_69]: (l1_pre_topc(B_68) | ~m1_pre_topc(B_68, A_69) | ~l1_pre_topc(A_69))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.38  tff(c_344, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_341])).
% 2.70/1.38  tff(c_353, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_344])).
% 2.70/1.38  tff(c_10, plain, (![A_6]: (l1_struct_0(A_6) | ~l1_pre_topc(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.38  tff(c_38, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.38  tff(c_389, plain, (![B_85, C_86, A_87]: (r1_tarski(u1_struct_0(B_85), u1_struct_0(C_86)) | ~m1_pre_topc(B_85, C_86) | ~m1_pre_topc(C_86, A_87) | ~m1_pre_topc(B_85, A_87) | ~l1_pre_topc(A_87) | ~v2_pre_topc(A_87))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_391, plain, (![B_85]: (r1_tarski(u1_struct_0(B_85), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_85, '#skF_2') | ~m1_pre_topc(B_85, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_389])).
% 2.70/1.38  tff(c_417, plain, (![B_90]: (r1_tarski(u1_struct_0(B_90), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_90, '#skF_2') | ~m1_pre_topc(B_90, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_391])).
% 2.70/1.38  tff(c_369, plain, (![A_76, B_77]: (r1_xboole_0(u1_struct_0(A_76), u1_struct_0(B_77)) | ~r1_tsep_1(A_76, B_77) | ~l1_struct_0(B_77) | ~l1_struct_0(A_76))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.70/1.38  tff(c_8, plain, (![A_3, B_4, C_5]: (~r1_xboole_0(A_3, B_4) | ~r1_tarski(C_5, B_4) | ~r1_tarski(C_5, A_3) | v1_xboole_0(C_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.38  tff(c_372, plain, (![C_5, B_77, A_76]: (~r1_tarski(C_5, u1_struct_0(B_77)) | ~r1_tarski(C_5, u1_struct_0(A_76)) | v1_xboole_0(C_5) | ~r1_tsep_1(A_76, B_77) | ~l1_struct_0(B_77) | ~l1_struct_0(A_76))), inference(resolution, [status(thm)], [c_369, c_8])).
% 2.70/1.38  tff(c_426, plain, (![B_90, A_76]: (~r1_tarski(u1_struct_0(B_90), u1_struct_0(A_76)) | v1_xboole_0(u1_struct_0(B_90)) | ~r1_tsep_1(A_76, '#skF_2') | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_76) | ~m1_pre_topc(B_90, '#skF_2') | ~m1_pre_topc(B_90, '#skF_1'))), inference(resolution, [status(thm)], [c_417, c_372])).
% 2.70/1.38  tff(c_553, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_426])).
% 2.70/1.38  tff(c_556, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_553])).
% 2.70/1.38  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_353, c_556])).
% 2.70/1.38  tff(c_562, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_426])).
% 2.70/1.38  tff(c_45, plain, (![B_27, A_28]: (l1_pre_topc(B_27) | ~m1_pre_topc(B_27, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.38  tff(c_48, plain, (l1_pre_topc('#skF_2') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_45])).
% 2.70/1.38  tff(c_57, plain, (l1_pre_topc('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_48])).
% 2.70/1.38  tff(c_94, plain, (![B_45, C_46, A_47]: (r1_tarski(u1_struct_0(B_45), u1_struct_0(C_46)) | ~m1_pre_topc(B_45, C_46) | ~m1_pre_topc(C_46, A_47) | ~m1_pre_topc(B_45, A_47) | ~l1_pre_topc(A_47) | ~v2_pre_topc(A_47))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_96, plain, (![B_45]: (r1_tarski(u1_struct_0(B_45), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_45, '#skF_2') | ~m1_pre_topc(B_45, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_32, c_94])).
% 2.70/1.38  tff(c_166, plain, (![B_53]: (r1_tarski(u1_struct_0(B_53), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_53, '#skF_2') | ~m1_pre_topc(B_53, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_96])).
% 2.70/1.38  tff(c_73, plain, (![A_35, B_36]: (r1_xboole_0(u1_struct_0(A_35), u1_struct_0(B_36)) | ~r1_tsep_1(A_35, B_36) | ~l1_struct_0(B_36) | ~l1_struct_0(A_35))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.70/1.38  tff(c_76, plain, (![C_5, B_36, A_35]: (~r1_tarski(C_5, u1_struct_0(B_36)) | ~r1_tarski(C_5, u1_struct_0(A_35)) | v1_xboole_0(C_5) | ~r1_tsep_1(A_35, B_36) | ~l1_struct_0(B_36) | ~l1_struct_0(A_35))), inference(resolution, [status(thm)], [c_73, c_8])).
% 2.70/1.38  tff(c_178, plain, (![B_53, A_35]: (~r1_tarski(u1_struct_0(B_53), u1_struct_0(A_35)) | v1_xboole_0(u1_struct_0(B_53)) | ~r1_tsep_1(A_35, '#skF_2') | ~l1_struct_0('#skF_2') | ~l1_struct_0(A_35) | ~m1_pre_topc(B_53, '#skF_2') | ~m1_pre_topc(B_53, '#skF_1'))), inference(resolution, [status(thm)], [c_166, c_76])).
% 2.70/1.38  tff(c_253, plain, (~l1_struct_0('#skF_2')), inference(splitLeft, [status(thm)], [c_178])).
% 2.70/1.38  tff(c_256, plain, (~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_10, c_253])).
% 2.70/1.38  tff(c_260, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_256])).
% 2.70/1.38  tff(c_262, plain, (l1_struct_0('#skF_2')), inference(splitRight, [status(thm)], [c_178])).
% 2.70/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.38  tff(c_110, plain, (![B_48, C_49, A_50]: (m1_pre_topc(B_48, C_49) | ~r1_tarski(u1_struct_0(B_48), u1_struct_0(C_49)) | ~m1_pre_topc(C_49, A_50) | ~m1_pre_topc(B_48, A_50) | ~l1_pre_topc(A_50) | ~v2_pre_topc(A_50))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.70/1.38  tff(c_115, plain, (![B_51, A_52]: (m1_pre_topc(B_51, B_51) | ~m1_pre_topc(B_51, A_52) | ~l1_pre_topc(A_52) | ~v2_pre_topc(A_52))), inference(resolution, [status(thm)], [c_6, c_110])).
% 2.70/1.38  tff(c_117, plain, (m1_pre_topc('#skF_2', '#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_32, c_115])).
% 2.70/1.38  tff(c_124, plain, (m1_pre_topc('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_117])).
% 2.70/1.38  tff(c_24, plain, (r1_tsep_1('#skF_3', '#skF_2') | r1_tsep_1('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.38  tff(c_43, plain, (r1_tsep_1('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_24])).
% 2.70/1.38  tff(c_103, plain, (![B_45]: (r1_tarski(u1_struct_0(B_45), u1_struct_0('#skF_2')) | ~m1_pre_topc(B_45, '#skF_2') | ~m1_pre_topc(B_45, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_96])).
% 2.70/1.38  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.70/1.38  tff(c_51, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_45])).
% 2.70/1.38  tff(c_60, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_51])).
% 2.70/1.38  tff(c_98, plain, (![B_45]: (r1_tarski(u1_struct_0(B_45), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_45, '#skF_3') | ~m1_pre_topc(B_45, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_94])).
% 2.70/1.38  tff(c_180, plain, (![B_54]: (r1_tarski(u1_struct_0(B_54), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_54, '#skF_3') | ~m1_pre_topc(B_54, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_98])).
% 2.70/1.38  tff(c_82, plain, (![C_39, B_40, A_41]: (~r1_tarski(C_39, u1_struct_0(B_40)) | ~r1_tarski(C_39, u1_struct_0(A_41)) | v1_xboole_0(C_39) | ~r1_tsep_1(A_41, B_40) | ~l1_struct_0(B_40) | ~l1_struct_0(A_41))), inference(resolution, [status(thm)], [c_73, c_8])).
% 2.70/1.38  tff(c_86, plain, (![B_40, A_41]: (~r1_tarski(u1_struct_0(B_40), u1_struct_0(A_41)) | v1_xboole_0(u1_struct_0(B_40)) | ~r1_tsep_1(A_41, B_40) | ~l1_struct_0(B_40) | ~l1_struct_0(A_41))), inference(resolution, [status(thm)], [c_6, c_82])).
% 2.70/1.38  tff(c_191, plain, (![B_54]: (v1_xboole_0(u1_struct_0(B_54)) | ~r1_tsep_1('#skF_3', B_54) | ~l1_struct_0(B_54) | ~l1_struct_0('#skF_3') | ~m1_pre_topc(B_54, '#skF_3') | ~m1_pre_topc(B_54, '#skF_1'))), inference(resolution, [status(thm)], [c_180, c_86])).
% 2.70/1.38  tff(c_243, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_191])).
% 2.70/1.38  tff(c_246, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_243])).
% 2.70/1.38  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_246])).
% 2.70/1.38  tff(c_252, plain, (l1_struct_0('#skF_3')), inference(splitRight, [status(thm)], [c_191])).
% 2.70/1.38  tff(c_192, plain, (![B_54, A_35]: (~r1_tarski(u1_struct_0(B_54), u1_struct_0(A_35)) | v1_xboole_0(u1_struct_0(B_54)) | ~r1_tsep_1(A_35, '#skF_3') | ~l1_struct_0('#skF_3') | ~l1_struct_0(A_35) | ~m1_pre_topc(B_54, '#skF_3') | ~m1_pre_topc(B_54, '#skF_1'))), inference(resolution, [status(thm)], [c_180, c_76])).
% 2.70/1.38  tff(c_305, plain, (![B_63, A_64]: (~r1_tarski(u1_struct_0(B_63), u1_struct_0(A_64)) | v1_xboole_0(u1_struct_0(B_63)) | ~r1_tsep_1(A_64, '#skF_3') | ~l1_struct_0(A_64) | ~m1_pre_topc(B_63, '#skF_3') | ~m1_pre_topc(B_63, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_192])).
% 2.70/1.38  tff(c_311, plain, (![B_45]: (v1_xboole_0(u1_struct_0(B_45)) | ~r1_tsep_1('#skF_2', '#skF_3') | ~l1_struct_0('#skF_2') | ~m1_pre_topc(B_45, '#skF_3') | ~m1_pre_topc(B_45, '#skF_2') | ~m1_pre_topc(B_45, '#skF_1'))), inference(resolution, [status(thm)], [c_103, c_305])).
% 2.70/1.38  tff(c_324, plain, (![B_65]: (v1_xboole_0(u1_struct_0(B_65)) | ~m1_pre_topc(B_65, '#skF_3') | ~m1_pre_topc(B_65, '#skF_2') | ~m1_pre_topc(B_65, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_262, c_43, c_311])).
% 2.70/1.38  tff(c_14, plain, (![A_10]: (~v1_xboole_0(u1_struct_0(A_10)) | ~l1_struct_0(A_10) | v2_struct_0(A_10))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.70/1.38  tff(c_329, plain, (![B_66]: (~l1_struct_0(B_66) | v2_struct_0(B_66) | ~m1_pre_topc(B_66, '#skF_3') | ~m1_pre_topc(B_66, '#skF_2') | ~m1_pre_topc(B_66, '#skF_1'))), inference(resolution, [status(thm)], [c_324, c_14])).
% 2.70/1.38  tff(c_332, plain, (~l1_struct_0('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_124, c_329])).
% 2.70/1.38  tff(c_335, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_262, c_332])).
% 2.70/1.38  tff(c_337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_335])).
% 2.70/1.38  tff(c_338, plain, (r1_tsep_1('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_24])).
% 2.70/1.38  tff(c_347, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_28, c_341])).
% 2.70/1.38  tff(c_356, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_347])).
% 2.70/1.38  tff(c_393, plain, (![B_85]: (r1_tarski(u1_struct_0(B_85), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_85, '#skF_3') | ~m1_pre_topc(B_85, '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1'))), inference(resolution, [status(thm)], [c_28, c_389])).
% 2.70/1.38  tff(c_406, plain, (![B_89]: (r1_tarski(u1_struct_0(B_89), u1_struct_0('#skF_3')) | ~m1_pre_topc(B_89, '#skF_3') | ~m1_pre_topc(B_89, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_393])).
% 2.70/1.38  tff(c_378, plain, (![C_80, B_81, A_82]: (~r1_tarski(C_80, u1_struct_0(B_81)) | ~r1_tarski(C_80, u1_struct_0(A_82)) | v1_xboole_0(C_80) | ~r1_tsep_1(A_82, B_81) | ~l1_struct_0(B_81) | ~l1_struct_0(A_82))), inference(resolution, [status(thm)], [c_369, c_8])).
% 2.70/1.38  tff(c_382, plain, (![B_81, A_82]: (~r1_tarski(u1_struct_0(B_81), u1_struct_0(A_82)) | v1_xboole_0(u1_struct_0(B_81)) | ~r1_tsep_1(A_82, B_81) | ~l1_struct_0(B_81) | ~l1_struct_0(A_82))), inference(resolution, [status(thm)], [c_6, c_378])).
% 2.70/1.38  tff(c_414, plain, (![B_89]: (v1_xboole_0(u1_struct_0(B_89)) | ~r1_tsep_1('#skF_3', B_89) | ~l1_struct_0(B_89) | ~l1_struct_0('#skF_3') | ~m1_pre_topc(B_89, '#skF_3') | ~m1_pre_topc(B_89, '#skF_1'))), inference(resolution, [status(thm)], [c_406, c_382])).
% 2.70/1.38  tff(c_537, plain, (~l1_struct_0('#skF_3')), inference(splitLeft, [status(thm)], [c_414])).
% 2.70/1.38  tff(c_540, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_10, c_537])).
% 2.70/1.38  tff(c_544, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_356, c_540])).
% 2.70/1.38  tff(c_548, plain, (![B_98]: (v1_xboole_0(u1_struct_0(B_98)) | ~r1_tsep_1('#skF_3', B_98) | ~l1_struct_0(B_98) | ~m1_pre_topc(B_98, '#skF_3') | ~m1_pre_topc(B_98, '#skF_1'))), inference(splitRight, [status(thm)], [c_414])).
% 2.70/1.38  tff(c_563, plain, (![B_99]: (v2_struct_0(B_99) | ~r1_tsep_1('#skF_3', B_99) | ~l1_struct_0(B_99) | ~m1_pre_topc(B_99, '#skF_3') | ~m1_pre_topc(B_99, '#skF_1'))), inference(resolution, [status(thm)], [c_548, c_14])).
% 2.70/1.38  tff(c_566, plain, (v2_struct_0('#skF_2') | ~l1_struct_0('#skF_2') | ~m1_pre_topc('#skF_2', '#skF_3') | ~m1_pre_topc('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_338, c_563])).
% 2.70/1.38  tff(c_569, plain, (v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_26, c_562, c_566])).
% 2.70/1.38  tff(c_571, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_569])).
% 2.70/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.38  
% 2.70/1.38  Inference rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Ref     : 0
% 2.70/1.38  #Sup     : 87
% 2.70/1.38  #Fact    : 0
% 2.70/1.38  #Define  : 0
% 2.70/1.38  #Split   : 13
% 2.70/1.38  #Chain   : 0
% 2.70/1.38  #Close   : 0
% 2.70/1.38  
% 2.70/1.38  Ordering : KBO
% 2.70/1.38  
% 2.70/1.38  Simplification rules
% 2.70/1.38  ----------------------
% 2.70/1.38  #Subsume      : 8
% 2.70/1.38  #Demod        : 95
% 2.70/1.38  #Tautology    : 27
% 2.70/1.38  #SimpNegUnit  : 3
% 2.70/1.38  #BackRed      : 0
% 2.70/1.38  
% 2.70/1.38  #Partial instantiations: 0
% 2.70/1.38  #Strategies tried      : 1
% 2.70/1.38  
% 2.70/1.38  Timing (in seconds)
% 2.70/1.38  ----------------------
% 2.70/1.38  Preprocessing        : 0.28
% 2.70/1.38  Parsing              : 0.15
% 2.70/1.38  CNF conversion       : 0.02
% 2.70/1.38  Main loop            : 0.31
% 2.70/1.38  Inferencing          : 0.12
% 2.70/1.38  Reduction            : 0.08
% 2.70/1.38  Demodulation         : 0.06
% 2.70/1.38  BG Simplification    : 0.02
% 2.70/1.38  Subsumption          : 0.06
% 2.70/1.38  Abstraction          : 0.01
% 2.70/1.38  MUC search           : 0.00
% 2.70/1.38  Cooper               : 0.00
% 2.70/1.38  Total                : 0.63
% 2.70/1.38  Index Insertion      : 0.00
% 2.70/1.38  Index Deletion       : 0.00
% 2.70/1.38  Index Matching       : 0.00
% 2.70/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
