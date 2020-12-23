%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:30:07 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 562 expanded)
%              Number of leaves         :   29 ( 201 expanded)
%              Depth                    :   16
%              Number of atoms          :  293 (1588 expanded)
%              Number of equality atoms :   23 (  95 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff(v1_tdlat_3,type,(
    v1_tdlat_3: $i > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v3_tex_2,type,(
    v3_tex_2: ( $i * $i ) > $o )).

tff(v2_tex_2,type,(
    v2_tex_2: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_42,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( v1_subset_1(B,A)
      <=> B != A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

tff(f_112,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v2_struct_0(A)
          & v2_pre_topc(A)
          & v1_tdlat_3(A)
          & l1_pre_topc(A) )
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
           => ( v3_tex_2(B,A)
            <=> ~ v1_subset_1(B,u1_struct_0(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_94,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & v1_tdlat_3(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => v2_tex_2(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ( v3_tex_2(B,A)
          <=> ( v2_tex_2(B,A)
              & ! [C] :
                  ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
                 => ( ( v2_tex_2(C,A)
                      & r1_tarski(B,C) )
                   => B = C ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

tff(c_14,plain,(
    ! [A_8] : k2_subset_1(A_8) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_16,plain,(
    ! [A_9] : m1_subset_1(k2_subset_1(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_57,plain,(
    ! [A_9] : m1_subset_1(A_9,k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_24,plain,(
    ! [B_16] :
      ( ~ v1_subset_1(B_16,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_59,plain,(
    ! [B_16] : ~ v1_subset_1(B_16,B_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_24])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_546,plain,(
    ! [C_120,A_121,B_122] :
      ( r2_hidden(C_120,A_121)
      | ~ r2_hidden(C_120,B_122)
      | ~ m1_subset_1(B_122,k1_zfmisc_1(A_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_575,plain,(
    ! [A_129,B_130,A_131] :
      ( r2_hidden('#skF_1'(A_129,B_130),A_131)
      | ~ m1_subset_1(A_129,k1_zfmisc_1(A_131))
      | r1_tarski(A_129,B_130) ) ),
    inference(resolution,[status(thm)],[c_6,c_546])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_587,plain,(
    ! [A_132,A_133] :
      ( ~ m1_subset_1(A_132,k1_zfmisc_1(A_133))
      | r1_tarski(A_132,A_133) ) ),
    inference(resolution,[status(thm)],[c_575,c_4])).

tff(c_594,plain,(
    r1_tarski('#skF_4',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_587])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( B_7 = A_6
      | ~ r1_tarski(B_7,A_6)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_599,plain,
    ( u1_struct_0('#skF_3') = '#skF_4'
    | ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_594,c_8])).

tff(c_613,plain,(
    ~ r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_599])).

tff(c_42,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_50,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_73,plain,(
    ~ v3_tex_2('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_46,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_44,plain,(
    v1_tdlat_3('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_56,plain,
    ( v3_tex_2('#skF_4','#skF_3')
    | ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_75,plain,(
    ~ v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_56])).

tff(c_91,plain,(
    ! [B_42,A_43] :
      ( v1_subset_1(B_42,A_43)
      | B_42 = A_43
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_94,plain,
    ( v1_subset_1('#skF_4',u1_struct_0('#skF_3'))
    | u1_struct_0('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_91])).

tff(c_100,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_94])).

tff(c_167,plain,(
    ! [B_61,A_62] :
      ( v2_tex_2(B_61,A_62)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(u1_struct_0(A_62)))
      | ~ l1_pre_topc(A_62)
      | ~ v1_tdlat_3(A_62)
      | ~ v2_pre_topc(A_62)
      | v2_struct_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_170,plain,(
    ! [B_61] :
      ( v2_tex_2(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3')
      | ~ v1_tdlat_3('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_167])).

tff(c_176,plain,(
    ! [B_61] :
      ( v2_tex_2(B_61,'#skF_3')
      | ~ m1_subset_1(B_61,k1_zfmisc_1('#skF_4'))
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_170])).

tff(c_179,plain,(
    ! [B_63] :
      ( v2_tex_2(B_63,'#skF_3')
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_176])).

tff(c_184,plain,(
    v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_179])).

tff(c_185,plain,(
    ! [A_64,B_65] :
      ( '#skF_2'(A_64,B_65) != B_65
      | v3_tex_2(B_65,A_64)
      | ~ v2_tex_2(B_65,A_64)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(u1_struct_0(A_64)))
      | ~ l1_pre_topc(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_188,plain,(
    ! [B_65] :
      ( '#skF_2'('#skF_3',B_65) != B_65
      | v3_tex_2(B_65,'#skF_3')
      | ~ v2_tex_2(B_65,'#skF_3')
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_4'))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_185])).

tff(c_207,plain,(
    ! [B_71] :
      ( '#skF_2'('#skF_3',B_71) != B_71
      | v3_tex_2(B_71,'#skF_3')
      | ~ v2_tex_2(B_71,'#skF_3')
      | ~ m1_subset_1(B_71,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_188])).

tff(c_211,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_207])).

tff(c_214,plain,
    ( '#skF_2'('#skF_3','#skF_4') != '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_184,c_211])).

tff(c_215,plain,(
    '#skF_2'('#skF_3','#skF_4') != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_214])).

tff(c_297,plain,(
    ! [A_93,B_94] :
      ( m1_subset_1('#skF_2'(A_93,B_94),k1_zfmisc_1(u1_struct_0(A_93)))
      | v3_tex_2(B_94,A_93)
      | ~ v2_tex_2(B_94,A_93)
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0(A_93)))
      | ~ l1_pre_topc(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_323,plain,(
    ! [B_94] :
      ( m1_subset_1('#skF_2'('#skF_3',B_94),k1_zfmisc_1('#skF_4'))
      | v3_tex_2(B_94,'#skF_3')
      | ~ v2_tex_2(B_94,'#skF_3')
      | ~ m1_subset_1(B_94,k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_297])).

tff(c_461,plain,(
    ! [B_106] :
      ( m1_subset_1('#skF_2'('#skF_3',B_106),k1_zfmisc_1('#skF_4'))
      | v3_tex_2(B_106,'#skF_3')
      | ~ v2_tex_2(B_106,'#skF_3')
      | ~ m1_subset_1(B_106,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_100,c_323])).

tff(c_116,plain,(
    ! [C_47,A_48,B_49] :
      ( r2_hidden(C_47,A_48)
      | ~ r2_hidden(C_47,B_49)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_132,plain,(
    ! [A_53,B_54,A_55] :
      ( r2_hidden('#skF_1'(A_53,B_54),A_55)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_55))
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_116])).

tff(c_143,plain,(
    ! [A_53,A_55] :
      ( ~ m1_subset_1(A_53,k1_zfmisc_1(A_55))
      | r1_tarski(A_53,A_55) ) ),
    inference(resolution,[status(thm)],[c_132,c_4])).

tff(c_484,plain,(
    ! [B_107] :
      ( r1_tarski('#skF_2'('#skF_3',B_107),'#skF_4')
      | v3_tex_2(B_107,'#skF_3')
      | ~ v2_tex_2(B_107,'#skF_3')
      | ~ m1_subset_1(B_107,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_461,c_143])).

tff(c_256,plain,(
    ! [B_89,A_90] :
      ( r1_tarski(B_89,'#skF_2'(A_90,B_89))
      | v3_tex_2(B_89,A_90)
      | ~ v2_tex_2(B_89,A_90)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(u1_struct_0(A_90)))
      | ~ l1_pre_topc(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_275,plain,(
    ! [A_92] :
      ( r1_tarski(u1_struct_0(A_92),'#skF_2'(A_92,u1_struct_0(A_92)))
      | v3_tex_2(u1_struct_0(A_92),A_92)
      | ~ v2_tex_2(u1_struct_0(A_92),A_92)
      | ~ l1_pre_topc(A_92) ) ),
    inference(resolution,[status(thm)],[c_57,c_256])).

tff(c_284,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3',u1_struct_0('#skF_3')))
    | v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_275])).

tff(c_292,plain,
    ( r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4'))
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_184,c_100,c_100,c_100,c_284])).

tff(c_293,plain,(
    r1_tarski('#skF_4','#skF_2'('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_292])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [A_53,B_54,B_2,A_55] :
      ( r2_hidden('#skF_1'(A_53,B_54),B_2)
      | ~ r1_tarski(A_55,B_2)
      | ~ m1_subset_1(A_53,k1_zfmisc_1(A_55))
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_132,c_2])).

tff(c_387,plain,(
    ! [A_99,B_100] :
      ( r2_hidden('#skF_1'(A_99,B_100),'#skF_2'('#skF_3','#skF_4'))
      | ~ m1_subset_1(A_99,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_293,c_142])).

tff(c_399,plain,(
    ! [A_101] :
      ( ~ m1_subset_1(A_101,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_101,'#skF_2'('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_387,c_4])).

tff(c_413,plain,(
    ! [A_101] :
      ( A_101 = '#skF_2'('#skF_3','#skF_4')
      | ~ r1_tarski('#skF_2'('#skF_3','#skF_4'),A_101)
      | ~ m1_subset_1(A_101,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_399,c_8])).

tff(c_490,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3')
    | ~ v2_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_484,c_413])).

tff(c_507,plain,
    ( '#skF_2'('#skF_3','#skF_4') = '#skF_4'
    | v3_tex_2('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_184,c_490])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73,c_215,c_507])).

tff(c_511,plain,(
    v3_tex_2('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_600,plain,(
    ! [B_134,A_135] :
      ( v2_tex_2(B_134,A_135)
      | ~ m1_subset_1(B_134,k1_zfmisc_1(u1_struct_0(A_135)))
      | ~ l1_pre_topc(A_135)
      | ~ v1_tdlat_3(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_612,plain,(
    ! [A_135] :
      ( v2_tex_2(u1_struct_0(A_135),A_135)
      | ~ l1_pre_topc(A_135)
      | ~ v1_tdlat_3(A_135)
      | ~ v2_pre_topc(A_135)
      | v2_struct_0(A_135) ) ),
    inference(resolution,[status(thm)],[c_57,c_600])).

tff(c_674,plain,(
    ! [B_151,A_152] :
      ( r1_tarski(B_151,'#skF_2'(A_152,B_151))
      | v3_tex_2(B_151,A_152)
      | ~ v2_tex_2(B_151,A_152)
      | ~ m1_subset_1(B_151,k1_zfmisc_1(u1_struct_0(A_152)))
      | ~ l1_pre_topc(A_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_848,plain,(
    ! [A_191] :
      ( r1_tarski(u1_struct_0(A_191),'#skF_2'(A_191,u1_struct_0(A_191)))
      | v3_tex_2(u1_struct_0(A_191),A_191)
      | ~ v2_tex_2(u1_struct_0(A_191),A_191)
      | ~ l1_pre_topc(A_191) ) ),
    inference(resolution,[status(thm)],[c_57,c_674])).

tff(c_542,plain,(
    ! [C_117,B_118,A_119] :
      ( r2_hidden(C_117,B_118)
      | ~ r2_hidden(C_117,A_119)
      | ~ r1_tarski(A_119,B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_550,plain,(
    ! [A_123,B_124,B_125] :
      ( r2_hidden('#skF_1'(A_123,B_124),B_125)
      | ~ r1_tarski(A_123,B_125)
      | r1_tarski(A_123,B_124) ) ),
    inference(resolution,[status(thm)],[c_6,c_542])).

tff(c_627,plain,(
    ! [A_139,B_140,B_141,B_142] :
      ( r2_hidden('#skF_1'(A_139,B_140),B_141)
      | ~ r1_tarski(B_142,B_141)
      | ~ r1_tarski(A_139,B_142)
      | r1_tarski(A_139,B_140) ) ),
    inference(resolution,[status(thm)],[c_550,c_2])).

tff(c_634,plain,(
    ! [A_143,B_144] :
      ( r2_hidden('#skF_1'(A_143,B_144),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_143,'#skF_4')
      | r1_tarski(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_594,c_627])).

tff(c_729,plain,(
    ! [A_157,B_158,B_159] :
      ( r2_hidden('#skF_1'(A_157,B_158),B_159)
      | ~ r1_tarski(u1_struct_0('#skF_3'),B_159)
      | ~ r1_tarski(A_157,'#skF_4')
      | r1_tarski(A_157,B_158) ) ),
    inference(resolution,[status(thm)],[c_634,c_2])).

tff(c_740,plain,(
    ! [B_159,A_157] :
      ( ~ r1_tarski(u1_struct_0('#skF_3'),B_159)
      | ~ r1_tarski(A_157,'#skF_4')
      | r1_tarski(A_157,B_159) ) ),
    inference(resolution,[status(thm)],[c_729,c_4])).

tff(c_858,plain,(
    ! [A_157] :
      ( ~ r1_tarski(A_157,'#skF_4')
      | r1_tarski(A_157,'#skF_2'('#skF_3',u1_struct_0('#skF_3')))
      | v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
      | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_848,c_740])).

tff(c_880,plain,(
    ! [A_157] :
      ( ~ r1_tarski(A_157,'#skF_4')
      | r1_tarski(A_157,'#skF_2'('#skF_3',u1_struct_0('#skF_3')))
      | v3_tex_2(u1_struct_0('#skF_3'),'#skF_3')
      | ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_858])).

tff(c_941,plain,(
    ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_880])).

tff(c_960,plain,
    ( ~ l1_pre_topc('#skF_3')
    | ~ v1_tdlat_3('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_612,c_941])).

tff(c_963,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_42,c_960])).

tff(c_965,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_963])).

tff(c_967,plain,(
    v2_tex_2(u1_struct_0('#skF_3'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_880])).

tff(c_991,plain,(
    ! [C_208,B_209,A_210] :
      ( C_208 = B_209
      | ~ r1_tarski(B_209,C_208)
      | ~ v2_tex_2(C_208,A_210)
      | ~ m1_subset_1(C_208,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ v3_tex_2(B_209,A_210)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_1005,plain,(
    ! [A_210] :
      ( u1_struct_0('#skF_3') = '#skF_4'
      | ~ v2_tex_2(u1_struct_0('#skF_3'),A_210)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ v3_tex_2('#skF_4',A_210)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_210)))
      | ~ l1_pre_topc(A_210) ) ),
    inference(resolution,[status(thm)],[c_594,c_991])).

tff(c_1062,plain,(
    ! [A_221] :
      ( ~ v2_tex_2(u1_struct_0('#skF_3'),A_221)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ v3_tex_2('#skF_4',A_221)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0(A_221)))
      | ~ l1_pre_topc(A_221) ) ),
    inference(splitLeft,[status(thm)],[c_1005])).

tff(c_1066,plain,
    ( ~ v2_tex_2(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v3_tex_2('#skF_4','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(u1_struct_0('#skF_3')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_57,c_1062])).

tff(c_1070,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40,c_511,c_967,c_1066])).

tff(c_1071,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1005])).

tff(c_664,plain,(
    ! [A_147,B_148,B_149,A_150] :
      ( r2_hidden('#skF_1'(A_147,B_148),B_149)
      | ~ r1_tarski(A_150,B_149)
      | ~ m1_subset_1(A_147,k1_zfmisc_1(A_150))
      | r1_tarski(A_147,B_148) ) ),
    inference(resolution,[status(thm)],[c_575,c_2])).

tff(c_684,plain,(
    ! [A_153,B_154] :
      ( r2_hidden('#skF_1'(A_153,B_154),u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_153,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_153,B_154) ) ),
    inference(resolution,[status(thm)],[c_594,c_664])).

tff(c_696,plain,(
    ! [A_155] :
      ( ~ m1_subset_1(A_155,k1_zfmisc_1('#skF_4'))
      | r1_tarski(A_155,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_684,c_4])).

tff(c_560,plain,(
    ! [A_123,B_124,B_2,B_125] :
      ( r2_hidden('#skF_1'(A_123,B_124),B_2)
      | ~ r1_tarski(B_125,B_2)
      | ~ r1_tarski(A_123,B_125)
      | r1_tarski(A_123,B_124) ) ),
    inference(resolution,[status(thm)],[c_550,c_2])).

tff(c_834,plain,(
    ! [A_188,B_189,A_190] :
      ( r2_hidden('#skF_1'(A_188,B_189),u1_struct_0('#skF_3'))
      | ~ r1_tarski(A_188,A_190)
      | r1_tarski(A_188,B_189)
      | ~ m1_subset_1(A_190,k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_696,c_560])).

tff(c_845,plain,(
    ! [B_189] :
      ( r2_hidden('#skF_1'('#skF_4',B_189),u1_struct_0('#skF_3'))
      | r1_tarski('#skF_4',B_189)
      | ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_594,c_834])).

tff(c_847,plain,(
    ~ m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_845])).

tff(c_1078,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1071,c_847])).

tff(c_1101,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_1078])).

tff(c_1103,plain,(
    m1_subset_1(u1_struct_0('#skF_3'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_845])).

tff(c_586,plain,(
    ! [A_129,A_131] :
      ( ~ m1_subset_1(A_129,k1_zfmisc_1(A_131))
      | r1_tarski(A_129,A_131) ) ),
    inference(resolution,[status(thm)],[c_575,c_4])).

tff(c_1114,plain,(
    r1_tarski(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1103,c_586])).

tff(c_1127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_613,c_1114])).

tff(c_1128,plain,(
    u1_struct_0('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_599])).

tff(c_510,plain,(
    v1_subset_1('#skF_4',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_1131,plain,(
    v1_subset_1('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1128,c_510])).

tff(c_1135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_1131])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.57  
% 3.62/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.58  %$ v3_tex_2 > v2_tex_2 > v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v2_struct_0 > v2_pre_topc > v1_tdlat_3 > l1_pre_topc > #nlpp > u1_struct_0 > k2_subset_1 > k1_zfmisc_1 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.62/1.58  
% 3.62/1.58  %Foreground sorts:
% 3.62/1.58  
% 3.62/1.58  
% 3.62/1.58  %Background operators:
% 3.62/1.58  
% 3.62/1.58  
% 3.62/1.58  %Foreground operators:
% 3.62/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.62/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.62/1.58  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.62/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.62/1.58  tff(v1_tdlat_3, type, v1_tdlat_3: $i > $o).
% 3.62/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.62/1.58  tff(v3_tex_2, type, v3_tex_2: ($i * $i) > $o).
% 3.62/1.58  tff(v2_tex_2, type, v2_tex_2: ($i * $i) > $o).
% 3.62/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.62/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.62/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.62/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.62/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.62/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.62/1.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.62/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.58  
% 3.62/1.60  tff(f_40, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.62/1.60  tff(f_42, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.62/1.60  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_subset_1(B, A) <=> ~(B = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 3.62/1.60  tff(f_112, negated_conjecture, ~(![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> ~v1_subset_1(B, u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_tex_2)).
% 3.62/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.62/1.60  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 3.62/1.60  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.62/1.60  tff(f_94, axiom, (![A]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & v1_tdlat_3(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => v2_tex_2(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_tex_2)).
% 3.62/1.60  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (v3_tex_2(B, A) <=> (v2_tex_2(B, A) & (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((v2_tex_2(C, A) & r1_tarski(B, C)) => (B = C)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_tex_2)).
% 3.62/1.60  tff(c_14, plain, (![A_8]: (k2_subset_1(A_8)=A_8)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.62/1.60  tff(c_16, plain, (![A_9]: (m1_subset_1(k2_subset_1(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.62/1.60  tff(c_57, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.62/1.60  tff(c_24, plain, (![B_16]: (~v1_subset_1(B_16, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.60  tff(c_59, plain, (![B_16]: (~v1_subset_1(B_16, B_16))), inference(demodulation, [status(thm), theory('equality')], [c_57, c_24])).
% 3.62/1.60  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.62/1.60  tff(c_546, plain, (![C_120, A_121, B_122]: (r2_hidden(C_120, A_121) | ~r2_hidden(C_120, B_122) | ~m1_subset_1(B_122, k1_zfmisc_1(A_121)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.62/1.60  tff(c_575, plain, (![A_129, B_130, A_131]: (r2_hidden('#skF_1'(A_129, B_130), A_131) | ~m1_subset_1(A_129, k1_zfmisc_1(A_131)) | r1_tarski(A_129, B_130))), inference(resolution, [status(thm)], [c_6, c_546])).
% 3.62/1.60  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.62/1.60  tff(c_587, plain, (![A_132, A_133]: (~m1_subset_1(A_132, k1_zfmisc_1(A_133)) | r1_tarski(A_132, A_133))), inference(resolution, [status(thm)], [c_575, c_4])).
% 3.62/1.60  tff(c_594, plain, (r1_tarski('#skF_4', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_40, c_587])).
% 3.62/1.60  tff(c_8, plain, (![B_7, A_6]: (B_7=A_6 | ~r1_tarski(B_7, A_6) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.62/1.60  tff(c_599, plain, (u1_struct_0('#skF_3')='#skF_4' | ~r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_594, c_8])).
% 3.62/1.60  tff(c_613, plain, (~r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_599])).
% 3.62/1.60  tff(c_42, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.60  tff(c_50, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | ~v3_tex_2('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.60  tff(c_73, plain, (~v3_tex_2('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 3.62/1.60  tff(c_48, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.60  tff(c_46, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.60  tff(c_44, plain, (v1_tdlat_3('#skF_3')), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.60  tff(c_56, plain, (v3_tex_2('#skF_4', '#skF_3') | ~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_112])).
% 3.62/1.60  tff(c_75, plain, (~v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_73, c_56])).
% 3.62/1.60  tff(c_91, plain, (![B_42, A_43]: (v1_subset_1(B_42, A_43) | B_42=A_43 | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.60  tff(c_94, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3')) | u1_struct_0('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_40, c_91])).
% 3.62/1.60  tff(c_100, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_75, c_94])).
% 3.62/1.60  tff(c_167, plain, (![B_61, A_62]: (v2_tex_2(B_61, A_62) | ~m1_subset_1(B_61, k1_zfmisc_1(u1_struct_0(A_62))) | ~l1_pre_topc(A_62) | ~v1_tdlat_3(A_62) | ~v2_pre_topc(A_62) | v2_struct_0(A_62))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.62/1.60  tff(c_170, plain, (![B_61]: (v2_tex_2(B_61, '#skF_3') | ~m1_subset_1(B_61, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_167])).
% 3.62/1.60  tff(c_176, plain, (![B_61]: (v2_tex_2(B_61, '#skF_3') | ~m1_subset_1(B_61, k1_zfmisc_1('#skF_4')) | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_170])).
% 3.62/1.60  tff(c_179, plain, (![B_63]: (v2_tex_2(B_63, '#skF_3') | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_48, c_176])).
% 3.62/1.60  tff(c_184, plain, (v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_57, c_179])).
% 3.62/1.60  tff(c_185, plain, (![A_64, B_65]: ('#skF_2'(A_64, B_65)!=B_65 | v3_tex_2(B_65, A_64) | ~v2_tex_2(B_65, A_64) | ~m1_subset_1(B_65, k1_zfmisc_1(u1_struct_0(A_64))) | ~l1_pre_topc(A_64))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.62/1.60  tff(c_188, plain, (![B_65]: ('#skF_2'('#skF_3', B_65)!=B_65 | v3_tex_2(B_65, '#skF_3') | ~v2_tex_2(B_65, '#skF_3') | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_4')) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_185])).
% 3.62/1.60  tff(c_207, plain, (![B_71]: ('#skF_2'('#skF_3', B_71)!=B_71 | v3_tex_2(B_71, '#skF_3') | ~v2_tex_2(B_71, '#skF_3') | ~m1_subset_1(B_71, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_188])).
% 3.62/1.60  tff(c_211, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_57, c_207])).
% 3.62/1.60  tff(c_214, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_184, c_211])).
% 3.62/1.60  tff(c_215, plain, ('#skF_2'('#skF_3', '#skF_4')!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_73, c_214])).
% 3.62/1.60  tff(c_297, plain, (![A_93, B_94]: (m1_subset_1('#skF_2'(A_93, B_94), k1_zfmisc_1(u1_struct_0(A_93))) | v3_tex_2(B_94, A_93) | ~v2_tex_2(B_94, A_93) | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0(A_93))) | ~l1_pre_topc(A_93))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.62/1.60  tff(c_323, plain, (![B_94]: (m1_subset_1('#skF_2'('#skF_3', B_94), k1_zfmisc_1('#skF_4')) | v3_tex_2(B_94, '#skF_3') | ~v2_tex_2(B_94, '#skF_3') | ~m1_subset_1(B_94, k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_297])).
% 3.62/1.60  tff(c_461, plain, (![B_106]: (m1_subset_1('#skF_2'('#skF_3', B_106), k1_zfmisc_1('#skF_4')) | v3_tex_2(B_106, '#skF_3') | ~v2_tex_2(B_106, '#skF_3') | ~m1_subset_1(B_106, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_100, c_323])).
% 3.62/1.60  tff(c_116, plain, (![C_47, A_48, B_49]: (r2_hidden(C_47, A_48) | ~r2_hidden(C_47, B_49) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.62/1.60  tff(c_132, plain, (![A_53, B_54, A_55]: (r2_hidden('#skF_1'(A_53, B_54), A_55) | ~m1_subset_1(A_53, k1_zfmisc_1(A_55)) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_6, c_116])).
% 3.62/1.60  tff(c_143, plain, (![A_53, A_55]: (~m1_subset_1(A_53, k1_zfmisc_1(A_55)) | r1_tarski(A_53, A_55))), inference(resolution, [status(thm)], [c_132, c_4])).
% 3.62/1.60  tff(c_484, plain, (![B_107]: (r1_tarski('#skF_2'('#skF_3', B_107), '#skF_4') | v3_tex_2(B_107, '#skF_3') | ~v2_tex_2(B_107, '#skF_3') | ~m1_subset_1(B_107, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_461, c_143])).
% 3.62/1.60  tff(c_256, plain, (![B_89, A_90]: (r1_tarski(B_89, '#skF_2'(A_90, B_89)) | v3_tex_2(B_89, A_90) | ~v2_tex_2(B_89, A_90) | ~m1_subset_1(B_89, k1_zfmisc_1(u1_struct_0(A_90))) | ~l1_pre_topc(A_90))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.62/1.60  tff(c_275, plain, (![A_92]: (r1_tarski(u1_struct_0(A_92), '#skF_2'(A_92, u1_struct_0(A_92))) | v3_tex_2(u1_struct_0(A_92), A_92) | ~v2_tex_2(u1_struct_0(A_92), A_92) | ~l1_pre_topc(A_92))), inference(resolution, [status(thm)], [c_57, c_256])).
% 3.62/1.60  tff(c_284, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', u1_struct_0('#skF_3'))) | v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_100, c_275])).
% 3.62/1.60  tff(c_292, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4')) | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_184, c_100, c_100, c_100, c_284])).
% 3.62/1.60  tff(c_293, plain, (r1_tarski('#skF_4', '#skF_2'('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_73, c_292])).
% 3.62/1.60  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.62/1.60  tff(c_142, plain, (![A_53, B_54, B_2, A_55]: (r2_hidden('#skF_1'(A_53, B_54), B_2) | ~r1_tarski(A_55, B_2) | ~m1_subset_1(A_53, k1_zfmisc_1(A_55)) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_132, c_2])).
% 3.62/1.60  tff(c_387, plain, (![A_99, B_100]: (r2_hidden('#skF_1'(A_99, B_100), '#skF_2'('#skF_3', '#skF_4')) | ~m1_subset_1(A_99, k1_zfmisc_1('#skF_4')) | r1_tarski(A_99, B_100))), inference(resolution, [status(thm)], [c_293, c_142])).
% 3.62/1.60  tff(c_399, plain, (![A_101]: (~m1_subset_1(A_101, k1_zfmisc_1('#skF_4')) | r1_tarski(A_101, '#skF_2'('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_387, c_4])).
% 3.62/1.60  tff(c_413, plain, (![A_101]: (A_101='#skF_2'('#skF_3', '#skF_4') | ~r1_tarski('#skF_2'('#skF_3', '#skF_4'), A_101) | ~m1_subset_1(A_101, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_399, c_8])).
% 3.62/1.60  tff(c_490, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3') | ~v2_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_484, c_413])).
% 3.62/1.60  tff(c_507, plain, ('#skF_2'('#skF_3', '#skF_4')='#skF_4' | v3_tex_2('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_184, c_490])).
% 3.62/1.60  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73, c_215, c_507])).
% 3.62/1.60  tff(c_511, plain, (v3_tex_2('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_50])).
% 3.62/1.60  tff(c_600, plain, (![B_134, A_135]: (v2_tex_2(B_134, A_135) | ~m1_subset_1(B_134, k1_zfmisc_1(u1_struct_0(A_135))) | ~l1_pre_topc(A_135) | ~v1_tdlat_3(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(cnfTransformation, [status(thm)], [f_94])).
% 3.62/1.60  tff(c_612, plain, (![A_135]: (v2_tex_2(u1_struct_0(A_135), A_135) | ~l1_pre_topc(A_135) | ~v1_tdlat_3(A_135) | ~v2_pre_topc(A_135) | v2_struct_0(A_135))), inference(resolution, [status(thm)], [c_57, c_600])).
% 3.62/1.60  tff(c_674, plain, (![B_151, A_152]: (r1_tarski(B_151, '#skF_2'(A_152, B_151)) | v3_tex_2(B_151, A_152) | ~v2_tex_2(B_151, A_152) | ~m1_subset_1(B_151, k1_zfmisc_1(u1_struct_0(A_152))) | ~l1_pre_topc(A_152))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.62/1.60  tff(c_848, plain, (![A_191]: (r1_tarski(u1_struct_0(A_191), '#skF_2'(A_191, u1_struct_0(A_191))) | v3_tex_2(u1_struct_0(A_191), A_191) | ~v2_tex_2(u1_struct_0(A_191), A_191) | ~l1_pre_topc(A_191))), inference(resolution, [status(thm)], [c_57, c_674])).
% 3.62/1.60  tff(c_542, plain, (![C_117, B_118, A_119]: (r2_hidden(C_117, B_118) | ~r2_hidden(C_117, A_119) | ~r1_tarski(A_119, B_118))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.62/1.60  tff(c_550, plain, (![A_123, B_124, B_125]: (r2_hidden('#skF_1'(A_123, B_124), B_125) | ~r1_tarski(A_123, B_125) | r1_tarski(A_123, B_124))), inference(resolution, [status(thm)], [c_6, c_542])).
% 3.62/1.60  tff(c_627, plain, (![A_139, B_140, B_141, B_142]: (r2_hidden('#skF_1'(A_139, B_140), B_141) | ~r1_tarski(B_142, B_141) | ~r1_tarski(A_139, B_142) | r1_tarski(A_139, B_140))), inference(resolution, [status(thm)], [c_550, c_2])).
% 3.62/1.60  tff(c_634, plain, (![A_143, B_144]: (r2_hidden('#skF_1'(A_143, B_144), u1_struct_0('#skF_3')) | ~r1_tarski(A_143, '#skF_4') | r1_tarski(A_143, B_144))), inference(resolution, [status(thm)], [c_594, c_627])).
% 3.62/1.60  tff(c_729, plain, (![A_157, B_158, B_159]: (r2_hidden('#skF_1'(A_157, B_158), B_159) | ~r1_tarski(u1_struct_0('#skF_3'), B_159) | ~r1_tarski(A_157, '#skF_4') | r1_tarski(A_157, B_158))), inference(resolution, [status(thm)], [c_634, c_2])).
% 3.62/1.60  tff(c_740, plain, (![B_159, A_157]: (~r1_tarski(u1_struct_0('#skF_3'), B_159) | ~r1_tarski(A_157, '#skF_4') | r1_tarski(A_157, B_159))), inference(resolution, [status(thm)], [c_729, c_4])).
% 3.62/1.60  tff(c_858, plain, (![A_157]: (~r1_tarski(A_157, '#skF_4') | r1_tarski(A_157, '#skF_2'('#skF_3', u1_struct_0('#skF_3'))) | v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(resolution, [status(thm)], [c_848, c_740])).
% 3.62/1.60  tff(c_880, plain, (![A_157]: (~r1_tarski(A_157, '#skF_4') | r1_tarski(A_157, '#skF_2'('#skF_3', u1_struct_0('#skF_3'))) | v3_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_858])).
% 3.62/1.60  tff(c_941, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(splitLeft, [status(thm)], [c_880])).
% 3.62/1.60  tff(c_960, plain, (~l1_pre_topc('#skF_3') | ~v1_tdlat_3('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_612, c_941])).
% 3.62/1.60  tff(c_963, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_42, c_960])).
% 3.62/1.60  tff(c_965, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_963])).
% 3.62/1.60  tff(c_967, plain, (v2_tex_2(u1_struct_0('#skF_3'), '#skF_3')), inference(splitRight, [status(thm)], [c_880])).
% 3.62/1.60  tff(c_991, plain, (![C_208, B_209, A_210]: (C_208=B_209 | ~r1_tarski(B_209, C_208) | ~v2_tex_2(C_208, A_210) | ~m1_subset_1(C_208, k1_zfmisc_1(u1_struct_0(A_210))) | ~v3_tex_2(B_209, A_210) | ~m1_subset_1(B_209, k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.62/1.60  tff(c_1005, plain, (![A_210]: (u1_struct_0('#skF_3')='#skF_4' | ~v2_tex_2(u1_struct_0('#skF_3'), A_210) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_210))) | ~v3_tex_2('#skF_4', A_210) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_210))) | ~l1_pre_topc(A_210))), inference(resolution, [status(thm)], [c_594, c_991])).
% 3.62/1.60  tff(c_1062, plain, (![A_221]: (~v2_tex_2(u1_struct_0('#skF_3'), A_221) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1(u1_struct_0(A_221))) | ~v3_tex_2('#skF_4', A_221) | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0(A_221))) | ~l1_pre_topc(A_221))), inference(splitLeft, [status(thm)], [c_1005])).
% 3.62/1.60  tff(c_1066, plain, (~v2_tex_2(u1_struct_0('#skF_3'), '#skF_3') | ~v3_tex_2('#skF_4', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_57, c_1062])).
% 3.62/1.60  tff(c_1070, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_40, c_511, c_967, c_1066])).
% 3.62/1.60  tff(c_1071, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_1005])).
% 3.62/1.60  tff(c_664, plain, (![A_147, B_148, B_149, A_150]: (r2_hidden('#skF_1'(A_147, B_148), B_149) | ~r1_tarski(A_150, B_149) | ~m1_subset_1(A_147, k1_zfmisc_1(A_150)) | r1_tarski(A_147, B_148))), inference(resolution, [status(thm)], [c_575, c_2])).
% 3.62/1.60  tff(c_684, plain, (![A_153, B_154]: (r2_hidden('#skF_1'(A_153, B_154), u1_struct_0('#skF_3')) | ~m1_subset_1(A_153, k1_zfmisc_1('#skF_4')) | r1_tarski(A_153, B_154))), inference(resolution, [status(thm)], [c_594, c_664])).
% 3.62/1.60  tff(c_696, plain, (![A_155]: (~m1_subset_1(A_155, k1_zfmisc_1('#skF_4')) | r1_tarski(A_155, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_684, c_4])).
% 3.62/1.60  tff(c_560, plain, (![A_123, B_124, B_2, B_125]: (r2_hidden('#skF_1'(A_123, B_124), B_2) | ~r1_tarski(B_125, B_2) | ~r1_tarski(A_123, B_125) | r1_tarski(A_123, B_124))), inference(resolution, [status(thm)], [c_550, c_2])).
% 3.62/1.60  tff(c_834, plain, (![A_188, B_189, A_190]: (r2_hidden('#skF_1'(A_188, B_189), u1_struct_0('#skF_3')) | ~r1_tarski(A_188, A_190) | r1_tarski(A_188, B_189) | ~m1_subset_1(A_190, k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_696, c_560])).
% 3.62/1.60  tff(c_845, plain, (![B_189]: (r2_hidden('#skF_1'('#skF_4', B_189), u1_struct_0('#skF_3')) | r1_tarski('#skF_4', B_189) | ~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1('#skF_4')))), inference(resolution, [status(thm)], [c_594, c_834])).
% 3.62/1.60  tff(c_847, plain, (~m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_845])).
% 3.62/1.60  tff(c_1078, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_1071, c_847])).
% 3.62/1.60  tff(c_1101, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_57, c_1078])).
% 3.62/1.60  tff(c_1103, plain, (m1_subset_1(u1_struct_0('#skF_3'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_845])).
% 3.62/1.60  tff(c_586, plain, (![A_129, A_131]: (~m1_subset_1(A_129, k1_zfmisc_1(A_131)) | r1_tarski(A_129, A_131))), inference(resolution, [status(thm)], [c_575, c_4])).
% 3.62/1.60  tff(c_1114, plain, (r1_tarski(u1_struct_0('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_1103, c_586])).
% 3.62/1.60  tff(c_1127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_613, c_1114])).
% 3.62/1.60  tff(c_1128, plain, (u1_struct_0('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_599])).
% 3.62/1.60  tff(c_510, plain, (v1_subset_1('#skF_4', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_50])).
% 3.62/1.60  tff(c_1131, plain, (v1_subset_1('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1128, c_510])).
% 3.62/1.60  tff(c_1135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_1131])).
% 3.62/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/1.60  
% 3.62/1.60  Inference rules
% 3.62/1.60  ----------------------
% 3.62/1.60  #Ref     : 0
% 3.62/1.60  #Sup     : 236
% 3.62/1.60  #Fact    : 0
% 3.62/1.60  #Define  : 0
% 3.62/1.60  #Split   : 6
% 3.62/1.60  #Chain   : 0
% 3.62/1.60  #Close   : 0
% 3.62/1.60  
% 3.62/1.60  Ordering : KBO
% 3.62/1.60  
% 3.62/1.60  Simplification rules
% 3.62/1.60  ----------------------
% 3.62/1.60  #Subsume      : 64
% 3.62/1.60  #Demod        : 119
% 3.62/1.60  #Tautology    : 40
% 3.62/1.60  #SimpNegUnit  : 18
% 3.62/1.60  #BackRed      : 29
% 3.62/1.60  
% 3.62/1.60  #Partial instantiations: 0
% 3.62/1.60  #Strategies tried      : 1
% 3.62/1.60  
% 3.62/1.60  Timing (in seconds)
% 3.62/1.60  ----------------------
% 3.62/1.60  Preprocessing        : 0.31
% 3.62/1.60  Parsing              : 0.17
% 3.62/1.60  CNF conversion       : 0.02
% 3.62/1.60  Main loop            : 0.52
% 3.62/1.60  Inferencing          : 0.17
% 3.62/1.60  Reduction            : 0.13
% 3.62/1.60  Demodulation         : 0.09
% 3.62/1.60  BG Simplification    : 0.02
% 3.62/1.60  Subsumption          : 0.16
% 3.62/1.60  Abstraction          : 0.02
% 3.62/1.60  MUC search           : 0.00
% 3.62/1.60  Cooper               : 0.00
% 3.62/1.60  Total                : 0.87
% 3.62/1.60  Index Insertion      : 0.00
% 3.62/1.60  Index Deletion       : 0.00
% 3.62/1.60  Index Matching       : 0.00
% 3.62/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
